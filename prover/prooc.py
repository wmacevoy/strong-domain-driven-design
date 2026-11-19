#!/usr/bin/env python3
"""
prooc -- a spike (2026-11-17): read a C++ class, refuse it if its boundary leaks, and write what
must be proven of it, for Lean.

It writes no C and nothing that ships.  For a class C in ordinary C++ it writes, into --out:

  CModel.lean   each method as a Lean function from the state and the arguments to the new state
                and the result, or `none` where the C++ would read or write outside an array; and
                the invariant, `Inv`, read from the class's own `bool invariant() const`
  COwed.lean    WHAT MUST BE PROVEN, as one statement, `C.Owed`: every method is safe (never `none`)
                from any state that satisfies the invariant, and leaves the invariant true.  It
                imports the model and nothing written by hand, so nothing written by hand can
                change what it says.  A proof of it is `C.Claims.owed` in CClaims.lean, written by a
                person or an agent, and trusted for nothing: Audit.lean checks it (see there)
  CDiff.lean, C_diff.cpp   the model and the C++ driven by the same numbers, to compare what they print

THE BOUNDARY.  A class is a domain only if nothing outside it can reach its state, so that an
invariant proved of its methods is an invariant of the program.  The generator refuses what would
let state out: a field that is not private, a friend, a base, a pointer or a reference anywhere,
`this` as a value, the address of anything.  And what it cannot give an exact meaning: see refuse().

Usage:  python3 prover/prooc.py prover/model/Gauge.hpp -o prover/gen
"""

import argparse
import os
import re
import sys

import clang.cindex as ci
from clang.cindex import CursorKind as CK, TypeKind as TK

from clang_edge import configure_libclang, probe, where, Unsupported   # noqa: E402
from cxxtypes import (   # noqa: F401
    OPTIONS, READ, USED, BytesT, ClassT, GenT, Int, binders, convert, first_token, is_bytes, is_caller,
    is_gen, lean_name, not_checked, outer_constant, plain_literal, qual_of, refuse, result_type,
    subarray_of, tokens_after, typ, unparen)
from owed import emit_owed
from reader import BodyReader
from model import Writer
from compare import (emit_diff_cpp, emit_diff_cpp_generic, emit_diff_lean, emit_diff_lean_generic,
                     emit_script)
from subject import PRE_FLAGS, file_scope, subject_text, with_pre


def used_class(cursor, t):
    """The class a value's type is, as a ClassT: a class read here, or a class template read here,
    at the type and the values this use gives it."""
    decl = t.get_declaration()
    at = None
    made_from = ci.conf.lib.clang_getSpecializedCursorTemplate(decl)
    if decl.kind == CK.CLASS_DECL and made_from is not None and made_from.kind == CK.CLASS_TEMPLATE:
        n = decl.get_num_template_arguments()
        kinds = [decl.get_template_argument_kind(i).name for i in range(n)]
        if kinds[:1] != ["TYPE"] or any(x != "INTEGRAL" for x in kinds[1:]):
            refuse(cursor, "a class template used at other than a type and whole numbers")
        it = Int(decl.get_template_argument_type(0), cursor)
        if it.signed or it.is_bool:
            refuse(cursor, "a class template used at a type that is not an unsigned integer (not yet: "
                           "the template is proved of every type, but a class that uses it is read with unsigned numbers only)")
        at = (it, [decl.get_template_argument_unsigned_value(i) for i in range(1, n)])
        decl = made_from
    if decl.kind not in (CK.CLASS_DECL, CK.CLASS_TEMPLATE) or not decl.is_definition():
        refuse(cursor, "a parameter of a type that is not a class read here")
    if decl.spelling not in USED:
        k = Klass(decl)
        emit_model(k, "")           # for what its methods are: which are const, which have loops
        USED[decl.spelling] = k
    k = USED[decl.spelling]
    if bool(k.generic) != bool(at) or (at and len(at[1]) != len(k.generic[1])):
        refuse(cursor, "a class template used in a way the generator does not know")
    return ClassT(k, at, t.spelling if at else None)


def pre_of(cursor, body, name):
    """(the conditions at the head of a method's body, whether they are tested). `pre(...)`, as
    with_pre wrote it there, is expected of the caller and tested by nothing. STRONG_CHECK is
    tested when the program runs, and ends the process: only a way in for code that is not proved
    has one, since what is proved is proved to be called rightly."""
    said, kinds = [], set()
    for c in (body.get_children() if body is not None else []):
        if c.kind != CK.CALL_EXPR or c.spelling != "__builtin_assume":
            break
        said.append(list(c.get_children())[-1])
        kinds.add(READ["text"][c.extent.start.offset:].startswith(b"STRONG_CHECK"))      # the word it stands at, in the text read
    if len(kinds) > 1:
        refuse(cursor, "pre(...) and STRONG_CHECK on one method: it is either proved of its callers, or tested")
    tested = kinds == {True}
    if tested and "_checked" not in name:
        refuse(cursor, "STRONG_CHECK in '%s', which is not a `_checked` way in: what is proved is called by "
                       "what is proved, and tests nothing when the program runs" % name)
    return said, tested


class Field:
    def __init__(self, cursor, klass=None):
        self.name = cursor.spelling
        t = cursor.type.get_canonical()
        if is_gen(klass, cursor.type):
            self.count, self.type = None, GenT()
        elif t.kind == TK.CONSTANTARRAY:
            self.count = t.element_count
            self.type = Int(t.element_type, cursor)
            if self.type.signed:
                refuse(cursor, "an array of a signed type")
        else:
            self.count = None
            self.type = Int(t, cursor)
            if self.type.signed:
                refuse(cursor, "a signed field: its arithmetic can overflow, which is undefined")

    def lean(self):
        if self.count is None:
            return self.type.lean()
        return "Vector (%s) %d" % (self.type.lean(), self.count)

    def zero(self):
        if isinstance(self.type, GenT):
            return "default"        # storage of a type of which nothing is known: any value of it
        z = "0#%d" % self.type.width
        return z if self.count is None else "Vector.replicate %d %s" % (self.count, z)


class Method:
    def __init__(self, cursor, klass):
        self.cursor = cursor
        self.name = cursor.spelling
        self.const = cursor.is_const_method()
        self.public = cursor.access_specifier == ci.AccessSpecifier.PUBLIC
        self.fuel = False
        self.params = []
        self.body = None
        rt = cursor.result_type
        self.result = None if rt.get_canonical().kind == TK.VOID else typ(klass, rt, cursor)
        if self.result is not None and self.result.signed:
            refuse(cursor, "a signed result")
        self.lengths = {}       # a view's length parameter: the view it is the length of
        parms = [c for c in cursor.get_children() if c.kind == CK.PARM_DECL and not is_caller(c.type)]
        while parms:
            c = parms.pop(0)
            if not c.spelling:
                refuse(c, "a parameter with no name")
            ct = c.type.get_canonical()
            if subarray_of(c.type):
                t = BytesT(ctype=subarray_of(c.type))
            elif is_bytes(c.type):
                t = BytesT()
            elif ct.kind == TK.RECORD:
                t = used_class(c, ct)
                not_checked(c, self.name, t.k.name)
                klass.uses[t.k.name] = t.k
            elif ct.kind == TK.POINTER:
                to = ct.get_pointee()
                n = parms.pop(0) if parms else None
                if (to.kind not in (TK.UCHAR, TK.CHAR_S, TK.CHAR_U) or not to.is_const_qualified() or n is None
                        or not n.spelling or n.type.get_canonical().kind not in (TK.ULONG, TK.ULONGLONG)):
                    refuse(c, "a pointer parameter that is not to const bytes, with their number (an unsigned "
                              "64-bit parameter) next after it: the two together are a view")
                t = BytesT(length=n.spelling, readable=to.kind == TK.UCHAR, ctype=to.spelling.replace("const ", ""))
                self.lengths[n.spelling] = c.spelling
            else:
                t = typ(klass, c.type, c)
                if t.signed:
                    refuse(c, "a signed parameter")
            self.params.append((c.spelling, t))
        for c in cursor.get_children():
            if c.kind == CK.COMPOUND_STMT:
                self.body = c
        if self.body is None:
            refuse(cursor, "a method with no body here: the model is the body")
        self.pre, self.tested = pre_of(cursor, self.body, self.name)
        for v in self.body.walk_preorder():        # a local that is another class's value: that class is used
            if v.kind == CK.VAR_DECL and v.type.get_canonical().kind == TK.RECORD:
                u = used_class(v, v.type.get_canonical())
                not_checked(v, self.name, u.k.name)
                klass.uses[u.k.name] = u.k


def invariant_of(cursor):
    """The condition `bool invariant() const` returns: what the class says is always true of it."""
    body = [c for c in cursor.get_children() if c.kind == CK.COMPOUND_STMT]
    if (not cursor.is_const_method() or cursor.result_type.get_canonical().kind != TK.BOOL
            or any(c.kind == CK.PARM_DECL for c in cursor.get_children()) or len(body) != 1):
        refuse(cursor, "the invariant is `bool invariant() const`, with a body and no parameters")
    only = list(body[0].get_children())
    if len(only) != 1 or only[0].kind != CK.RETURN_STMT:
        refuse(cursor, "the invariant is one `return` of a condition on the fields")
    return list(only[0].get_children())[0]


class Klass:
    generic = None      # a class template: (the type parameter's name, the names of its value parameters)

    @property
    def lt(self):
        """Its type, in Lean."""
        return "%s %s" % (self.name, self.generic[0]) if self.generic else self.name

    @property
    def gb(self):
        """What a class template's model is given before anything else: the type, that two values of
        it compare, and the values of its other parameters."""
        if not self.generic:
            return ""
        t = self.generic[0]
        return " {%s : Type} [LE %s] [DecidableLE %s] [Inhabited %s]" % (t, t, t, t) + "".join(" (%s : %s)" % (lean_name(v), t) for v in self.generic[1])

    @property
    def ga(self):
        return "".join(" " + lean_name(v) for v in self.generic[1]) if self.generic else ""

    def __init__(self, cursor):
        self.name = cursor.spelling
        self.cursor = cursor
        self.is_function = False
        if cursor.kind == CK.CLASS_TEMPLATE:
            types = [c for c in cursor.get_children() if c.kind == CK.TEMPLATE_TYPE_PARAMETER]
            values = [c for c in cursor.get_children() if c.kind == CK.TEMPLATE_NON_TYPE_PARAMETER]
            if len(types) != 1 or any(v.type.spelling != types[0].spelling for v in values):
                refuse(cursor, "a class template that is not of one type and values of that type: "
                               "`template <typename T, T A, T B>`")
            self.generic = (types[0].spelling, [v.spelling for v in values])
        self.qual = qual_of(cursor)
        self.fields = []
        self.methods = []
        self.constants = {}             # static const members with a literal value: names for numbers
        self.uses = {}                  # the other classes its methods take as parameters
        self.ctor_params = []
        self.ready = {}                 # the methods whose models are written: what a call may name
        self.ctor = None
        self.ctor_pre, self.ctor_tested = [], False
        self.inv = None
        for c in cursor.get_children():
            k = c.kind
            if k in (CK.CXX_ACCESS_SPEC_DECL, CK.TEMPLATE_TYPE_PARAMETER, CK.TEMPLATE_NON_TYPE_PARAMETER):
                continue
            if k == CK.STATIC_ASSERT:
                continue        # the compiler's to check, and nothing here rests on it
            if k == CK.CXX_BASE_SPECIFIER:
                refuse(c, "a base class (the spike reads one class alone)")
            if k == CK.FRIEND_DECL:
                refuse(c, "a friend: it could reach the state from outside the class")
            if k == CK.FIELD_DECL:
                if c.access_specifier != ci.AccessSpecifier.PRIVATE:
                    refuse(c, "the field '%s' is not private: anything could change it, and no "
                              "invariant of the class would hold of the program" % c.spelling)
                if c.is_mutable_field():
                    refuse(c, "a mutable field: a const method could change the state")
                self.fields.append(Field(c, self))
            elif k == CK.CONSTRUCTOR:
                if self.ctor is not None:
                    refuse(c, "more than one constructor")
                for x in c.get_children():
                    if x.kind == CK.PARM_DECL and not is_caller(x.type):
                        t = typ(self, x.type, x)
                        if t.signed or not x.spelling:
                            refuse(x, "a constructor's parameter that is signed, or has no name")
                        self.ctor_params.append((x.spelling, t))
                self.ctor = c
                self.ctor_pre, self.ctor_tested = pre_of(c, ([x for x in c.get_children() if x.kind == CK.COMPOUND_STMT] or [None])[0], self.name)
            elif k == CK.DESTRUCTOR:
                body = [x for x in c.get_children() if x.kind == CK.COMPOUND_STMT]
                if not body or list(body[0].get_children()):
                    refuse(c, "a destructor that does something")
            elif k == CK.CXX_METHOD:
                if c.is_virtual_method() or c.is_static_method():
                    refuse(c, "a virtual or static method (the spike reads plain methods)")
                if c.spelling.startswith("operator"):
                    refuse(c, "an operator")
                if c.spelling == "invariant":
                    self.inv = invariant_of(c)
                else:
                    self.methods.append(Method(c, self))
            elif k == CK.VAR_DECL:
                if not c.type.is_const_qualified():
                    refuse(c, "a static member that is not const: it is state outside the object")
                it = Int(c.type, c)
                value = [x for x in c.get_children() if x.kind != CK.TYPE_REF]
                lit = plain_literal(value[0]) if len(value) == 1 else None
                if lit is None or it.signed:
                    refuse(c, "a constant that is not an unsigned number given by a literal")
                self.constants[c.spelling] = lit % (1 << it.width)
            else:
                refuse(c, "%s in a model class" % k.name.lower().replace("_", " "))
        if self.ctor is None:
            refuse(cursor, "no constructor: the state would begin as anything")
        if self.inv is None and not OPTIONS["no_invariant"]:
            refuse(cursor, "no `bool invariant() const`: what is owed is derived from it, so the class "
                           "must say it (one that claims nothing is `return true;`)")
        self.field = {f.name: f for f in self.fields}
        self.public = [m for m in self.methods if m.public]


class Function(Klass):
    """A function that is not a method, read as a class with no state and one method: what is owed
    of it is that it ends and commits no memory error, for every argument."""

    def __init__(self, cursor):
        self.name = cursor.spelling
        self.cursor = None
        self.qual = cursor.spelling
        self.fields, self.constants, self.ready, self.field = [], {}, {}, {}
        self.uses, self.ctor_params = {}, []
        self.ctor = self.inv = None
        self.ctor_pre, self.ctor_tested = [], False
        self.is_function = True
        if cursor.is_static_method() or cursor.kind != CK.FUNCTION_DECL:
            refuse(cursor, "not a function")
        m = Method(cursor, self)
        m.const = m.public = True
        m.name = "call"            # the structure has the function's name: its one method is the call of it
        self.methods = self.public = [m]


# ---------------------------------------------------------------------------
# Bodies
# ---------------------------------------------------------------------------

class Body:
    """A method's statements, read (reader.BodyReader), then written as the lines of a Lean `do`
    block in Option (model.Writer)."""

    def __init__(self, klass, in_ctor=False, method=None, plain=False):
        self.k = klass
        self.r = BodyReader(klass, klass.cursor, klass.ready, in_ctor, method, plain)
        self.r.used_class = used_class
        self.w = Writer(klass, in_ctor, method, plain)
        self.assigned = self.r.assigned

    @property
    def calls_fuel(self):
        return self.r.calls_fuel

    @property
    def count(self):
        return self.r.count

    @property
    def defs(self):
        return self.w.defs

    def expr(self, c):
        return self.w.expr(self.r.expr(c))

    def cond(self, c):
        return self.w.cond(self.r.cond(c))

    def truth(self, c):
        return self.w.truth(self.r.cond(c))

    def stmts(self, c, depth, out):
        self.w.stmts(self.r.stmt(c), depth, out)


# ---------------------------------------------------------------------------
# What is written
# ---------------------------------------------------------------------------


def pre_def(k, name, bound, conds, cursor, of, tested=False):
    """What a method expects of its caller, as a Prop of the state and the arguments. The method's
    model is `none` where it is not so: so a caller that is proved safe has kept it. Or, of a way
    in for code that is not proved, what it tests: the process ends where it is not so."""
    if not all(pure for _, pure in conds):
        refuse(cursor, "a pre( condition ) that could fail to have a value (it reads an array, or calls)")
    names = " ".join(re.findall(r"\((\w+) :", bound))
    return ["/-- WHAT IS TESTED, when the program runs, at the head of %s: the process ends, saying who called, if it is not so. -/" % of.replace("`pre(...)`", "`STRONG_CHECK`") if tested else
            "/-- WHAT IS EXPECTED OF THE CALLER of %s. Not checked when the program runs: owed by whoever calls. -/" % of,
            "def %s_pre%s : Prop := %s" % (name, bound, " ∧ ".join(t for t, _ in conds)), "",
            "instance%s : Decidable (%s_pre %s) := by unfold %s_pre; infer_instance" % (bound, name, names, name), ""]


def emit_model(k, src):
    L = ["import Prooc"] + ["import %sModel" % u for u in k.uses] + ["",
         "/-! GENERATED by prover/prooc.py from %s. Do not edit." % src,
         "Each method of %s as a function: the state and the arguments in, the new state and the" % k.name,
         "result out, or `none` where the C++ would read or write outside an array or a view.",
         "A method with a loop takes `fuel`, the most rounds any of its loops may run: `none` also",
         "if that is not enough. So a result at all means the C++ ends, with no memory error. -/", "",
         "set_option linter.unusedVariables false", "",
         "structure %s%s where" % (k.name, " (%s : Type)" % k.generic[0] if k.generic else "")]
    for f in k.fields:
        L.append("  %s : %s" % (lean_name(f.name), f.lean()))
    inv, pure = Body(k, plain=True).cond(k.inv) if k.inv is not None else ("True", True)
    if not pure:
        refuse(k.inv, "an invariant that could fail to have a value")
    L += ["", "namespace %s" % k.name, "",
          "/-- THE INVARIANT, as the class says it: `invariant()` in %s. -/" % src if k.inv is not None else
          "/-- A function has no state: there is nothing for an invariant to say (%s). -/" % src if k.is_function else
          "/-- The class in %s says NO INVARIANT (it has no `bool invariant() const`): nothing is claimed\n"
          "of its state, and what is owed of it is memory and ending alone. -/" % src,
          "def Inv%s (me : %s) : Prop := %s" % (k.gb, k.lt, inv), "",
          "instance%s (me : %s) : Decidable (Inv%s me) := by unfold Inv; infer_instance" % (k.gb, k.lt, k.ga), "",
          "/-- Storage before the constructor has run. The constructor assigns every field, and reads none",
          "(the generator checked), so nothing depends on these values. -/",
          "def raw%s : %s := { %s }" % (k.gb, k.lt, ", ".join("%s := %s" % (lean_name(f.name), f.zero()) for f in k.fields)) if k.fields
          else "def raw%s : %s := {}" % (k.gb, k.lt),
          ""]
    body = Body(k, in_ctor=True)
    lines = []
    ctor_body = [c for c in k.ctor.get_children() if c.kind == CK.COMPOUND_STMT] if not k.is_function else [None]
    if len(ctor_body) != 1:
        refuse(k.ctor, "a constructor with no body here")
    # The initializer list: FIELD( value ), or FIELD() for zeros. None may read a field (expr refuses
    # it in a constructor), so the order C++ runs them in does not matter.
    parts = [c for c in k.ctor.get_children() if c.kind not in (CK.COMPOUND_STMT, CK.PARM_DECL)] if not k.is_function else []
    while parts:
        c = parts.pop(0)
        if c.kind != CK.MEMBER_REF or c.spelling not in k.field:
            refuse(c, "an initializer that is not of a field of this class")
        f = k.field[c.spelling]
        init = parts.pop(0) if parts and parts[0].kind != CK.MEMBER_REF else None
        zeros = init is None or (init.kind == CK.UNEXPOSED_EXPR and not list(init.get_children()))
        if f.count is not None:
            if not zeros:
                refuse(c, "an array initialised by anything but `()`, which is zeros")
            lines.append("  me := { me with %s := %s }" % (lean_name(f.name), f.zero()))
            body.assigned.update((f.name, i) for i in range(f.count))
        else:
            if not zeros and not isinstance(f.type, GenT) and not (f.type.is_bool and k.generic) and Int(init.type, init).width != f.type.width:
                refuse(init, "an initializer that is not the field's own type")
            given = f.zero() if zeros else body.truth(init) if f.type.is_bool and k.generic else body.expr(init)
            lines.append("  me := { me with %s := %s }" % (lean_name(f.name), given))
            body.assigned.add(f.name)
    if not k.is_function:
        body.stmts(ctor_body[0], 1, lines)
    if lines and lines[-1].strip() == "pure ()":
        lines.pop()
    for f in k.fields:
        missing = ([f.name] if f.count is None and f.name not in body.assigned else
                   ["%s[%d]" % (f.name, i) for i in range(f.count or 0) if (f.name, i) not in body.assigned])
        if missing:
            refuse(k.ctor, "the constructor does not assign %s: it would begin as anything" % ", ".join(missing))
    cb = "".join(" (%s : %s)" % (lean_name(n), t.lean()) for n, t in k.ctor_params)
    ca = "".join(" " + lean_name(n) for n, _ in k.ctor_params)
    must = []
    if k.ctor_pre:
        L += pre_def(k, "new", k.gb + cb, [Body(k, in_ctor=True).cond(c) for c in k.ctor_pre], k.ctor_pre[0],
                     "the constructor: `pre(...)`", k.ctor_tested)
        must = ["  let _ ← (if %s.new_pre%s%s then some () else none)" % (k.name, k.ga, ca)]
    L += ["def new%s%s : Option %s := do" % (k.gb, cb, "(%s)" % k.lt if k.generic else k.name),
          "  let mut me := %s" % ("%s.raw%s" % (k.name, k.ga) if k.ctor_params or k.generic else "raw")] + must + lines + ["  return me", ""]
    for m in k.methods:
        lines = []
        body = Body(k, method=m)
        body.stmts(m.body, 1, lines)
        m.fuel = body.count > 0 or body.calls_fuel
        k.ready[m.name] = m
        fuel = "fuel" if m.fuel else "0"
        lines = [x.replace("‹FUEL›", fuel) for x in lines]
        L += [x.replace("‹FUEL›", "fuel") for x in body.defs]
        if m.pre:
            if m.name + "_pre" in k.ready:
                refuse(m.cursor, "a method named as another's precondition is")
            L += pre_def(k, m.name, k.gb + " (me : %s)%s" % (k.lt, binders(m)),
                         [Body(k, method=m, plain=True).cond(c) for c in m.pre], m.pre[0], "`%s`: `pre(...)`" % m.name, m.tested)
        if not m.public:
            L.append("/-- `%s` is not public: nothing is owed of it alone, only of the public methods that call it. -/" % m.name)
        L.append("def %s%s%s (me : %s)%s : Option (%s × %s) := do"
                 % (lean_name(m.name), k.gb, " (fuel : Nat)" if m.fuel else "", k.lt, binders(m), k.lt, result_type(m)))
        L.append("  let mut me := me")
        for n, _ in m.params:
            L.append("  let mut %s := %s" % (lean_name(n), lean_name(n)))
        if m.pre:
            L.append("  let _ ← (if %s.%s%s me%s then some () else none)"
                     % (k.name, lean_name(m.name + "_pre"), k.ga, "".join(" " + lean_name(n) for n, _ in m.params)))
        L += lines
        last = list(m.body.get_children())
        if not last or last[-1].kind != CK.RETURN_STMT:
            L.append("  return (me, ())" if m.result is None else "  none  -- the C++ falls off the end: undefined")
        L.append("")
    L.append("end %s" % k.name)
    return "\n".join(L) + "\n"


def main():
    ap = argparse.ArgumentParser(description="write what must be proven of a C++ class, for Lean")
    ap.add_argument("sources", nargs="+")
    ap.add_argument("--class", dest="klass", help="the one source is a file of another program: read this class of it, as it stands")
    ap.add_argument("--function", help="as --class, for a function that is not a method")
    ap.add_argument("--uses", action="append", default=[], metavar="FILE:CLASS",
                    help="with --class: a class its methods take as a parameter, read from its own file")
    ap.add_argument("--needs", action="append", default=[], metavar="FILE:NAME",
                    help="with --class: a name for a type or a number that it is written with, read from its own file")
    ap.add_argument("--invariant-may-be-absent", action="store_true",
                    help="a class with no `bool invariant() const` claims nothing of its state (for a class that cannot be changed)")
    ap.add_argument("-o", "--out", default="prover/gen")
    ap.add_argument("--std", default="c++20")
    ap.add_argument("--steps", type=int, default=2000)
    args = ap.parse_args()

    OPTIONS["no_invariant"] = args.invariant_may_be_absent
    configure_libclang()
    index = ci.Index.create()
    builtin = probe([os.environ.get("CC", "cc"), "-print-resource-dir"], "-resource-dir") \
        or probe([os.environ.get("CC", "cc"), "-print-file-name=include"], "-isystem")
    wanted = args.klass or args.function
    if wanted and (len(args.sources) != 1 or (args.klass and args.function)):
        raise Unsupported("--class or --function reads one thing of one file")
    written = []
    for path in args.sources:
        flags = ["-x", "c++", "-std=" + args.std, "-Wno-pragma-once-outside-header",
                 "-I" + os.path.dirname(os.path.abspath(path)),
                 "-I" + os.path.join(os.path.dirname(os.path.abspath(__file__)), "model")] + builtin
        qual = None
        if wanted:
            text, lines, qual = subject_text(index, path, wanted, args.std, builtin, function=bool(args.function),
                                             uses=[tuple(u.rsplit(":", 1)) for u in args.uses],
                                             needs=[tuple(u.rsplit(":", 1)) for u in args.needs])
            name = wanted + ".subject.hpp"
            said = "%s, %s" % (wanted, lines)
            here = os.path.abspath(os.path.join(args.out, name))
            written.append((name, text))
        else:
            name = said = os.path.basename(path)
            here = os.path.abspath(path)
            text = open(path, encoding="utf-8").read()
        read = with_pre(index, here, text, flags)
        header = name
        if read is not None:        # what is read, where a method says pre(...): beside the text itself
            header = name.rsplit(".", 2 if wanted else 1)[0] + ".read.hpp"
            written.append((header, read))
        READ["text"] = (read or text).encode("utf-8")
        tu = index.parse(here, args=flags + PRE_FLAGS, unsaved_files=[(here, read or text)])
        fatal = [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
        if fatal:
            for d in fatal:
                print("prooc: %s" % d, file=sys.stderr)
            return 1
        classes = file_scope(tu.cursor, here, "function" if args.function else bool(args.klass))
        if not classes:
            raise Unsupported("%s: no class at file scope" % path)
        if wanted:          # the classes it uses stand before it in the text: they are read as parameters' types
            classes = [c for c in classes if c.spelling == wanted]
        for c in classes:
            k = Function(c) if c.kind == CK.FUNCTION_DECL else Klass(c)
            k.qual = qual or k.name
            written += [(k.name + "Model.lean", emit_model(k, said)),
                        (k.name + "Owed.lean", emit_owed(k, said)),
                        (k.name + "Diff.lean", emit_diff_lean_generic(k) if k.generic else emit_diff_lean(k)),
                        (k.name + "_diff.cpp", emit_diff_cpp_generic(k, header) if k.generic else emit_diff_cpp(k, header)),
                        (k.name + ".script", emit_script(k, args.steps))]
    os.makedirs(args.out, exist_ok=True)       # everything is read before anything is written
    for name, text in written:
        open(os.path.join(args.out, name), "w").write(text)
        print("prooc: %s/%s" % (args.out, name))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Unsupported as e:
        print("prooc: refused\n  %s" % e, file=sys.stderr)
        sys.exit(2)
