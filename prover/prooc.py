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
    """A method's statements, as the lines of a Lean `do` block in Option."""

    def __init__(self, klass, in_ctor=False, method=None, plain=False):
        self.k = klass
        self.in_ctor = in_ctor
        self.plain = plain          # the invariant: a condition on the fields, which cannot fail
        self.assigned = set()       # constructor only: fields, and (field, index) for array elements
        self.m = method
        self.scope = [(n, t.lean()) for n, t in method.params] if method else []   # locals a loop carries
        self.loops = []             # the loops we are inside: (tuple text, increment cursor or None)
        self.defs = []              # the loops' and blocks' own functions, innermost first
        self.count = 0
        self.objects = {n: t for n, t in method.params if isinstance(t, ClassT)} if method else {}
        self.views = {n: n for n, t in method.params if isinstance(t, BytesT) and t.length and t.readable} if method else {}
        self.raw = {n for n, t in method.params if isinstance(t, BytesT) and t.length} if method else set()
        self.blocks = 0
        self.in_block = 0
        self.r = BodyReader(klass, klass.cursor, klass.ready, in_ctor, method, plain)
        self.r.objects, self.r.views = self.objects, self.views     # one each: the statements add to them
        self.w = Writer(klass, in_ctor, method, plain)

    def declare(self, cursor, name, lean_type):
        if any(n == name for n, _ in self.scope):
            refuse(cursor, "the name '%s' is declared twice in one method: give the inner one its own name" % name)
        self.scope.append((name, lean_type))

    def tuple_of(self, names):
        return "(%s)" % ", ".join(["me"] + [lean_name(n) for n in names])

    # ---- expressions: read, then written

    @property
    def calls_fuel(self):
        return self.r.calls_fuel

    def expr(self, c):
        return self.w.expr(self.r.expr(c))

    def cond(self, c):
        return self.w.cond(self.r.cond(c))

    def truth(self, c):
        return self.w.truth(self.r.cond(c))

    def if_line(self, c, negate=False):
        return self.w.if_line(self.r.cond(c), negate)

    def own_call(self, c):
        call = self.r.own_call(c)
        return None if call is None else (call.method, self.w.call(call))

    def own_field(self, c):
        return self.r.own_field(c)

    def array_place(self, c):
        e = self.r.array_place(c)
        return self.k.field[e.field], self.w.index(e), e.lit

    def say_return(self, value):
        return "return .ret (me, %s)" % value if self.loops else "return (me, %s)" % value

    def changed_in(self, cursors):
        """What a loop assigns: (whether the object, the names of locals)."""
        me, names = False, set()
        for top in cursors:
            if top is None:
                continue
            for c in top.walk_preorder():
                if c.kind == CK.CALL_EXPR:
                    ref = list(c.get_children())[0].referenced if list(c.get_children()) else None
                    if c.spelling == "memset" or (ref is not None and ref.kind == CK.CXX_METHOD
                                                  and (self.k.cursor is not None and ref.semantic_parent == self.k.cursor) and not ref.is_const_method()):
                        me = True
                    continue
                if c.kind == CK.UNARY_OPERATOR and self.step(c) is None:
                    continue
                if c.kind not in (CK.BINARY_OPERATOR, CK.COMPOUND_ASSIGNMENT_OPERATOR, CK.UNARY_OPERATOR):
                    continue
                lhs = list(c.get_children())[0]
                if c.kind == CK.BINARY_OPERATOR and tokens_after(c, lhs) != "=":
                    continue
                lhs = unparen(lhs)
                if lhs.kind == CK.DECL_REF_EXPR:
                    names.add(lhs.spelling)
                else:
                    me = True
        return me, names

    def outlined(self, c):
        """Whether a branch becomes a function of its own: more than one statement, and no way out
        of it but its end. Small functions are what can be reasoned about: one large one cannot."""
        if self.in_ctor or getattr(self.k, "generic", None) or c.kind != CK.COMPOUND_STMT or len(list(c.get_children())) < 2:
            return False
        return not any(x.kind in (CK.BREAK_STMT, CK.CONTINUE_STMT, CK.RETURN_STMT) for x in c.walk_preorder())

    def outline(self, c, depth, out):
        pad = "  " * depth
        mark = len(self.scope)
        me_changed, names = self.changed_in([c])
        state = [(n, t) for n, t in self.scope if n in names]
        state_names = (["me"] if me_changed else []) + [lean_name(n) for n, _ in state]
        types = ([self.k.name] if me_changed else []) + [t for _, t in state]
        self.blocks += 1
        name = "%s.block%d" % (lean_name(self.m.name), self.blocks)
        binders = " (me : %s)" % self.k.name + "".join(" (%s : %s)" % (lean_name(n), t) for n, t in self.scope)
        args = " ".join(["me"] + [lean_name(n) for n, _ in self.scope])
        B = ["/-- A branch of `%s` (%s): what it changes. -/" % (self.m.name, where(c)),
             "def %s (fuel : Nat)%s : Option (%s) := do" % (name, binders, " × ".join(types) or "Unit"),
             "  let mut me := me"]
        B += ["  let mut %s := %s" % (lean_name(n), lean_name(n)) for n, _ in state]
        loops, self.loops = self.loops, []
        self.in_block += 1
        self.stmts(c, 1, B)
        self.in_block -= 1
        self.loops = loops
        del self.scope[mark:]
        B += ["  return (%s)" % ", ".join(state_names), ""]
        self.defs += B
        raw = (["me"] if me_changed else []) + [n for n, _ in state]
        fresh = ["«%s'»" % n for n in raw]
        out.append("%slet %s ← %s ‹FUEL› %s" % (pad, "(%s)" % ", ".join(fresh) if fresh else "_", name, args))
        for n, f in zip(state_names, fresh):
            out.append("%s%s := %s" % (pad, n, f))

    def branch(self, c, depth, out):
        if self.outlined(c):
            self.outline(c, depth, out)
        else:
            self.block(c, depth, out)

    def loop(self, c, depth, out, init, cond, inc, body):
        """A loop: its body as one function (a round), the loop as another (rounds until done, or
        `none` if `fuel` rounds were not enough), and here a call that takes back what it changed."""
        pad = "  " * depth
        mark = len(self.scope)
        if init is not None:
            self.stmts(init, depth, out)
        carried = [n for n, _ in self.scope]
        me_changed, names = self.changed_in([cond, body, inc])
        state = [(n, t) for n, t in self.scope if n in names]      # what the loop hands back: only what it changes
        state_names = (["me"] if me_changed else []) + [lean_name(n) for n, _ in state]
        types = ([self.k.name] if me_changed else []) + [t for _, t in state]
        self.count += 1
        base = "%s.%%s%d" % (lean_name(self.m.name), self.count)
        binders = " (me : %s)" % self.k.name + "".join(" (%s : %s)" % (lean_name(n), t) for n, t in self.scope)
        kind = "Option (Prooc.Step (%s) (%s × %s))" % (" × ".join(types) or "Unit", self.k.name, result_type(self.m))
        here = "(%s)" % ", ".join(state_names)
        B = ["/-- One round of a loop of `%s` (%s). -/" % (self.m.name, where(c)),
             "def %s (fuel : Nat)%s : %s := do" % (base % "round", binders, kind),
             "  let mut me := me"]
        B += ["  let mut %s := %s" % (lean_name(n), lean_name(n)) for n, _ in state]
        B += ["  " + self.if_line(cond, negate=True), "    return .done %s" % here]
        self.loops.append((here, inc))
        self.stmts(body, 1, B)
        del self.scope[len(carried):]
        if inc is not None:
            self.stmts(inc, 1, B)
        self.loops.pop()
        B += ["  return .next %s" % here, ""]
        args = " ".join(["me"] + [lean_name(n) for n in carried])
        B += ["/-- The loop: rounds until it is done; `none` if `left` rounds are not enough. (`fuel` is",
              "what a loop inside a round begins with.) -/",
              "def %s (fuel : Nat) (left : Nat)%s : %s :=" % (base % "loop", binders, kind),
              "  match left with", "  | 0 => none", "  | left + 1 => do",
              "    match (← %s fuel %s) with" % (base % "round", args),
              "    | .next %s => %s fuel left %s" % (here, base % "loop", args),
              "    | .done s => pure (.done s)", "    | .ret r => pure (.ret r)", ""]
        self.defs += B
        raw = (["me"] if me_changed else []) + [n for n, _ in state]
        fresh = ["«%s'»" % n for n in raw]
        back = "(%s)" % ", ".join(fresh)
        out.append("%smatch (← %s fuel fuel %s) with" % (pad, base % "loop", args))
        out.append("%s| .ret r => %s" % (pad, "none  -- (no return is inside this branch)" if self.in_block and not self.loops
                                         else "return .ret r" if self.loops else "return r"))
        out.append("%s| .done %s | .next %s =>" % (pad, back, back))
        for n, f in zip(state_names, fresh):
            out.append("%s  %s := %s" % (pad, n, f))
        if not fresh:
            out.append("%s  pure ()" % pad)
        del self.scope[mark:]

    # ---- statements

    def stmts(self, c, depth, out):
        pad = "  " * depth
        k = c.kind
        if k == CK.COMPOUND_STMT:
            n = len(out)
            for s in c.get_children():
                self.stmts(s, depth, out)
            if len(out) == n:
                out.append(pad + "pure ()")
            return
        if k == CK.CALL_EXPR and c.spelling == "__builtin_assume":
            return          # a pre( condition ), written here by with_pre: it is the method's _pre, not a statement
        if self.in_ctor and k != CK.BINARY_OPERATOR:
            refuse(c, "the constructor may only assign each field once, in order")
        if k == CK.UNARY_OPERATOR and self.step(c) is not None:      # x++ or --x, its value not used
            lhs = list(c.get_children())[0]
            t = Int(lhs.type, lhs)
            if t.signed:
                refuse(c, "++ or -- of a signed number")
            self.assign(lhs, "(%s %s 1#%d)" % (self.expr(lhs), self.step(c), t.width), pad, out)
            return
        if k == CK.COMPOUND_ASSIGNMENT_OPERATOR:
            lhs, rhs = list(c.get_children())
            op = tokens_after(c, lhs)
            t, tr = Int(lhs.type, lhs), Int(rhs.type, rhs)
            if op not in ("+=", "-=", "*=", "&=", "|=", "^=") or t.signed or t.width < 32 or (tr.width, tr.signed) != (t.width, False):
                refuse(c, "'%s' here: the two sides are one unsigned type of 32 bits or more, and the "
                          "operator is one of + - * & | ^" % op)
            lean = {"+=": "+", "-=": "-", "*=": "*", "&=": "&&&", "|=": "|||", "^=": "^^^"}[op]
            self.assign(lhs, "(%s %s %s)" % (self.expr(lhs), lean, self.expr(rhs)), pad, out)
            return
        if k == CK.CALL_EXPR and c.spelling == "memset":
            self.memset(c, pad, out)
            return
        if k == CK.CALL_EXPR and self.own_call(c) is not None:
            m, call = self.own_call(c)
            out.append("%sme := (← %s).1" % (pad, call) if not m.const else "%slet _ ← %s" % (pad, call))
            return
        if k == CK.NULL_STMT:
            return
        if k == CK.DECL_STMT:
            for v in c.get_children():
                if v.kind != CK.VAR_DECL:
                    refuse(v, "a declaration that is not a variable")
                init = [x for x in v.get_children() if x.kind not in (CK.TYPE_REF,)]
                vt = v.type.get_canonical()
                if vt.kind == TK.POINTER:
                    # Another name for a view: `const unsigned char* p = reinterpret_cast<...>( data )`,
                    # or `= data`. It is given once (a pointer is never assigned: expr refuses one).
                    src = init[0] if len(init) == 1 else None
                    if src is not None and src.kind in (CK.CXX_REINTERPRET_CAST_EXPR, CK.CXX_STATIC_CAST_EXPR, CK.CSTYLE_CAST_EXPR):
                        inner = [x for x in src.get_children() if x.kind != CK.TYPE_REF]
                        src = inner[0] if len(inner) == 1 else None
                    src = unparen(src) if src is not None else None
                    to = vt.get_pointee()
                    if (src is None or src.kind != CK.DECL_REF_EXPR or src.spelling not in self.raw
                            or src.referenced.kind != CK.PARM_DECL or to.kind != TK.UCHAR or not to.is_const_qualified()):
                        refuse(v, "a local pointer that is not `const unsigned char*`, made once from a view's own pointer")
                    self.views[v.spelling] = src.spelling
                    continue
                if vt.kind == TK.RECORD:
                    # A value of another class, made by its constructor: `U name( arguments );`. What that
                    # constructor expects of its caller is owed here: its model is `none` where it is not so.
                    u = used_class(v, vt)
                    init = [x for x in init if x.kind != CK.TEMPLATE_REF]
                    made = unparen(init[0]) if len(init) == 1 else None
                    given = list(made.get_children()) if made is not None and made.kind == CK.CALL_EXPR else None
                    if given is None or len(given) != len(u.k.ctor_params) or self.loops or self.in_block:
                        refuse(v, "a local of a class's type that is not made by its constructor, `%s %s( ... );`, "
                                  "outside any loop" % (u.k.name, v.spelling))
                    text = ""
                    for a, (_, t) in zip(given, u.params()):
                        if Int(a.type, a).width != t.width:
                            refuse(a, "an argument that is not the parameter's own type")
                        text += " " + self.expr(a)
                    self.objects[v.spelling] = u
                    out.append("%slet %s ← %s.new%s%s" % (pad, lean_name(v.spelling), u.k.name, u.ga, text))
                    continue
                if len(init) != 1:
                    refuse(v, "the local '%s' has no first value: it would begin as anything" % v.spelling)
                t = typ(self.k, v.type, v)
                value = self.expr(init[0])
                self.declare(v, v.spelling, t.lean())
                out.append("%slet mut %s : %s := %s" % (pad, lean_name(v.spelling), t.lean(), value))
            return
        if k == CK.IF_STMT:
            parts = list(c.get_children())
            out.append(pad + self.if_line(parts[0]))
            self.branch(parts[1], depth + 1, out)
            if len(parts) > 2:
                out.append(pad + "else")
                self.branch(parts[2], depth + 1, out)
            return
        if k == CK.RETURN_STMT:
            value = list(c.get_children())
            called = unparen(value[0]) if value else None
            if called is not None and called.kind == CK.CALL_EXPR and self.own_call(called) is not None:
                m, call = self.own_call(called)     # `return method( ... );`: its state, then its answer
                if m.result is None:
                    refuse(c, "the return of a call that gives nothing")
                out.append("%slet «called» ← %s" % (pad, call))
                if not m.const:
                    out.append("%sme := «called».1" % pad)
                out.append(pad + self.say_return("«called».2"))
                return
            out.append(pad + self.say_return(self.expr(value[0]) if value else "()"))
            return
        if k in (CK.WHILE_STMT, CK.FOR_STMT) and getattr(self.k, "generic", None):
            refuse(c, "a loop in a class template")
        if k == CK.WHILE_STMT:
            cond, body = list(c.get_children())
            self.loop(c, depth, out, None, cond, None, body)
            return
        if k == CK.FOR_STMT:
            parts = list(c.get_children())
            if len(parts) != 4:
                refuse(c, "a for with a part left out: write all three, or a while")
            self.loop(c, depth, out, parts[0], parts[1], parts[2], parts[3])
            return
        if k == CK.BREAK_STMT and self.loops:
            out.append("%sreturn .done %s" % (pad, self.loops[-1][0]))
            return
        if k == CK.CONTINUE_STMT and self.loops:
            if self.loops[-1][1] is not None:
                self.stmts(self.loops[-1][1], depth, out)
            out.append("%sreturn .next %s" % (pad, self.loops[-1][0]))
            return
        if k == CK.BINARY_OPERATOR:
            lhs, rhs = list(c.get_children())
            if tokens_after(c, lhs) != "=":
                refuse(c, "an expression as a statement that is not an assignment")
            self.assign(lhs, self.expr(rhs), pad, out)
            return
        refuse(c, "%s (not in the spike's subset: no do-while, calls, switch, goto, throw, new or delete)"
               % k.name.lower().replace("_", " "))

    def step(self, c):
        """"+" or "-" if this UNARY_OPERATOR is ++ or --, before or after; else None."""
        words = [t.spelling for t in c.get_tokens()]
        for w in (words[:1] + words[-1:]):
            if w in ("++", "--"):
                return w[0]
        return None

    def assign(self, lhs, value, pad, out):
        if lhs.kind == CK.DECL_REF_EXPR and self.m is not None and lhs.spelling in self.m.lengths:
            refuse(lhs, "an assignment to a view's length: it says how many bytes may be read")
        if lhs.kind == CK.DECL_REF_EXPR:
            self.expr(lhs)
            out.append("%s%s := %s" % (pad, lean_name(lhs.spelling), value))
        elif lhs.kind == CK.MEMBER_REF_EXPR:
            f = self.own_field(lhs)
            if f.count is not None:
                refuse(lhs, "an array assigned whole")
            self.assigned.add(f.name)
            out.append("%sme := { me with %s := %s }" % (pad, lean_name(f.name), value))
        elif lhs.kind == CK.ARRAY_SUBSCRIPT_EXPR:
            f, i, lit = self.array_place(lhs)
            if self.in_ctor:
                if lit is None:
                    refuse(lhs, "the constructor names each element by a number")
                self.assigned.add((f.name, lit))
            out.append("%sme := { me with %s := (← Prooc.set me.%s %s (%s)) }"
                       % (pad, lean_name(f.name), lean_name(f.name), i, value))
        else:
            refuse(lhs, "an assignment to something that is not a local, a field, or an element")

    def memset(self, c, pad, out):
        """memset( FIELD, BYTE, sizeof( FIELD ) ), of one of the class's own arrays, whole: every
        element becomes that byte in each of its bytes. Any other memset could write anywhere."""
        parts = list(c.get_children())
        ref = unparen(parts[0]).referenced if parts else None
        if ref is None or ref.kind != CK.FUNCTION_DECL or not ref.location.is_in_system_header or len(parts) != 4:
            refuse(c, "a memset that is not the library's")
        target, size = unparen(parts[1]), unparen(parts[3])
        byte = plain_literal(parts[2])
        words = [t.spelling for t in size.get_tokens()]
        if (target.kind != CK.MEMBER_REF_EXPR or byte is None or not 0 <= byte <= 255 or size.kind != CK.CXX_UNARY_EXPR
                or [w for w in words if w not in "()"] != ["sizeof", target.spelling]):
            refuse(c, "a memset that is not memset( FIELD, BYTE, sizeof( FIELD ) ) of an array of this class")
        f = self.own_field(target)
        if f.count is None or self.in_ctor:
            refuse(c, "a memset of something that is not an array of this class")
        value = sum(byte << (8 * i) for i in range(f.type.width // 8))
        out.append("%sme := { me with %s := Vector.replicate %d %d#%d }" % (pad, lean_name(f.name), f.count, value, f.type.width))

    def block(self, c, depth, out):
        n = len(out)
        mark = len(self.scope)
        self.stmts(c, depth, out)
        del self.scope[mark:]
        if len(out) == n:
            out.append("  " * depth + "pure ()")


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
