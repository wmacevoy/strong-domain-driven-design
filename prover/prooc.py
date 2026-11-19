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

from oopcc import configure_libclang, probe, where, Unsupported   # noqa: E402

UNSIGNED = {TK.UCHAR: 8, TK.USHORT: 16, TK.UINT: 32, TK.ULONG: 64, TK.ULONGLONG: 64, TK.BOOL: 8}
OPTIONS = {"no_invariant": False}
SIGNED = {TK.INT: 32}
LEAN_WORDS = set("""at by do else end for from fun have if in let match mut of open return show then
where with def theorem structure class instance namespace section import variable universe example
local private Type Prop given""".split())


def refuse(cursor, why):
    raise Unsupported("%s: %s" % (where(cursor), why))


def lean_name(name):
    if name in ("me", "me'", "fuel", "left", "r"):
        raise Unsupported("the name '%s' is the model's own: choose another." % name)
    return "«%s»" % name if name in LEAN_WORDS else name


class Int:
    """An integer type the model knows exactly: its width, and whether it is signed."""

    def __init__(self, t, cursor):
        k = t.get_canonical().kind
        self.is_bool = k == TK.BOOL      # a byte that is 0 or 1: every way to make one here gives one of them
        if k in UNSIGNED:
            self.width, self.signed = UNSIGNED[k], False
        elif k in SIGNED:
            self.width, self.signed = SIGNED[k], True
        else:
            refuse(cursor, "the type '%s' is not one the model knows exactly (the unsigned "
                           "integers of 8 to 64 bits; int only where a literal or a promotion makes one)."
                   % t.spelling)

    def lean(self):
        return "BitVec %d" % self.width


class BytesT:
    """The byte view: a parameter only. Either a `Bytes`, read by at() and size(); or a pointer to
    const bytes with the unsigned 64-bit parameter after it, its length: read by `p[i]`, and the
    length by its name. `readable` is false for `const char*`, whose bytes are signed: it is read
    through a `const unsigned char*` local made from it."""
    width, signed, is_bool = None, False, False

    def __init__(self, length=None, readable=True, ctype="Bytes"):
        self.length, self.readable, self.ctype = length, readable, ctype

    def lean(self):
        return "Prooc.Bytes"


class GenT:
    """The type parameter of a class template, of which nothing is known but that two values of it
    may be compared by `<=`. What is proved of such a class is proved for every type and every value
    of its other parameters at once."""
    width, signed, is_bool = None, False, False

    def lean(self):
        return "T"


def is_gen(k, t):
    g = getattr(k, "generic", None)
    return bool(g) and t.spelling.replace("const ", "").strip() == g[0]


def typ(k, t, cursor):
    return GenT() if is_gen(k, t) else Int(t, cursor)


class ClassT:
    """A value of another class, as a parameter: a domain of its own, proved apart. What is owed of
    a method that takes one is owed only for values that satisfy that class's invariant, since its
    constructor and its methods are the only ways to make one. Here it is used by calling its const
    methods, and no other way."""
    width, signed, is_bool = None, False, False

    def __init__(self, klass, at=None, qual=None):
        self.k = klass
        self.at = at            # of a class template: (the type its T is here, the values of its parameters)
        self.qual = qual or klass.qual
        self.ga = "".join(" %d#%d" % (v % (1 << at[0].width), at[0].width) for v in at[1]) if at else ""

    def lean(self):
        return "(%s (%s))" % (self.k.name, self.at[0].lean()) if self.at else self.k.name

    def inv(self, name):
        return "%s.Inv%s %s" % (self.k.name, self.ga, name)

    def of(self, t):
        """A type of the class's own, as it is here: its T is the type it was given."""
        return self.at[0] if isinstance(t, GenT) else t

    def params(self):
        return [(n, self.of(t)) for n, t in self.k.ctor_params]

    def same(self, other):
        return other is not None and self.k is other.k and self.ga == other.ga


USED = {}       # the classes used as parameters, by name: read once each


def not_checked(cursor, method_name, used_name):
    """A proved class is called by proved classes, which are proved to call it rightly: it has no
    use for a test when the program runs. So only a way in for code that is not proved, a method
    named `..._checked`, may take, make or call anything `_checked`."""
    if "_checked" in used_name and not method_name.endswith("_checked"):
        refuse(cursor, "'%s' in '%s', which is not a `_checked` way in: what is proved is called by what is "
                       "proved, and tests nothing when the program runs" % (used_name, method_name))


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


PRE_FLAGS = ["-Dpre(x)=", "-Dprooc_pre=__builtin_assume"]

# What stands before a class read from another program. The standard headers a class in the subset
# can need; and the two names a way in for code that is not proved is written with:
#   STRONG_CHECK( condition, from );   as the first statements of a `_checked` constructor or method:
#       the condition is tested when the program runs, and the process ends, saying who called,
#       if it is not so. Here it is read as what the rest of the body may rest on.
#   Strong::caller                     who called: a last parameter, with a default. Not modelled.
PRELUDE = ["#include <cstddef>", "#include <cstdint>", "#include <cstring>", "",
           "namespace Strong { struct caller { caller() {} }; }",
           # Strong::subarray<T, N>, subarray_checked<T, N>: a window on an array of N of T, read by at() and
           # size(). Not modelled as a class: it is the byte view (Prooc.Bytes), and this is the text the
           # comparison runs. That the count is at most N is the constructor's to expect, or to test.
           "#ifdef PROOC_CHECKED", "#include <cstdlib>", "#define PROOC_INSIDE( c ) if ( !( c ) ) std::abort()",
           "#else", "#define PROOC_INSIDE( c )", "#endif",
           "namespace Strong {"] + [
           "template <typename T, size_t N> class %s { const T* first; uint64_t count; public: "
           "template <typename U> %s( U ( &array )[N], uint64_t n, caller = caller() ) : first( reinterpret_cast<const T*>( array ) ), count( n ) { PROOC_INSIDE( n <= N ); } "
           "uint64_t size() const { return count; } T at( uint64_t i ) const { PROOC_INSIDE( i < count ); return first[i]; } };" % (n, n)
           for n in ("subarray", "subarray_checked")] + ["}",
           "#ifndef STRONG_CHECK", "#define STRONG_CHECK( condition, from ) prooc_pre( condition )", "#endif", ""]


READ = {"text": b""}     # the text being read, as bytes: what a cursor's place is a place in


def is_caller(t):
    return t.get_canonical().spelling in ("Strong::caller", "const Strong::caller")


def with_pre(index, here, text, flags):
    """C++26 says what a method expects of its caller after its parameters: `pre( condition )`. The
    library this reads C++ with does not know that, so the text is read with `pre(...)` as nothing,
    and each condition is found by its words and written again as the first statement of its
    method's body: `prooc_pre( condition );`. Nothing else of the text is changed, and no line
    moves. The text so written, or None if no method says `pre`. What is trusted here: that a
    condition means at the head of the body what it means after the parameters."""
    if "prooc_pre" in text.replace("\n".join(PRELUDE), ""):
        raise Unsupported("%s: the name prooc_pre is the generator's own" % here)
    tu = index.parse(here, args=flags + PRE_FLAGS, unsaved_files=[(here, text)], options=0x200)
    data = text.encode("utf-8")
    adds = []

    def walk(c):
        for x in c.get_children():
            if not x.location.file or os.path.abspath(x.location.file.name) != here:
                continue
            body = [y for y in x.get_children() if y.kind == CK.COMPOUND_STMT]
            if x.kind in (CK.CXX_METHOD, CK.CONSTRUCTOR, CK.FUNCTION_DECL) and len(body) == 1:
                stop = body[0].extent.start.offset
                toks = [t for t in x.get_tokens() if t.extent.start.offset < stop]
                depth, said, i = 0, [], 0
                while i < len(toks):
                    w = toks[i].spelling
                    if w == "pre" and depth == 0 and i + 1 < len(toks) and toks[i + 1].spelling == "(":
                        j, d = i + 1, 0
                        while j < len(toks):
                            d += {"(": 1, ")": -1}.get(toks[j].spelling, 0)
                            if d == 0:
                                break
                            j += 1
                        if j == len(toks):
                            refuse(x, "a pre( that is not closed")
                        said.append(data[toks[i + 1].extent.end.offset:toks[j].extent.start.offset].decode("utf-8").strip())
                        i = j
                    else:
                        depth += {"(": 1, ")": -1}.get(w, 0)
                    i += 1
                if said:
                    adds.append((stop + 1, "".join(" prooc_pre( %s );" % q for q in said)))
            else:
                walk(x)

    walk(tu.cursor)
    if not adds:
        return None
    for at, more in sorted(adds, reverse=True):
        data = data[:at] + more.encode("utf-8") + data[at:]
    return data.decode("utf-8")


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


def subarray_of(t):
    """(the type as it is said in full, N) for a Strong::subarray or subarray_checked of unsigned char; or None."""
    m = re.match(r"(?:const )?(Strong::subarray(?:_checked)?<unsigned char, (\d+)>)$", t.get_canonical().spelling)
    return (m.group(1), int(m.group(2))) if m else None


def is_bytes(t):
    return t.get_canonical().spelling in ("Bytes", "const Bytes") or subarray_of(t) is not None


def convert(text, src, dst):
    """The value `text` of type src, as C++ converts it to dst."""
    if dst.is_bool and not src.is_bool:
        return "(if %s = 0#%d then 0#8 else 1#8)" % (text, src.width)
    if src.width == dst.width:
        return text
    if dst.width > src.width and src.signed:
        return "((%s).signExtend %d)" % (text, dst.width)
    return "((%s).setWidth %d)" % (text, dst.width)


def tokens_after(cursor, child):
    """The first token of `cursor` after the end of `child`: a binary operator's own token."""
    if cursor.kind in (CK.BINARY_OPERATOR, CK.COMPOUND_ASSIGNMENT_OPERATOR):
        # asked of the library itself: the words are not where the cursor says, inside a macro's argument
        import ctypes
        lib = ci.conf.lib
        lib.clang_getCursorBinaryOperatorKind.argtypes = [ci.Cursor]
        lib.clang_getCursorBinaryOperatorKind.restype = ctypes.c_int
        lib.clang_getBinaryOperatorKindSpelling.argtypes = [ctypes.c_int]
        lib.clang_getBinaryOperatorKindSpelling.restype = ci._CXString
        said = lib.clang_getBinaryOperatorKindSpelling(lib.clang_getCursorBinaryOperatorKind(cursor))
        text = lib.clang_getCString(said)
        text = text.decode("utf-8") if isinstance(text, bytes) else text
        if text:
            return text
    end = child.extent.end.offset
    for t in cursor.get_tokens():
        if t.extent.start.offset >= end:
            return t.spelling
    refuse(cursor, "an operator the generator could not read (is it in a macro?)")


def plain_literal(c):
    """The number an integer literal says, through the conversions around it; or None."""
    c = unparen(c)
    if c.kind != CK.INTEGER_LITERAL:
        return None
    return int(first_token(c).lower().rstrip("ul"), 0)


def outer_constant(v):
    """The number a const declared outside any class is, if a literal gives it; else None."""
    value = [x for x in v.get_children() if x.kind != CK.TYPE_REF]
    lit = plain_literal(value[0]) if len(value) == 1 else None
    it = Int(v.type, v)
    return None if lit is None or it.signed else lit % (1 << it.width)


def unparen(c):
    while c.kind in (CK.UNEXPOSED_EXPR, CK.PAREN_EXPR) and len(list(c.get_children())) == 1:
        c = list(c.get_children())[0]
    return c


def first_token(cursor):
    for t in cursor.get_tokens():
        return t.spelling
    refuse(cursor, "an expression with no text of its own (is it in a macro?)")


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
                t = BytesT(ctype=subarray_of(c.type)[0])
                t.capacity = subarray_of(c.type)[1]
                not_checked(c, self.name, t.ctype)
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
        self.calls_fuel = False     # it calls a method that has a loop
        self.objects = {n: t for n, t in method.params if isinstance(t, ClassT)} if method else {}
        self.views = {n: n for n, t in method.params if isinstance(t, BytesT) and t.length and t.readable} if method else {}
        self.raw = {n for n, t in method.params if isinstance(t, BytesT) and t.length} if method else set()
        self.blocks = 0
        self.in_block = 0

    def declare(self, cursor, name, lean_type):
        if any(n == name for n, _ in self.scope):
            refuse(cursor, "the name '%s' is declared twice in one method: give the inner one its own name" % name)
        self.scope.append((name, lean_type))

    def tuple_of(self, names):
        return "(%s)" % ", ".join(["me"] + [lean_name(n) for n in names])

    # ---- expressions

    def own_field(self, c):
        ref = c.referenced
        if ref is None or ref.kind != CK.FIELD_DECL or ref.spelling not in self.k.field:
            refuse(c, "a member that is not a field of this class")
        for child in c.get_children():
            if child.kind != CK.CXX_THIS_EXPR:
                refuse(c, "a field reached through something other than this object")
        return self.k.field[ref.spelling]

    def array_place(self, c):
        """(field, index text) for an ARRAY_SUBSCRIPT_EXPR on one of the class's own arrays."""
        base, index = list(c.get_children())
        while base.kind in (CK.UNEXPOSED_EXPR, CK.PAREN_EXPR):
            base = list(base.get_children())[0]
        if base.kind != CK.MEMBER_REF_EXPR:
            refuse(c, "an index into something that is not an array field of this class")
        f = self.own_field(base)
        if f.count is None:
            refuse(c, "an index into a field that is not an array")
        it = Int(index.type, index)
        i = self.expr(index)
        if it.signed:
            lit = self.literal(index)
            if lit is None:
                refuse(index, "an index of a signed type (it could be negative): use an unsigned one")
            return f, str(lit), lit
        return f, "(%s).toNat" % i, None

    def literal(self, c):
        """A literal's number, or a constant of the class's (a name for one)."""
        lit = plain_literal(c)
        if lit is not None:
            return lit
        c = unparen(c)
        if c.kind == CK.DECL_REF_EXPR and self.constant(c) is not None:
            return self.constant(c)
        return None

    def constant(self, c):
        ref = c.referenced
        if ref is not None and ref.kind == CK.VAR_DECL and (self.k.cursor is not None and ref.semantic_parent == self.k.cursor):
            return self.k.constants.get(ref.spelling)
        if ref is not None and ref.kind == CK.VAR_DECL and ref.semantic_parent.spelling in self.k.uses:
            return self.k.uses[ref.semantic_parent.spelling].constants.get(ref.spelling)     # U::NAME, of a class it takes
        if (ref is not None and ref.kind == CK.VAR_DECL and ref.semantic_parent.kind in (CK.NAMESPACE, CK.TRANSLATION_UNIT)
                and ref.type.is_const_qualified()):
            return outer_constant(ref)       # a name for a number, beside the classes
        return None

    def own_call(self, c):
        """(the method, the Lean text of the call) if a CALL_EXPR calls a method of this class on
        this object; else None."""
        parts = list(c.get_children())
        if not parts or parts[0].kind != CK.MEMBER_REF_EXPR:
            return None
        ref = parts[0].referenced
        if ref is None or ref.kind != CK.CXX_METHOD or (self.k.cursor is None or ref.semantic_parent != self.k.cursor):
            return None
        if any(x.kind != CK.CXX_THIS_EXPR for x in parts[0].get_children()):
            refuse(c, "a method called on something other than this object")
        if self.in_ctor or self.plain:
            refuse(c, "a call in the constructor or the invariant")
        not_checked(c, self.m.name if self.m else "the constructor", ref.spelling)
        m = self.k.ready.get(ref.spelling)
        if m is None:
            refuse(c, "a call to '%s', which is not written before this method (or is this method): "
                      "the model of a call is the model of what is called" % ref.spelling)
        args = parts[1:]
        if len(args) != len(m.params):
            refuse(c, "a call with a default argument")
        text = ""
        for a, (_, t) in zip(args, m.params):
            if isinstance(t, ClassT):
                o = unparen(a)
                while o.kind == CK.CALL_EXPR and len(list(o.get_children())) == 1:     # the copy C++ makes of it
                    o = unparen(list(o.get_children())[0])
                if o.kind != CK.DECL_REF_EXPR or not t.same(self.objects.get(o.spelling)):
                    refuse(a, "an argument of a class's type that is not the name of a value of that class")
                text += " " + lean_name(o.spelling)
                continue
            if isinstance(t, BytesT) or Int(a.type, a).width != t.width:
                refuse(a, "an argument that is not the parameter's own type")
            text += " " + self.expr(a)
        if m.fuel:
            self.calls_fuel = True
        return m, "%s.%s%s%s me%s" % (self.k.name, lean_name(m.name), self.k.ga, " ‹FUEL›" if m.fuel else "", text)

    def view_of(self, c):
        """The view a pointer's name stands for (a parameter, or a local made from one), or None."""
        c = unparen(c)
        if c.kind == CK.DECL_REF_EXPR and c.referenced is not None and c.referenced.kind in (CK.PARM_DECL, CK.VAR_DECL):
            return self.views.get(c.spelling)
        return None

    def other_call(self, c):
        """The Lean text of a call to a const method of a parameter that is another class; or None."""
        parts = list(c.get_children())
        if not parts or parts[0].kind != CK.MEMBER_REF_EXPR:
            return None
        base = [unparen(x) for x in parts[0].get_children()]
        if len(base) != 1 or base[0].kind != CK.DECL_REF_EXPR or base[0].spelling not in self.objects:
            return None
        ct = self.objects[base[0].spelling]
        k = ct.k
        ref = parts[0].referenced
        m = k.ready.get(ref.spelling) if ref is not None and ref.kind == CK.CXX_METHOD else None
        if m is None or not m.const or not m.public or m.result is None or len(parts) - 1 != len(m.params):
            refuse(c, "a call on a parameter that is not to a public const method of its class that gives a number")
        text = ""
        for a, (_, t) in zip(parts[1:], m.params):
            t = ct.of(t)
            if not isinstance(t, Int) or Int(a.type, a).width != t.width:
                refuse(a, "an argument that is not the parameter's own type")
            text += " " + self.expr(a)
        if m.fuel:
            self.calls_fuel = True
        return "((← %s.%s%s%s %s%s)).2" % (k.name, lean_name(m.name), ct.ga, " ‹FUEL›" if m.fuel else "", lean_name(base[0].spelling), text)

    def of_t(self, c):
        """Whether an expression is of a class template's own type T, or one of its value parameters."""
        if not getattr(self.k, "generic", None):
            return False
        g = unparen(c)
        return is_gen(self.k, g.type) or (g.kind == CK.DECL_REF_EXPR and g.referenced is not None
                                         and g.referenced.kind == CK.TEMPLATE_NON_TYPE_PARAMETER)

    def gexpr(self, g):
        """A value of the type T: a name for one, and nothing else. Nothing is done to a T but to
        keep it, hand it back, and compare it."""
        if g.kind == CK.DECL_REF_EXPR and g.referenced is not None and g.referenced.kind in (
                CK.TEMPLATE_NON_TYPE_PARAMETER, CK.PARM_DECL, CK.VAR_DECL):
            return lean_name(g.spelling)
        if g.kind == CK.MEMBER_REF_EXPR:
            f = self.own_field(g)
            if self.in_ctor:
                refuse(g, "the constructor reads a field")
            return "me.%s" % lean_name(f.name)
        refuse(g, "of a class template's type %s, only a name for a value: nothing is known of the "
                  "type but that two of it compare by `<=`" % self.k.generic[0])

    def truth(self, c):
        """A condition as a value: a bool, 1 or 0."""
        text, pure = self.cond(c)
        return "(if %s then 1#8 else 0#8)" % (text if pure else "(← %s)" % text)

    def expr(self, c):
        """Lean text of an integer expression, a BitVec of c.type's width."""
        k = c.kind
        if self.of_t(c):
            return self.gexpr(unparen(c))
        if c.type.get_canonical().kind in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE):
            refuse(c, "a pointer or a reference: the state could leave the class by it")
        if k == CK.INTEGER_LITERAL:
            t = Int(c.type, c)
            return "%d#%d" % (self.literal(c), t.width)
        if k == CK.PAREN_EXPR:
            return "(%s)" % self.expr(list(c.get_children())[0])
        if k in (CK.UNEXPOSED_EXPR, CK.CSTYLE_CAST_EXPR, CK.CXX_STATIC_CAST_EXPR, CK.CXX_FUNCTIONAL_CAST_EXPR):
            inner = [x for x in c.get_children() if x.kind != CK.TYPE_REF]
            if len(inner) != 1:
                refuse(c, "an expression the generator does not know")
            dst = Int(c.type, c)
            lit = self.literal(inner[0])
            if lit is not None and dst.is_bool:
                return "1#8" if lit else "0#8"
            if lit is not None:
                return "%d#%d" % (lit % (1 << dst.width), dst.width)     # a literal, converted here
            return convert(self.expr(inner[0]), Int(inner[0].type, inner[0]), dst)
        if k == CK.CXX_BOOL_LITERAL_EXPR:
            return "1#8" if first_token(c) == "true" else "0#8"
        if k == CK.DECL_REF_EXPR and self.constant(c) is not None:
            return "%d#%d" % (self.constant(c), Int(c.type, c).width)
        if (k == CK.DECL_REF_EXPR and self.m is not None and c.spelling in self.m.lengths
                and c.referenced is not None and c.referenced.kind == CK.PARM_DECL):
            return "(Prooc.Bytes.size %s)" % lean_name(self.m.lengths[c.spelling])     # a view's length, by its name
        if k == CK.DECL_REF_EXPR:
            ref = c.referenced
            if ref is None or ref.kind not in (CK.VAR_DECL, CK.PARM_DECL) or ref.semantic_parent.kind == CK.TRANSLATION_UNIT:
                refuse(c, "a name that is not a local or a parameter (a global is state outside the class)")
            Int(c.type, c)
            return lean_name(c.spelling)
        if k == CK.MEMBER_REF_EXPR:
            f = self.own_field(c)
            if f.count is not None:
                refuse(c, "an array used whole: only its elements are read")
            if self.in_ctor:
                refuse(c, "a field read in the constructor (it may not have a value yet)")
            return "me.%s" % lean_name(f.name)
        if k == CK.ARRAY_SUBSCRIPT_EXPR and unparen(list(c.get_children())[0]).kind == CK.DECL_REF_EXPR:
            base, index = list(c.get_children())
            view = self.view_of(base)
            if view is None:
                refuse(c, "an index into a pointer that is not a view of const unsigned bytes (a parameter "
                          "with its length after it, or a `const unsigned char*` local made from one)")
            if Int(index.type, index).signed:
                lit = self.literal(index)
                if lit is None or lit < 0:
                    refuse(index, "an index of a signed type (it could be negative): use an unsigned one")
                return "(← Prooc.Bytes.read %s %d)" % (lean_name(view), lit)
            return "(← Prooc.Bytes.read %s (%s).toNat)" % (lean_name(view), self.expr(index))
        if k == CK.ARRAY_SUBSCRIPT_EXPR:
            if self.in_ctor:
                refuse(c, "an element read in the constructor (it may not have a value yet)")
            f, i, lit = self.array_place(c)
            if self.plain:
                if lit is None or lit >= f.count:
                    refuse(c, "the invariant names an element by a number inside the array")
                return "me.%s[%d]" % (lean_name(f.name), lit)
            return "(← Prooc.get me.%s %s)" % (lean_name(f.name), i)
        if k == CK.CALL_EXPR and self.other_call(c) is not None:
            return self.other_call(c)
        if k == CK.CALL_EXPR and self.own_call(c) is not None:
            m, call = self.own_call(c)
            if not m.const or m.result is None:
                refuse(c, "a call inside an expression to a method that is not const, or gives nothing: "
                          "make the call a statement of its own")
            return "((← %s)).2" % call
        if k == CK.CALL_EXPR:
            parts = list(c.get_children())
            callee = parts[0] if parts else None
            if callee is None or callee.kind != CK.MEMBER_REF_EXPR or callee.spelling not in ("at", "size"):
                refuse(c, "a call that is not to a method of this class, nor at() or size() of a Bytes parameter")
            view = list(callee.get_children())
            while view and view[0].kind in (CK.UNEXPOSED_EXPR, CK.PAREN_EXPR):
                view = list(view[0].get_children())
            if (len(view) != 1 or view[0].kind != CK.DECL_REF_EXPR or view[0].referenced.kind != CK.PARM_DECL
                    or not is_bytes(view[0].type)):
                refuse(c, "at() or size() of something that is not a Bytes parameter")
            name = lean_name(view[0].spelling)
            if callee.spelling == "size":
                if len(parts) != 1 or Int(c.type, c).width != 64:
                    refuse(c, "size() takes nothing and gives 64 bits")
                return "(Prooc.Bytes.size %s)" % name
            if len(parts) != 2:
                refuse(c, "at() takes one unsigned index")
            lit = self.literal(parts[1])
            if lit is not None and lit >= 0:       # as `p[4]` is read
                return "(← Prooc.Bytes.read %s %d)" % (name, lit)
            if Int(parts[1].type, parts[1]).signed:
                refuse(c, "at() takes one unsigned index")
            return "(← Prooc.Bytes.read %s (%s).toNat)" % (name, self.expr(parts[1]))
        if k == CK.BINARY_OPERATOR:
            a, b = list(c.get_children())
            op = tokens_after(c, a)
            if op in ("<", "<=", ">", ">=", "==", "!=", "&&", "||"):
                return self.truth(c)
            t = Int(c.type, c)
            if op in ("/", "%"):
                if t.signed or Int(a.type, a).width != t.width or Int(b.type, b).width != t.width:
                    refuse(c, "'%s' on signed numbers, or on two different types" % op)
                by = self.literal(b)
                if by is not None and by % (1 << t.width) != 0:
                    return "(%s %s %s)" % (self.expr(a), op, self.expr(b))
                # By a number known only when it runs: undefined at zero, so owed never to be.
                if self.plain or by is not None:
                    refuse(c, "a division by zero, or in the invariant by a number that is not a literal")
                return "(← Prooc.%s %s %s)" % ("div" if op == "/" else "mod", self.expr(a), self.expr(b))
            if op in ("<<", ">>"):
                amount = self.literal(b)
                if t.signed or (amount is not None and not 0 <= amount < t.width):
                    refuse(c, "a shift of a signed number, or by a literal that is not below the width: "
                              "either can be undefined")
                if amount is not None:
                    return "(%s %s %d)" % (self.expr(a), "<<<" if op == "<<" else ">>>", amount)
                # By an amount known only when it runs: undefined at the width or more, so it is an
                # error of the same standing as a read outside an array, and owed never to happen.
                if Int(b.type, b).signed:
                    refuse(c, "a shift by a signed amount (it could be negative, which is undefined): "
                              "use an unsigned one of 32 bits or more")
                if self.plain:
                    refuse(c, "a shift in the invariant by an amount that is not a literal")
                return "(← Prooc.%s %s (%s).toNat)" % ("shl" if op == "<<" else "shr", self.expr(a), self.expr(b))
            if op in ("&", "|", "^"):
                return "(%s %s %s)" % (self.expr(a), {"&": "&&&", "|": "|||", "^": "^^^"}[op], self.expr(b))
            if op in ("+", "-", "*"):
                if t.signed:
                    refuse(c, "'%s' on signed numbers can overflow, which is undefined: make them unsigned" % op)
                return "(%s %s %s)" % (self.expr(a), op, self.expr(b))
            refuse(c, "the operator '%s' here (the spike knows + - * & | ^ and comparisons)" % op)
        if k == CK.UNARY_OPERATOR:
            op = first_token(c)
            if op == "!":
                return self.truth(c)
            if op == "~":
                return "(~~~%s)" % self.expr(list(c.get_children())[0])
            refuse(c, "the operator '%s' (an address or a dereference would let state out; ++ and -- "
                      "are written as assignments)" % op)
        if k == CK.CXX_THIS_EXPR:
            refuse(c, "`this` as a value: the object could be handed to something else")
        refuse(c, "%s (not in the spike's subset)" % k.name.lower().replace("_", " "))

    def cond(self, c):
        """A condition: (text, pure). Pure text is a decidable Prop. Text that is not pure is an
        Option Bool: a condition that reads memory, kept in C++'s order, so that the right side of
        && or || is not read when the left decides."""
        k = c.kind
        if k == CK.PAREN_EXPR:
            return self.cond(list(c.get_children())[0])
        if k == CK.CXX_BOOL_LITERAL_EXPR:
            return ("True" if first_token(c) == "true" else "False"), True
        if (k == CK.UNEXPOSED_EXPR and getattr(self.k, "generic", None) and len(list(c.get_children())) == 1
                and c.type.get_canonical().kind in (TK.INVALID, TK.DEPENDENT)):
            return self.cond(list(c.get_children())[0])      # in a class template: the parentheses of an initializer
        if k == CK.UNEXPOSED_EXPR and c.type.get_canonical().kind == TK.BOOL:
            inner = list(c.get_children())[0]
            if inner.type.get_canonical().kind == TK.BOOL:
                return self.cond(inner)
            return self.leaf("(%s ≠ 0#%d)" % (self.expr(inner), Int(inner.type, inner).width))
        if k == CK.UNARY_OPERATOR and first_token(c) == "!":
            text, pure = self.cond(list(c.get_children())[0])
            return ("(¬ %s)" % text, True) if pure else ("(do pure (!(← %s)))" % text, False)
        if k == CK.BINARY_OPERATOR:
            a, b = list(c.get_children())
            op = tokens_after(c, a)
            if op in ("&&", "||"):
                (x, px), (y, py) = self.cond(a), self.cond(b)
                if px and py:
                    return "(%s %s %s)" % (x, "∧" if op == "&&" else "∨", y), True
                x = "(pure (decide %s))" % x if px else x
                y = "(pure (decide %s))" % y if py else y
                if op == "&&":
                    return "(do if (← %s) then %s else pure false)" % (x, y), False
                return "(do if (← %s) then pure true else %s)" % (x, y), False
            if op in ("<", "<=", ">", ">=", "==", "!=") and (self.of_t(a) or self.of_t(b)):
                if op != "<=" or not (self.of_t(a) and self.of_t(b)):
                    refuse(c, "two values of a class template's type are compared by `<=`, and no other way")
                return "(%s ≤ %s)" % (self.expr(a), self.expr(b)), True
            if op in ("<", "<=", ">", ">=", "==", "!="):
                ta, tb = Int(a.type, a), Int(b.type, b)
                if (ta.width, ta.signed) != (tb.width, tb.signed):
                    refuse(c, "a comparison of two different types")
                x, y = self.expr(a), self.expr(b)
                if op == "==":
                    return self.leaf("(%s = %s)" % (x, y))
                if op == "!=":
                    return self.leaf("(%s ≠ %s)" % (x, y))
                if ta.signed:
                    f = {"<": "BitVec.slt %s %s", "<=": "BitVec.sle %s %s",
                         ">": "BitVec.slt %s %s", ">=": "BitVec.sle %s %s"}[op]
                    return self.leaf("(%s = true)" % (f % ((x, y) if op in ("<", "<=") else (y, x))))
                return self.leaf("(%s %s %s)" % (x, {"<": "<", "<=": "≤", ">": ">", ">=": "≥"}[op], y))
        if c.type.get_canonical().kind == TK.BOOL and k in (CK.DECL_REF_EXPR, CK.MEMBER_REF_EXPR, CK.CALL_EXPR):
            return self.leaf("(%s ≠ 0#8)" % self.expr(c))
        refuse(c, "a condition the generator does not know (comparisons, !, && and ||)")

    def leaf(self, prop):
        if "←" in prop:
            return "(do pure (decide %s))" % prop, False
        return prop, True

    def if_line(self, c, negate=False):
        text, pure = self.cond(c)
        if pure:
            return "if %s%s then" % ("¬ " if negate else "", text)
        return "if %s(← %s) then" % ("!" if negate else "", text)

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

def binders(m):
    return "".join(" (%s : %s)" % (lean_name(n), t.lean()) for n, t in m.params)


def result_type(m):
    return "Unit" if m.result is None else m.result.lean()


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


def emit_owed(k, src):
    n, G, ga, lt = k.name, k.gb, k.ga, k.lt
    cb = "".join(" (%s : %s)" % (lean_name(p), t.lean()) for p, t in k.ctor_params)
    ca = "".join(" " + lean_name(p) for p, _ in k.ctor_params)
    inv = "%s.Inv%s" % (n, ga)
    new = "%s.new%s%s" % (n, ga, ca)
    L = ["import %sModel" % n, "",
         "/-! GENERATED by prover/prooc.py from %s. Do not edit." % src,
         "WHAT MUST BE PROVEN of %s, derived from the class and from nothing else: this file imports" % n,
         "the model, and nothing written by hand. A proof of `%s.Owed` is the product. With the" % n,
         "first two statements, the rest are induction over every history of calls, with no bound. -/", ""]
    if k.generic:
        L[3:3] = ["%s is a class template: each statement is of every type %s whose values compare, and of" % (n, k.generic[0]),
                    "every value of %s. So it is proved once, for all of them." % " and ".join(k.generic[1])]
    L += ["structure %s.Owed : Prop where" % n,
          "  /-- The constructor commits no memory error%s. -/" % (", where what it tests is so (the process ends otherwise)" if k.ctor_tested else
                                                                   ", given what it expects of its caller" if k.ctor_pre else
                                                                   ", whatever it is given" if k.ctor_params else ""),
          "  new_safe : %s.isSome" % new if not (k.ctor_params or G) else
          "  new_safe : ∀%s%s, %s(%s).isSome" % (G, cb, "%s.new_pre%s%s → " % (n, ga, ca) if k.ctor_pre else "", new),
          "  /-- A new object satisfies the invariant%s. -/" % (", whatever it was made from" if k.ctor_params else ""),
          "  new_inv : ∀%s%s (me : %s), %s = some me → %s me" % (G, cb, lt, new, inv)]
    for m in k.public:
        mn = lean_name(m.name)
        call = "%s.%s%s" % (n, mn, ga)
        args = "".join(" " + lean_name(p) for p, _ in m.params)
        # A parameter that is another class's value satisfies that class's invariant: its
        # constructor and methods are the only ways to make one, and they are owed to keep it.
        given = "".join("%s → " % t.inv(lean_name(p)) for p, t in m.params if isinstance(t, ClassT))
        if m.pre:           # what it expects of its caller: owed by the caller, given here
            given += "%s.%s%s me%s → " % (n, lean_name(m.name + "_pre"), ga, args)
        hyp = "%s me → %s" % (inv, given)
        me = "∀%s (me : %s)%s" % (G, lt, binders(m))
        out = "(me' : %s) (r : %s)" % (lt, result_type(m))
        # A loop's model takes `fuel`, and is `none` if that many rounds are not enough; with enough
        # it is the C++'s run. So "for some fuel there is a result" says the C++ ends.
        if m.fuel and m.const:
            L += ["  /-- `%s` ends, and commits no memory error, from any state that satisfies the invariant. -/" % m.name,
                  "  %s_ends : %s, %s∃ (fuel : Nat), (%s fuel me%s).isSome" % (m.name, me, hyp, call, args)]
        elif m.fuel:
            L += ["  /-- `%s` ends, commits no memory error, and leaves the invariant true, from any state" % m.name,
                  "  that satisfies it. -/",
                  "  %s_ends : %s, %s∃ (fuel : Nat) %s, %s fuel me%s = some (me', r) ∧ %s me'"
                  % (m.name, me, hyp, out, call, args, inv)]
        else:
            L += ["  /-- `%s` commits no memory error, from any state that satisfies the invariant. -/" % m.name,
                  "  %s_safe : %s, %s(%s me%s).isSome" % (m.name, me, hyp, call, args)]
        fuel_all, fuel = (" (fuel : Nat)", " fuel") if m.fuel else ("", "")
        if m.const and not k.is_function:
            L += ["  /-- `%s` is const: it leaves the state as it was. -/" % m.name,
                  "  %s_same : ∀%s%s (me : %s)%s %s, %s%s me%s = some (me', r) → me' = me"
                  % (m.name, G, fuel_all, lt, binders(m), out, call, fuel, args)]
        elif not m.fuel and not k.is_function:
            L += ["  /-- `%s` leaves the invariant true. -/" % m.name,
                  "  %s_inv : %s %s, %s%s me%s = some (me', r) → %s me'"
                  % (m.name, me, out, hyp, call, args, inv)]
    return "\n".join(L) + "\n"


# The model and the C++ are driven by one script: a line is a method's number, then its arguments,
# a number in decimal or a view's bytes in hex ("-" for none). Each prints the method, its result,
# and whether the invariant holds after it: the invariant is read from the C++ too, and compared.

def diff_words(t, j):
    """The names of a parameter's words in a line of the script: one, or for a value of another
    class, what its constructor takes."""
    if isinstance(t, ClassT):
        return ["a%d_%d" % (j, i) for i in range(len(t.k.ctor_params))]
    return ["a%d" % j]


def lean_int(t, word):
    return "(BitVec.ofNat %d %s.toNat!)" % (t.width, word)


def cpp_type(t):
    return "bool" if t.is_bool else "uint%d_t" % t.width


def qual_of(cursor):
    """A class's name with its namespaces."""
    names, c = [cursor.spelling], cursor.semantic_parent
    while c is not None and c.kind == CK.NAMESPACE:
        names.insert(0, c.spelling)
        c = c.semantic_parent
    return "::".join(names)


def emit_diff_lean(k):
    n = k.name
    made = 's!"new inv={if %s.Inv me then 1 else 0}"' % n
    L = ["import %sModel" % n, "",
         "/-! GENERATED by prover/prooc.py. The model of %s, driven by the script on standard input. -/" % n, "",
         "partial def run (me : %s) (stdin : IO.FS.Stream) : IO Unit := do" % n,
         "  let line ← stdin.getLine",
         "  if line.isEmpty then return",
         "  match (line.splitOn \"\\n\").head!.splitOn \" \" with"]
    for i, m in enumerate(k.public):
        pats, args, objects = [], "", []
        for j, (p, t) in enumerate(m.params):
            words = diff_words(t, j)
            pats += words
            if isinstance(t, BytesT):
                args += " (Prooc.Bytes.ofHex a%d)" % j
            elif isinstance(t, ClassT):       # made as the C++ makes it: by its constructor
                objects.append(("o%d" % j, "%s.new%s%s" % (t.k.name, t.ga, "".join(" " + lean_int(ct, w) for (_, ct), w in zip(t.params(), words)))))
                args += " o%d" % j
            else:
                args += " " + lean_int(t, "a%d" % j)
        show = 's!"%s %s inv={if %s.Inv me then 1 else 0}"' % (m.name, "-" if m.result is None else "{r.toNat}", n)
        L.append("  | [%s] =>" % ", ".join(['"%d"' % i] + pats))
        pad = "    "
        for (name, new), u in zip(objects, [t.k for _, t in m.params if isinstance(t, ClassT)]):
            L += ["%smatch %s with" % (pad, new)]
            L += (["%s| none =>" % pad, "%s  IO.println \"%s pre\"" % (pad, m.name), "%s  run me stdin" % pad] if u.ctor_pre else
                  ["%s| none => IO.println \"%s MEMORY ERROR\"" % (pad, m.name)])
            L += ["%s| some %s =>" % (pad, name)]
            pad += "  "
        if m.pre:           # not what its caller owes it: the C++ is not called either
            L += ["%sif ¬ (%s.%s me%s) then" % (pad, n, lean_name(m.name + "_pre"), args),
                  "%s  IO.println \"%s pre\"" % (pad, m.name), "%s  run me stdin" % pad, "%selse" % pad]
            pad += "  "
        L += ["%smatch %s.%s%s me%s with" % (pad, n, lean_name(m.name), " 4294967296" if m.fuel else "", args),
              "%s| some (me, %s) =>" % (pad, "_" if m.result is None else "r"),
              "%s  IO.println %s" % (pad, show), "%s  run me stdin" % pad,
              "%s| none => IO.println \"%s MEMORY ERROR\"" % (pad, m.name)]
    if k.ctor_params:       # a line that makes the object anew, from what its constructor takes
        words = ["c%d" % i for i in range(len(k.ctor_params))]
        L += ["  | [%s] =>" % ", ".join(['"%d"' % len(k.public)] + words),
              "    match %s.new%s with" % (n, "".join(" " + lean_int(t, w) for (_, t), w in zip(k.ctor_params, words))),
              "    | some me =>", "      IO.println %s" % made, "      run me stdin"]
        L += (["    | none =>", "      IO.println \"new pre\"", "      run me stdin"] if k.ctor_pre else
              ["    | none => IO.println \"new MEMORY ERROR\""])
    L += ["  | _ => IO.println \"a line the script should not have\"", ""]
    if k.ctor_pre:
        # There is no object until a line makes one from what its constructor expects.
        L += ["partial def start (stdin : IO.FS.Stream) : IO Unit := do",
              "  let line ← stdin.getLine",
              "  if line.isEmpty then return",
              "  match (line.splitOn \"\\n\").head!.splitOn \" \" with",
              "  | [%s] =>" % ", ".join(['"%d"' % len(k.public)] + words),
              "    match %s.new%s with" % (n, "".join(" " + lean_int(t, w) for (_, t), w in zip(k.ctor_params, words))),
              "    | some me =>", "      IO.println %s" % made, "      run me stdin",
              "    | none =>", "      IO.println \"new pre\"", "      start stdin",
              "  | _ =>", "    IO.println \"no object\"", "    start stdin", "",
              "def main : IO Unit := do", "  start (← IO.getStdin)"]
    else:
        L += ["def main : IO Unit := do",
              "  match %s.new%s with" % (n, "".join(" 0#%d" % t.width for _, t in k.ctor_params)),
              "  | some me =>",
              "    IO.println %s" % made,
              "    run me (← IO.getStdin)",
              "  | none => IO.println \"new MEMORY ERROR\""]
    return "\n".join(L) + "\n"


def emit_diff_cpp(k, header):
    n = k.name
    me = "(*at)" if k.ctor_pre else "me"
    inv = "(int)%s.invariant()" % me if k.inv is not None else "1"
    zeros = "(%s)" % ", ".join("0" for _ in k.ctor_params) if k.ctor_params else ""
    L = ["/* GENERATED by prover/prooc.py. %s itself, driven by the script on standard input. */" % n]
    if header.endswith(".read.hpp"):
        L += ["#define pre(x)"]
    pre = True  # what a method expects of its caller, or tests, is tested here: so that the script may ask anything
    L += ["#define prooc_pre(x) do { if (!(x)) throw 0; } while (0)", "#define STRONG_CHECK( condition, from ) do { (void)( from ); if ( !( condition ) ) throw 0; } while ( 0 )", "#include <new>"]
    L += ['#include "%s"' % header, "#include <cstdint>", "#include <cstdio>", "#include <cstdlib>",
         "#include <sstream>", "#include <iostream>", "#include <string>", "#include <vector>", "",
         "[[maybe_unused]] static std::vector<uint8_t> unhex(const std::string &h) {",
         "  std::vector<uint8_t> out;",
         "  for (size_t i = 0; i + 1 < h.size(); i += 2) out.push_back((uint8_t)std::stoul(h.substr(i, 2), 0, 16));",
         "  return out;", "}", "",
         "int main() {", "  std::string line;"]
    if k.ctor_pre:      # no object until a line makes one
        L += ["  alignas(%s) static unsigned char store[sizeof(%s)];" % (k.qual, k.qual), "  %s *at = nullptr;" % k.qual]
    elif not k.is_function:
        L += ["  %s me%s;" % (k.qual, zeros)]
    if not k.ctor_pre:
        L += ['  std::printf("new inv=%%d\\n", %s);' % inv]
    L += ["  while (std::getline(std::cin, line)) {",
          "    std::istringstream in(line);", "    int which; in >> which;"]
    if k.ctor_pre:
        L += ['    if (!at && which != %d) { std::printf("no object\\n"); continue; }' % len(k.public)]
    for i, m in enumerate(k.public):
        L.append("    if (which == %d) {" % i)
        L.append("      try {" if pre else "      {")
        args = []
        for j, (p, t) in enumerate(m.params):
            if isinstance(t, ClassT):       # a value of another class: made by its constructor
                made = []
                for i2, (_, ct) in enumerate(t.params()):
                    L.append("      unsigned long long n%d_%d; in >> n%d_%d;" % (j, i2, j, i2))
                    made.append("(%s)n%d_%d" % (cpp_type(ct), j, i2))
                L.append("      %s a%d%s;" % (t.qual, j, "(%s)" % ", ".join(made) if made else ""))
            elif isinstance(t, BytesT):
                L += ["      std::string h%d; in >> h%d;" % (j, j),
                      "      std::vector<uint8_t> b%d = unhex(h%d);" % (j, j)]
                if t.length:        # a pointer and its length: two arguments
                    args.append("reinterpret_cast<const %s *>(b%d.data()), b%d.size()" % (t.ctype, j, j))
                    continue
                if t.ctype != "Bytes":      # a window on an array: the bytes are put in one of its size
                    L += ["      static unsigned char s%d[%d]; std::memcpy(s%d, b%d.data(), b%d.size());" % (j, t.capacity, j, j, j),
                          "      %s a%d(s%d, b%d.size());" % (t.ctype, j, j, j)]
                    args.append("a%d" % j)
                    continue
                L += ["      Bytes a%d(b%d.data(), b%d.size());" % (j, j, j)]
            else:
                L += ["      unsigned long long n%d; in >> n%d;" % (j, j),
                      "      %s a%d = (%s)n%d;" % (cpp_type(t), j, cpp_type(t), j)]
            args.append("a%d" % j)
        call = "%s(%s)" % (k.qual if k.is_function else me + "." + m.name, ", ".join(args))
        if m.result is None:
            L += ["      %s;" % call, '      std::printf("%s - inv=%%d\\n", %s);' % (m.name, inv)]
        else:
            L += ["      unsigned long long r = %s;" % call,
                  '      std::printf("%s %%llu inv=%%d\\n", r, %s);' % (m.name, inv)]
        L.append('      } catch (int) { std::printf("%s pre\\n"); }' % m.name if pre else "      }")
        L.append("    }")
    if k.ctor_params:
        L.append("    if (which == %d) {" % len(k.public))
        made = []
        for i2, (_, ct) in enumerate(k.ctor_params):
            L.append("      unsigned long long c%d; in >> c%d;" % (i2, i2))
            made.append("(%s)c%d" % (cpp_type(ct), i2))
        if k.ctor_pre:
            L += ["      try {", "        %s made(%s);" % (k.qual, ", ".join(made)),
                  "        if (at) *at = made; else at = new (store) %s(made);" % k.qual,
                  '        std::printf("new inv=%%d\\n", %s);' % inv,
                  '      } catch (int) { std::printf("new pre\\n"); }', "    }"]
        else:
            L += ["      me = %s(%s);" % (k.qual, ", ".join(made)), '      std::printf("new inv=%%d\\n", %s);' % inv, "    }"]
    L += ["  }", "  return 0;", "}"]
    return "\n".join(L) + "\n"


# A class template is proved once, of every type. Its model is compared with the C++ at four: an
# unsigned and a signed integer, and the two floating types, each with bounds of its own. A value
# crosses as its 64 (or 32) bits, so that what is not a number, and the infinities, are tried too.
# (tag, the C++ type, Lean's, the values of the template's parameters in each, bits to a value, and back)
AT = [("uint64_t", "uint64_t", "BitVec 64", ["5", "1000"], ["5#64", "1000#64"],
       "(BitVec.ofNat 64 w)", "r.toNat"),
      ("int64_t", "int64_t", "Int64", ["-5", "1000"], ["(-5 : Int64)", "(1000 : Int64)"],
       "(UInt64.ofNat w).toInt64", "r.toUInt64.toNat"),
      ("double", "double", "Float", ["-1.5", "2.5"], ["(-1.5 : Float)", "(2.5 : Float)"],
       "(Float.ofBits (UInt64.ofNat w))", "r.toBits.toNat"),
      ("float", "float", "Float32", ["-1.5f", "2.5f"], ["(-1.5 : Float32)", "(2.5 : Float32)"],
       "(Float32.ofBits (UInt32.ofNat w))", "r.toBits.toNat")]


def generic_ok(k):
    for m in k.public:
        if any(not isinstance(t, (GenT, Int)) for _, t in m.params):
            refuse(m.cursor, "a class template's method that takes a view or another class")
    if len(k.generic[1]) != 2:
        refuse(k.cursor, "a class template of other than two values (the comparison knows two: the bounds)")


def emit_diff_lean_generic(k):
    generic_ok(k)
    n, T = k.name, k.generic[0]
    inv = "{if %s.Inv%s me then 1 else 0}" % (n, k.ga)
    again = "run%s rd wr %%s rest" % k.ga

    def value(t, word):
        return "(rd %s.toNat!)" % word if isinstance(t, GenT) else lean_int(t, word)

    L = ["import %sModel" % n, "",
         "/-! GENERATED by prover/prooc.py. The model of %s, at one type, driven by the script. -/" % n, "",
         "partial def run%s (rd : Nat → %s) (wr : %s → Nat) (me? : Option (%s)) (lines : List String) : IO Unit := do"
         % (k.gb, T, T, k.lt),
         "  match lines with",
         "  | [] => return",
         "  | line :: rest =>",
         "  match line.splitOn \" \", me? with"]
    words = ["c%d" % i for i in range(len(k.ctor_params))]
    L += ["  | [%s], _ =>" % ", ".join(['"%d"' % len(k.public)] + words),
          "    match %s.new%s%s with" % (n, k.ga, "".join(" " + value(t, w) for (_, t), w in zip(k.ctor_params, words))),
          "    | some me =>", "      IO.println s!\"new inv=%s\"" % inv, "      " + again % "(some me)",
          "    | none =>", "      IO.println \"new %s\"" % ("pre" if k.ctor_pre else "MEMORY ERROR"), "      " + again % "me?"]
    for i, m in enumerate(k.public):
        pats = ["a%d" % j for j in range(len(m.params))]
        args = "".join(" " + value(t, "a%d" % j) for j, (_, t) in enumerate(m.params))
        r = "-" if m.result is None else "{wr r}" if isinstance(m.result, GenT) else "{r.toNat}"
        L += ["  | [%s], some me =>" % ", ".join(['"%d"' % i] + pats),
              "    match %s.%s%s%s me%s with" % (n, lean_name(m.name), k.ga, " 4294967296" if m.fuel else "", args),
              "    | some (me, %s) =>" % ("_" if m.result is None else "r"),
              "      IO.println s!\"%s %s inv=%s\"" % (m.name, r, inv), "      " + again % "(some me)",
              "    | none =>", "      IO.println \"%s %s\"" % (m.name, "pre" if m.pre else "MEMORY ERROR"), "      " + again % "(some me)"]
    L += ["  | _, none =>", "    IO.println \"no object\"", "    " + again % "none",
          "  | _, _ => IO.println \"a line the script should not have\"", "",
          "partial def all (stdin : IO.FS.Stream) (sofar : Array String) : IO (List String) := do",
          "  let line ← stdin.getLine",
          "  if line.isEmpty then return sofar.toList",
          "  all stdin (sofar.push (line.splitOn \"\\n\").head!)", "",
          "def main : IO Unit := do",
          "  let lines ← all (← IO.getStdin) #[]"]
    for tag, _, lean_t, _, bounds, rd, wr in AT:
        L += ["  IO.println \"%s\"" % tag,
              "  run %s (fun w => %s) (fun (r : %s) => %s) none lines" % (" ".join(bounds), rd, lean_t, wr)]
    return "\n".join(L) + "\n"


def emit_diff_cpp_generic(k, header):
    n, T = k.name, k.generic[0]
    pre = header.endswith(".read.hpp")
    q = "%s<%s, A, B>" % (k.qual, T)
    inv = "(int)at->invariant()" if k.inv is not None else "1"
    L = ["/* GENERATED by prover/prooc.py. %s itself, at four types, driven by the script on standard input. */" % n]
    if pre:
        L += ["#define pre(x)"]
    L += ["#define prooc_pre(x) do { if (!(x)) throw 0; } while (0)", "#define STRONG_CHECK( condition, from ) do { (void)( from ); if ( !( condition ) ) throw 0; } while ( 0 )"]
    L += ['#include "%s"' % header, "#include <cstdint>", "#include <cstdio>", "#include <cstring>", "#include <new>",
          "#include <sstream>", "#include <iostream>", "#include <string>", "#include <type_traits>", "#include <vector>", "",
          "template <typename T> static T rd(unsigned long long w) {",
          "  if constexpr (std::is_floating_point_v<T>) {",
          "    T v; if (sizeof(T) == 4) { uint32_t b = (uint32_t)w; std::memcpy(&v, &b, 4); } else { uint64_t b = w; std::memcpy(&v, &b, 8); }",
          "    return v;", "  } else return (T)w;", "}", "",
          "template <typename T> static unsigned long long wr(T r) {",
          "  if constexpr (std::is_floating_point_v<T>) {",
          "    if (sizeof(T) == 4) { uint32_t b; std::memcpy(&b, &r, 4); return b; }",
          "    uint64_t b; std::memcpy(&b, &r, 8); return b;",
          "  } else return (unsigned long long)(uint64_t)r;", "}", "",
          "template <typename %s, %s A, %s B> static void run(const char *tag, const std::vector<std::string> &lines) {" % (T, T, T),
          '  std::printf("%s\\n", tag);',
          "  alignas(%s) unsigned char store[sizeof(%s)];" % (q, q), "  %s *at = nullptr;" % q,
          "  for (const std::string &line : lines) {",
          "    std::istringstream in(line);", "    int which; in >> which;",
          '    if (!at && which != %d) { std::printf("no object\\n"); continue; }' % len(k.public)]

    def read(params, L):
        args = []
        for j, (_, t) in enumerate(params):
            L.append("      unsigned long long n%d; in >> n%d;" % (j, j))
            args.append("rd<%s>(n%d)" % (T, j) if isinstance(t, GenT) else "(%s)n%d" % (cpp_type(t), j))
        return ", ".join(args)

    for i, m in enumerate(k.public):
        L += ["    if (which == %d) {" % i, "      try {"]
        call = "at->%s(%s)" % (m.name, read(m.params, L))
        if m.result is None:
            L += ["      %s;" % call, '      std::printf("%s - inv=%%d\\n", %s);' % (m.name, inv)]
        else:
            L += ["      unsigned long long r = %s;" % ("wr<%s>(%s)" % (T, call) if isinstance(m.result, GenT) else call),
                  '      std::printf("%s %%llu inv=%%d\\n", r, %s);' % (m.name, inv)]
        L += ['      } catch (int) { std::printf("%s pre\\n"); }' % m.name, "    }"]
    L += ["    if (which == %d) {" % len(k.public), "      try {"]
    made = read(k.ctor_params, L)
    L += ["        %s made%s;" % (q, "(%s)" % made if made else ""),
          "        if (at) *at = made; else at = new (store) %s(made);" % q,
          '        std::printf("new inv=%%d\\n", %s);' % inv,
          '      } catch (int) { std::printf("new pre\\n"); }', "    }", "  }", "}", "",
          "int main() {", "  std::vector<std::string> lines;", "  std::string line;",
          "  while (std::getline(std::cin, line)) lines.push_back(line);"]
    for tag, cpp_t, _, bounds, _, _, _ in AT:
        L.append('  run<%s, %s>("%s", lines);' % (cpp_t, ", ".join(bounds), tag))
    L += ["  return 0;", "}"]
    return "\n".join(L) + "\n"


SPECIAL = [0x3ff0000000000000, 0xbff8000000000000, 0x4004000000000000, 0x4004000000000001, 0x7ff8000000000000,
           0x7ff0000000000000, 0xfff0000000000000, 0x8000000000000000, 0x3f800000, 0xbfc00000, 0x40200000, 0x40200001,
           0x7fc00000, 0x7f800000, 0xff800000, 0x80000000, 5, 4, 1000, 1001, (1 << 64) - 5, (1 << 64) - 6]


def emit_script(k, steps):
    """A seeded script of calls: half the numbers small, so that edges are met."""
    import random
    rng = random.Random(12345)

    def number(t):
        if isinstance(t, GenT):     # its bits: small, or an edge of one of the four types, or anything
            return str(rng.choice([rng.randrange(8), rng.choice(SPECIAL), rng.randrange(1 << 64)]))
        return str(rng.randrange(2) if t.is_bool else rng.randrange(8) if rng.random() < 0.5 else rng.randrange(1 << t.width))

    lines = []
    kinds = len(k.public) + (1 if k.ctor_params or k.generic else 0)
    for _ in range(steps if kinds else 0):
        i = rng.randrange(kinds)
        words = [str(i)]
        for _, t in (k.public[i].params if i < len(k.public) else k.ctor_params):
            if isinstance(t, ClassT):
                words += [number(ct) for _, ct in t.params()]
            elif isinstance(t, BytesT):
                words.append(bytes(rng.randrange(256) for _ in range(rng.randrange(48))).hex() or "-")
            else:
                words.append(number(t))
        lines.append(" ".join(words))
    return "\n".join(lines) + "\n"


def find_class(cursor, name, spaces=(), function=False):
    """Every definition of a class (or a function) of this name, with the namespaces it is in."""
    found = []
    for c in cursor.get_children():
        if c.kind == CK.NAMESPACE:
            found += find_class(c, name, spaces + (c.spelling,), function)
        elif (c.kind in (CK.CLASS_DECL, CK.CLASS_TEMPLATE, CK.FUNCTION_DECL) and c.is_definition() and c.spelling == name
              and (c.kind == CK.FUNCTION_DECL) == function):
            found.append((c, spaces))
    return found


NAMES = (CK.TYPEDEF_DECL, CK.TYPE_ALIAS_DECL, CK.TYPE_ALIAS_TEMPLATE_DECL, CK.VAR_DECL)


def needed_text(index, path, name, std, builtin):
    """A declaration that is not a class, which the class read is written with: a name for a type,
    or for a number. Its own text, as it stands in its file, in its namespaces."""
    tu = index.parse(path, args=["-x", "c++", "-std=" + std] + builtin + PRE_FLAGS, options=0x200)
    here = os.path.abspath(path)

    def find(cursor, spaces):
        found = []
        for c in cursor.get_children():
            if c.kind == CK.NAMESPACE:
                found += find(c, spaces + (c.spelling,))
            elif c.kind in NAMES and c.spelling == name and c.location.file and os.path.abspath(c.location.file.name) == here:
                found.append((c, spaces))
        return found

    found = find(tu.cursor, ())
    if len(found) != 1:
        raise Unsupported("%s: %d declarations of %s that are a name for a type or a number (one is wanted)" % (path, len(found), name))
    c, spaces = found[0]
    text = open(path, "rb").read()[c.extent.start.offset:c.extent.end.offset].decode("utf-8")
    return ["namespace %s {" % sp for sp in spaces] + [text + ";"] + ["}" for _ in spaces]


def subject_text(index, path, name, std, builtin, function=False, uses=(), needs=()):
    """A class as it stands in a file of another program: its own text, not one character changed,
    with only the standard headers a class in the subset can need before it and its namespaces
    around it. The file is parsed here only to find where the class begins and ends: it need not
    compile alone (its other includes may be missing). Everything that is owed is then read from
    this text, which must compile alone, with no error."""
    tu = index.parse(path, args=["-x", "c++", "-std=" + std] + builtin + PRE_FLAGS, options=0x200)     # keep going past errors
    here = os.path.abspath(path)
    found = [(c, sp) for c, sp in find_class(tu.cursor, name, function=function)
             if c.location.file and os.path.abspath(c.location.file.name) == here]
    if len(found) != 1:
        raise Unsupported("%s: %d definitions of a %s %s (one is wanted)" % (path, len(found), "function" if function else "class", name))
    c, spaces = found[0]
    data = open(path, "rb").read()
    text = data[c.extent.start.offset:c.extent.end.offset].decode("utf-8")
    lines = "lines %d to %d of %s" % (c.extent.start.line, c.extent.end.line, os.path.basename(path))
    out = ["/* GENERATED by prover/prooc.py: %s %s, %s, as it stands there. */" % ("function" if function else "class", name, lines)] + PRELUDE
    for upath, uname in uses:      # the classes it takes as parameters, each as it stands, before it
        utext = subject_text(index, upath, uname, std, builtin)[0]
        out += utext.split("\n")[1 + len(PRELUDE):]
    for npath, nname in needs:     # and the names it is written with, each as it stands
        out += needed_text(index, npath, nname, std, builtin)
    out += ["namespace %s {" % sp for sp in spaces]
    out += [text + ("" if function else ";")]
    out += ["}" for _ in spaces]
    return "\n".join(out) + "\n", lines, "::".join(spaces + (name,))


def file_scope(cursor, here, spaces_allowed):
    """The classes at file scope of the file `here`; anything else beside them is refused."""
    classes = []
    for c in cursor.get_children():
        if not c.location.file or os.path.abspath(c.location.file.name) != here:
            continue
        if c.kind == CK.CLASS_TEMPLATE and c.spelling in ("subarray", "subarray_checked") and c.semantic_parent.spelling == "Strong":
            continue        # the window on an array (PRELUDE): the byte view, not a class read here
        if c.kind in (CK.CLASS_DECL, CK.CLASS_TEMPLATE) and c.is_definition():
            classes.append(c)
        elif c.kind == CK.FUNCTION_DECL and c.is_definition() and spaces_allowed == "function":
            classes.append(c)
        elif c.kind == CK.INCLUSION_DIRECTIVE:
            continue
        elif c.kind == CK.STRUCT_DECL and c.spelling == "caller" and c.semantic_parent.spelling == "Strong":
            continue        # who called (PRELUDE): not modelled
        elif c.kind in NAMES and (c.kind != CK.VAR_DECL or (c.type.is_const_qualified() and outer_constant(c) is not None)):
            continue        # a name for a type, or for a number a literal gives: no state
        elif c.kind == CK.NAMESPACE and spaces_allowed:
            classes += file_scope(c, here, spaces_allowed)
        else:
            refuse(c, "%s at file scope: a model is one class and nothing beside it (a global is "
                      "state outside the class)" % c.kind.name.lower().replace("_", " "))
    return classes


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
