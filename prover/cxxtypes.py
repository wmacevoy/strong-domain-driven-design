"""What the modules of the prover share: the refusal, the names Lean is written with, the
types a C++ class's numbers, views and parameters are read as, and the small helpers that read a
cursor.  Three pieces of state are kept here, as they were: USED, OPTIONS and READ.
"""

import re

from clang.cindex import CursorKind as CK, TypeKind as TK

from clang_edge import where, Unsupported, operator_of   # noqa: E402


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


READ = {"text": b""}     # the text being read, as bytes: what a cursor's place is a place in


def is_caller(t):
    return t.get_canonical().spelling in ("Strong::caller", "const Strong::caller")


def subarray_of(t):
    """The type as it is said in full, for a Strong::subarray of unsigned bytes that are not written; or None."""
    m = re.match(r"(?:const )?(Strong::subarray<const unsigned char \*>)$", t.get_canonical().spelling)
    return m.group(1) if m else None


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
        text = operator_of(cursor)
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


def binders(m):
    return "".join(" (%s : %s)" % (lean_name(n), t.lean()) for n, t in m.params)


def result_type(m):
    return "Unit" if m.result is None else m.result.lean()


def qual_of(cursor):
    """A class's name with its namespaces."""
    names, c = [cursor.spelling], cursor.semantic_parent
    while c is not None and c.kind == CK.NAMESPACE:
        names.insert(0, c.spelling)
        c = c.semantic_parent
    return "::".join(names)
