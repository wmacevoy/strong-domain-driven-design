"""The reader: Clang's cursors in, the tree of cxx.py out. Every question asked of Clang, and every
refusal, is here (and in subject.py and clang_edge.py); nothing here knows how Lean is written.

It reads in the order the generator always has, statement by statement in the order of the text,
so that of a class with several faults, the first refused is the one it always was.
"""

import clang.cindex as ci
from clang.cindex import CursorKind as CK, TypeKind as TK

import re

import cxx
from clang_edge import where, Unsupported, operator_of
from cxxtypes import OPTIONS, OWN, READ, USED, BytesT, ClassT, GenT, Int
from cxx import (Byte, Call, Cmp, Compl, Conv, Div, Elem, Lit, LNot, Logic, Name, NonZero,
                 OtherCall, Made, FieldDo, Paren, Bin, SignedBin, Shift, Size, Truth, Value,
                 Block, Break, CallStmt, Compound, Continue, Decl, ForLoop, Ite, Fill, Memcpy, Memset, ObjDecl, OutCall, OutDo, Ret,
                 Seq, Set, Skip, Step, Sub, Throw, End, ViewDecl, WhileLoop)


UNSIGNED = {TK.UCHAR: 8, TK.USHORT: 16, TK.UINT: 32, TK.ULONG: 64, TK.ULONGLONG: 64, TK.BOOL: 8}
SIGNED = {TK.INT: 32}


def refuse(cursor, why):
    raise Unsupported("%s: %s" % (where(cursor), why))


def named(name):
    """A name the model will be written with: refused if it is one of the model's own. Asked where
    the generator, when it wrote as it read, first wrote the name, so that the same name is refused
    first."""
    if name in OWN:
        raise Unsupported("the name '%s' is the model's own: choose another." % name)
    return name


def int_of(t, cursor):
    """An integer type the model knows exactly, as Int; refused if it is not one."""
    k = t.get_canonical().kind
    if k in UNSIGNED:
        return Int(UNSIGNED[k], False, k == TK.BOOL)
    if k in SIGNED:
        return Int(SIGNED[k], True)
    refuse(cursor, "the type '%s' is not one the model knows exactly (the unsigned "
                   "integers of 8 to 64 bits; int only where a literal or a promotion makes one)."
           % t.spelling)


def is_gen(k, t):
    g = getattr(k, "generic", None)
    return bool(g) and t.spelling.replace("const ", "").strip() == g[0]


def typ(k, t, cursor):
    return GenT() if is_gen(k, t) else int_of(t, cursor)


def not_checked(cursor, method_name, used_name):
    """A proved class is called by proved classes, which are proved to call it rightly: it has no
    use for a test when the program runs. So only a way in for code that is not proved, a method
    named `..._checked`, may take, make or call anything `_checked`."""
    if "_checked" in used_name and not method_name.endswith("_checked"):
        refuse(cursor, "'%s' in '%s', which is not a `_checked` way in: what is proved is called by what is "
                       "proved, and tests nothing when the program runs" % (used_name, method_name))


def is_caller(t):
    return t.get_canonical().spelling in ("Strong::caller", "const Strong::caller")


def subarray_of(t):
    """The type as it is said in full, for a Strong::subarray of unsigned bytes that are not written; or None.
    What it says they are (its second argument) is not read: every window is the one byte view."""
    m = re.match(r"(?:const )?(Strong::subarray<const unsigned char \*(?:, [\w:<>, ]+)?>)$", t.get_canonical().spelling)
    return m.group(1) if m else None


def fixed_of(t):
    """(the type as it is said in full, N) for a Strong::fixed<N, of>, a window of N bytes; or None.
    What it says they are is not read, as of a subarray."""
    m = re.match(r"(?:const )?(Strong::fixed<(\d+)[UL]*(?:, [\w:<>, ]+)?>)$", t.get_canonical().spelling)
    return (m.group(1), int(m.group(2))) if m else None


def is_bytes(t):
    return t.get_canonical().spelling in ("Bytes", "const Bytes") or subarray_of(t) is not None or fixed_of(t) is not None


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
    it = int_of(v.type, v)
    return None if lit is None or it.signed else lit % (1 << it.width)


def unparen(c):
    while c.kind in (CK.UNEXPOSED_EXPR, CK.PAREN_EXPR) and len(list(c.get_children())) == 1:
        c = list(c.get_children())[0]
    return c


def first_token(cursor):
    for t in cursor.get_tokens():
        return t.spelling
    refuse(cursor, "an expression with no text of its own (is it in a macro?)")


def words(body):
    """The words of a body, as the compiler's tokenizer gives them, its comments left out."""
    return [t.spelling for t in body.get_tokens() if t.kind != ci.TokenKind.COMMENT]


def qual_of(cursor):
    """A class's name with its namespaces."""
    names, c = [cursor.spelling], cursor.semantic_parent
    while c is not None and c.kind == CK.NAMESPACE:
        names.insert(0, c.spelling)
        c = c.semantic_parent
    return "::".join(names)


class BodyReader:
    """A method's body, the constructor's, or the invariant, read into the tree."""

    def __init__(self, klass, kc, ready, in_ctor=False, method=None, plain=False):
        self.k = klass
        self.kc = kc                # the class's cursor, or None for a function
        self.ready = ready          # the methods read before this one, by name: what a call may name
        self.in_ctor = in_ctor
        self.plain = plain          # the invariant or a precondition: a condition on the fields, which cannot fail
        self.m = method
        self.assigned = set()       # constructor only: fields, and (field, index) for array elements
        self.scope = [n for n, _ in method.params] if method else []     # the names a loop would carry
        self.loops = []             # the loops we are inside: the increment's cursor, or None
        self.count = 0              # the loops read
        self.in_block = 0           # inside a branch the model writes as a function of its own
        self.calls_fuel = False     # it calls a method that has a loop
        self.objects = {n: t for n, t in method.params if isinstance(t, ClassT)} if method else {}
        self.outcalls = 0           # calls of a function outside the program read in this method
        self.views = {n: n for n, t in method.params if isinstance(t, BytesT) and t.length and t.readable} if method else {}
        self.raw = {n for n, t in method.params if isinstance(t, BytesT) and t.length} if method else set()
        self.fixed = {n: t.fixed for n, t in method.params if isinstance(t, BytesT) and t.fixed} if method else {}

    # ---- expressions

    def own_field(self, c):
        ref = c.referenced
        if ref is None or ref.kind != CK.FIELD_DECL or ref.spelling not in self.k.field:
            refuse(c, "a member that is not a field of this class")
        for child in c.get_children():
            if child.kind != CK.CXX_THIS_EXPR:
                refuse(c, "a field reached through something other than this object")
        f = self.k.field[ref.spelling]
        if isinstance(f.type, ClassT):
            refuse(c, "the part '%s' used but by calling a method of it: a part is never copied, "
                      "assigned or handed on, so it is changed by its own methods and nothing else" % f.name)
        return f

    def array_place(self, c):
        """Elem, for an ARRAY_SUBSCRIPT_EXPR on one of the class's own arrays."""
        base, index = list(c.get_children())
        while base.kind in (CK.UNEXPOSED_EXPR, CK.PAREN_EXPR):
            base = list(base.get_children())[0]
        if base.kind != CK.MEMBER_REF_EXPR:
            refuse(c, "an index into something that is not an array field of this class")
        f = self.own_field(base)
        if f.count is None:
            refuse(c, "an index into a field that is not an array")
        it = int_of(index.type, index)
        i = self.expr(index)
        if it.signed:
            lit = self.literal(index)
            if lit is None:
                refuse(index, "an index of a signed type (it could be negative): use an unsigned one")
            return Elem(f.name, i, lit, place=where(c))
        return Elem(f.name, i, None, place=where(c))

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
        if ref is not None and ref.kind == CK.VAR_DECL and (self.kc is not None and ref.semantic_parent == self.kc):
            return self.k.constants.get(ref.spelling)
        if ref is not None and ref.kind == CK.VAR_DECL and ref.semantic_parent.spelling in self.k.uses:
            return self.k.uses[ref.semantic_parent.spelling].constants.get(ref.spelling)     # U::NAME, of a class it takes
        if (ref is not None and ref.kind == CK.VAR_DECL and ref.semantic_parent.kind in (CK.NAMESPACE, CK.TRANSLATION_UNIT)
                and ref.type.is_const_qualified()):
            return outer_constant(ref)       # a name for a number, beside the classes
        return None

    def own_call(self, c):
        """Call, if a CALL_EXPR calls a method of this class on this object; else None."""
        parts = list(c.get_children())
        if not parts or parts[0].kind != CK.MEMBER_REF_EXPR:
            return None
        ref = parts[0].referenced
        if ref is None or ref.kind != CK.CXX_METHOD or (self.kc is None or ref.semantic_parent != self.kc):
            return None
        if any(x.kind != CK.CXX_THIS_EXPR for x in parts[0].get_children()):
            refuse(c, "a method called on something other than this object")
        if self.in_ctor or self.plain:
            refuse(c, "a call in the constructor or the invariant")
        not_checked(c, self.m.name if self.m else "the constructor", ref.spelling)
        m = self.ready.get(ref.spelling)
        if m is None:
            refuse(c, "a call to '%s', which is not written before this method (or is this method): "
                      "the model of a call is the model of what is called" % ref.spelling)
        if m.throws or m.ends:
            refuse(c, "a call of '%s', which may throw or end the process: what its caller does then is not read yet" % m.name)
        args = parts[1:]
        if len(args) != len(m.params):
            refuse(c, "a call with a default argument")
        given = []
        for a, (_, t) in zip(args, m.params):
            if isinstance(t, ClassT):
                o = unparen(a)
                while o.kind == CK.CALL_EXPR and len(list(o.get_children())) == 1:     # the copy C++ makes of it
                    o = unparen(list(o.get_children())[0])
                if o.kind != CK.DECL_REF_EXPR or not t.same(self.objects.get(o.spelling)):
                    refuse(a, "an argument of a class's type that is not the name of a value of that class")
                given.append(Name(named(o.spelling), "object", place=where(o)))
                continue
            if isinstance(t, BytesT) or int_of(a.type, a).width != t.width:
                refuse(a, "an argument that is not the parameter's own type")
            given.append(self.expr(a))
        if m.fuel:
            self.calls_fuel = True
        named(m.name)
        return Call(m, given, place=where(c))

    def view_of(self, c):
        """The view a pointer's name stands for (a parameter, or a local made from one), or None."""
        c = unparen(c)
        if c.kind == CK.DECL_REF_EXPR and c.referenced is not None and c.referenced.kind in (CK.PARM_DECL, CK.VAR_DECL):
            return self.views.get(c.spelling)
        return None

    def other_call(self, c):
        """OtherCall, for a call to a const method of a parameter that is another class; or None."""
        parts = list(c.get_children())
        if not parts or parts[0].kind != CK.MEMBER_REF_EXPR:
            return None
        part = self.part_of(parts[0])
        if part is not None:
            if self.in_ctor or (self.plain and self.m is not None):
                refuse(c, "a call on a part in the constructor or a precondition")
            ct = part.type
        else:
            base = [unparen(x) for x in parts[0].get_children()]
            if len(base) != 1 or base[0].kind != CK.DECL_REF_EXPR or base[0].spelling not in self.objects:
                return None
            ct = self.objects[base[0].spelling]
        k = ct.k
        ref = parts[0].referenced
        m = ready_of(k).get(ref.spelling) if ref is not None and ref.kind == CK.CXX_METHOD else None
        if m is None or not m.const or not m.public or m.result is None or len(parts) - 1 != len(m.params):
            refuse(c, "a call on a %s that is not to a public const method of its class that gives a number"
                      % ("part" if part is not None else "parameter") + (" (one that changes the part is a statement "
                      "of its own)" if part is not None and m is not None and not m.const else ""))
        given = []
        for a, (_, t) in zip(parts[1:], m.params):
            t = ct.of(t)
            if not isinstance(t, Int) or int_of(a.type, a).width != t.width:
                refuse(a, "an argument that is not the parameter's own type")
            given.append(self.expr(a))
        if m.fuel:
            self.calls_fuel = True
        named(m.name)
        if part is not None:
            return OtherCall(named(part.name), ct, m, given, field=True, place=where(c))
        return OtherCall(named(base[0].spelling), ct, m, given, place=where(c))

    def part_of(self, callee):
        """The field a method is called on, if it is a part: a field of this class that is a value
        of another class, reached through this object; or None."""
        base = [unparen(x) for x in callee.get_children()]
        if len(base) != 1 or base[0].kind != CK.MEMBER_REF_EXPR:
            return None
        ref = base[0].referenced
        if ref is None or ref.kind != CK.FIELD_DECL or ref.spelling not in self.k.field:
            return None
        if any(x.kind != CK.CXX_THIS_EXPR for x in base[0].get_children()):
            refuse(callee, "a part reached through something other than this object")
        f = self.k.field[ref.spelling]
        return f if isinstance(f.type, ClassT) else None

    def part_do(self, c):
        """FieldDo, if a CALL_EXPR calls a method that is not const of a part; else None."""
        parts = list(c.get_children())
        if not parts or parts[0].kind != CK.MEMBER_REF_EXPR:
            return None
        part = self.part_of(parts[0])
        ref = parts[0].referenced
        if part is None or ref is None or ref.kind != CK.CXX_METHOD:
            return None
        m = ready_of(part.type.k).get(ref.spelling)
        if m is None or m.const:
            return None         # a const one is read as an expression (other_call), and refused as a statement there
        if self.in_ctor or self.plain:
            refuse(c, "a call on a part in the constructor, the invariant or a precondition")
        if not m.public or len(parts) - 1 != len(m.params):
            refuse(c, "a call on a part that is not to a public method of its class, with every argument")
        not_checked(c, self.m.name, m.name)
        given = []
        for a, (_, t) in zip(parts[1:], m.params):
            t = part.type.of(t)
            if not isinstance(t, Int) or int_of(a.type, a).width != t.width:
                refuse(a, "an argument that is not the parameter's own type (a part's method is handed numbers)")
            given.append(self.expr(a))
        if m.fuel:
            self.calls_fuel = True
        named(m.name)
        return FieldDo(named(part.name), part.type, m, given, place=where(c))

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
            what = {CK.TEMPLATE_NON_TYPE_PARAMETER: "generic", CK.PARM_DECL: "param", CK.VAR_DECL: "local"}[g.referenced.kind]
            return Name(named(g.spelling), what, place=where(g))
        if g.kind == CK.MEMBER_REF_EXPR:
            f = self.own_field(g)
            if self.in_ctor:
                refuse(g, "the constructor reads a field")
            return Name(named(f.name), "field", place=where(g))
        refuse(g, "of a class template's type %s, only a name for a value: nothing is known of the "
                  "type but that two of it compare by `<=`" % self.k.generic[0])

    def expr(self, c):
        """An integer expression: a number of c.type's width."""
        k = c.kind
        at = where(c)
        if self.of_t(c):
            return self.gexpr(unparen(c))
        if c.type.get_canonical().kind in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE):
            refuse(c, "a pointer or a reference: the state could leave the class by it")
        if k == CK.INTEGER_LITERAL:
            t = int_of(c.type, c)
            return Lit(self.literal(c), t.width, written=first_token(c), place=at)
        if k == CK.PAREN_EXPR:
            return Paren(self.expr(list(c.get_children())[0]), place=at)
        if k in (CK.UNEXPOSED_EXPR, CK.CSTYLE_CAST_EXPR, CK.CXX_STATIC_CAST_EXPR, CK.CXX_FUNCTIONAL_CAST_EXPR):
            inner = [x for x in c.get_children() if x.kind != CK.TYPE_REF]
            if len(inner) != 1:
                refuse(c, "an expression the generator does not know")
            dst = int_of(c.type, c)
            lit = self.literal(inner[0])
            if lit is not None and dst.is_bool:
                return Lit(1 if lit else 0, 8, place=at)
            if lit is not None and k == CK.UNEXPOSED_EXPR and inner[0].kind == CK.INTEGER_LITERAL:
                return Lit(lit % (1 << dst.width), dst.width, written=first_token(inner[0]), converted=dst, place=at)
            if lit is not None:
                return Lit(lit % (1 << dst.width), dst.width, place=at)     # a literal, converted here
            e = self.expr(inner[0])
            return Conv(int_of(inner[0].type, inner[0]), dst, e, cast=k != CK.UNEXPOSED_EXPR,
                        same=c.type.get_canonical() == inner[0].type.get_canonical(), place=at)
        if k == CK.CXX_BOOL_LITERAL_EXPR:
            return Truth(first_token(c) == "true", place=at)
        if k == CK.CALL_EXPR:
            out = self.outside_call(c)      # a function outside the program: its answer, by its contract
            if out is not None:
                return out
        if self.buffer_call(c, 1) is not None:     # a buffer's length: the number it was made of
            f = self.buffer_call(c, 1)
            return Lit(f.count, int_of(c.type, c).width, place=at)
        if k == CK.DECL_REF_EXPR and self.constant(c) is not None:
            return Lit(self.constant(c), int_of(c.type, c).width, place=at)
        if (k == CK.DECL_REF_EXPR and self.m is not None and c.spelling in self.m.lengths
                and c.referenced is not None and c.referenced.kind == CK.PARM_DECL):
            return Size(named(self.m.lengths[c.spelling]), place=at)     # a view's length, by its name
        if k == CK.DECL_REF_EXPR:
            ref = c.referenced
            if ref is None or ref.kind not in (CK.VAR_DECL, CK.PARM_DECL) or ref.semantic_parent.kind == CK.TRANSLATION_UNIT:
                refuse(c, "a name that is not a local or a parameter (a global is state outside the class)")
            int_of(c.type, c)
            return Name(named(c.spelling), "param" if ref.kind == CK.PARM_DECL else "local", place=at)
        if k == CK.MEMBER_REF_EXPR:
            f = self.own_field(c)
            if f.count is not None:
                refuse(c, "an array used whole: only its elements are read")
            if self.in_ctor:
                refuse(c, "a field read in the constructor (it may not have a value yet)")
            return Name(named(f.name), "field", place=at)
        if k == CK.ARRAY_SUBSCRIPT_EXPR and unparen(list(c.get_children())[0]).kind == CK.DECL_REF_EXPR:
            base, index = list(c.get_children())
            view = self.view_of(base)
            if view is None:
                refuse(c, "an index into a pointer that is not a view of const unsigned bytes (a parameter "
                          "with its length after it, or a `const unsigned char*` local made from one)")
            if int_of(index.type, index).signed:
                lit = self.literal(index)
                if lit is None or lit < 0:
                    refuse(index, "an index of a signed type (it could be negative): use an unsigned one")
                return Byte(named(view), None, lit, place=at)
            named(view)
            return Byte(view, self.expr(index), None, place=at)
        if k == CK.ARRAY_SUBSCRIPT_EXPR:
            if self.in_ctor:
                refuse(c, "an element read in the constructor (it may not have a value yet)")
            e = self.array_place(c)
            if self.plain:
                if e.lit is None or e.lit >= self.k.field[e.field].count:
                    refuse(c, "the invariant names an element by a number inside the array")
            named(e.field)
            return e
        if k == CK.CALL_EXPR and self.other_call(c) is not None:
            return self.other_call(c)
        if k == CK.CALL_EXPR and self.own_call(c) is not None:
            call = self.own_call(c)
            if not call.method.const or call.method.result is None:
                refuse(c, "a call inside an expression to a method that is not const, or gives nothing: "
                          "make the call a statement of its own")
            return call
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
            name = named(view[0].spelling)
            if callee.spelling == "size":
                if len(parts) != 1 or int_of(c.type, c).width != 64:
                    refuse(c, "size() takes nothing and gives 64 bits")
                if name in self.fixed:      # its length is its type
                    return Lit(self.fixed[name], 64, place=at)
                return Size(name, place=at)
            if len(parts) != 2:
                refuse(c, "at() takes one unsigned index")
            lit = self.literal(parts[1])
            if name in self.fixed:
                if lit is None or lit < 0 or lit >= self.fixed[name]:
                    refuse(c, "at() of a fixed window of %d bytes, at an index that is not written out below %d"
                              % (self.fixed[name], self.fixed[name]))
                return Byte(name, None, lit, whole=True, place=at)
            if lit is not None and lit >= 0:       # as `p[4]` is read
                return Byte(name, None, lit, place=at)
            if int_of(parts[1].type, parts[1]).signed:
                refuse(c, "at() takes one unsigned index")
            return Byte(name, self.expr(parts[1]), None, place=at)
        if k == CK.BINARY_OPERATOR:
            a, b = list(c.get_children())
            op = tokens_after(c, a)
            if op in ("<", "<=", ">", ">=", "==", "!=", "&&", "||"):
                return Value(self.cond(c), place=at)
            t = int_of(c.type, c)
            if op in ("/", "%"):
                if t.signed or int_of(a.type, a).width != t.width or int_of(b.type, b).width != t.width:
                    refuse(c, "'%s' on signed numbers, or on two different types" % op)
                by = self.literal(b)
                if by is not None and by % (1 << t.width) != 0:
                    x = self.expr(a)
                    return Div(op, x, self.expr(b), True, place=at)
                # By a number known only when it runs: undefined at zero, so owed never to be.
                if self.plain or by is not None:
                    refuse(c, "a division by zero, or in the invariant by a number that is not a literal")
                x = self.expr(a)
                return Div(op, x, self.expr(b), False, place=at)
            if op in ("<<", ">>"):
                amount = self.literal(b)
                if t.signed or (amount is not None and not 0 <= amount < t.width):
                    refuse(c, "a shift of a signed number, or by a literal that is not below the width: "
                              "either can be undefined")
                if amount is not None:
                    return Shift(op, self.expr(a), None, amount, place=at)
                # By an amount known only when it runs: undefined at the width or more, so it is an
                # error of the same standing as a read outside an array, and owed never to happen.
                if int_of(b.type, b).signed:
                    refuse(c, "a shift by a signed amount (it could be negative, which is undefined): "
                              "use an unsigned one of 32 bits or more")
                if self.plain:
                    refuse(c, "a shift in the invariant by an amount that is not a literal")
                x = self.expr(a)
                return Shift(op, x, self.expr(b), None, place=at)
            if op in ("&", "|", "^"):
                x = self.expr(a)
                return Bin(op, x, self.expr(b), place=at)
            if op in ("+", "-") and t.signed and t.width >= 32 and all(signed_as_written(x) for x in (a, b)):
                # Two signed numbers as the C++ has them (not unsigned ones promoted): undefined
                # where it overflows, and so owed never to.
                x = self.expr(a)
                return SignedBin(op, x, self.expr(b), place=at)
            if op in ("+", "-", "*"):
                if t.signed:
                    refuse(c, "'%s' on signed numbers can overflow, which is undefined: make them unsigned, "
                              "or (+ and -) both of a signed type of 32 bits or more as written" % op)
                x = self.expr(a)
                return Bin(op, x, self.expr(b), place=at)
            refuse(c, "the operator '%s' here (the spike knows + - * & | ^ and comparisons)" % op)
        if k == CK.UNARY_OPERATOR:
            op = first_token(c)
            if op == "!":
                return Value(self.cond(c), place=at)
            if op == "~":
                return Compl(self.expr(list(c.get_children())[0]), place=at)
            refuse(c, "the operator '%s' (an address or a dereference would let state out; ++ and -- "
                      "are written as assignments)" % op)
        if k == CK.CXX_THIS_EXPR:
            refuse(c, "`this` as a value: the object could be handed to something else")
        refuse(c, "%s (not in the spike's subset)" % k.name.lower().replace("_", " "))

    def cond(self, c):
        """A condition. (The model keeps C++'s order in it: the right side of && or || is not read
        when the left decides.)"""
        k = c.kind
        at = where(c)
        if k == CK.PAREN_EXPR:
            node = self.cond(list(c.get_children())[0])
            node.parens += 1
            return node
        if k == CK.CXX_BOOL_LITERAL_EXPR:
            return Truth(first_token(c) == "true", place=at)
        if (k == CK.UNEXPOSED_EXPR and getattr(self.k, "generic", None) and len(list(c.get_children())) == 1
                and c.type.get_canonical().kind in (TK.INVALID, TK.DEPENDENT)):
            return self.cond(list(c.get_children())[0])      # in a class template: the parentheses of an initializer
        if k == CK.UNEXPOSED_EXPR and c.type.get_canonical().kind == TK.BOOL:
            inner = list(c.get_children())[0]
            if inner.type.get_canonical().kind == TK.BOOL:
                return self.cond(inner)
            e = self.expr(inner)
            return NonZero(e, int_of(inner.type, inner).width, place=at)
        if k == CK.UNARY_OPERATOR and first_token(c) == "!":
            return LNot(self.cond(list(c.get_children())[0]), place=at)
        if k == CK.BINARY_OPERATOR:
            a, b = list(c.get_children())
            op = tokens_after(c, a)
            if op in ("&&", "||"):
                x = self.cond(a)
                return Logic(op, x, self.cond(b), place=at)
            if op in ("<", "<=", ">", ">=", "==", "!=") and (self.of_t(a) or self.of_t(b)):
                if op != "<=" or not (self.of_t(a) and self.of_t(b)):
                    refuse(c, "two values of a class template's type are compared by `<=`, and no other way")
                x = self.expr(a)
                return Cmp("<=", x, self.expr(b), False, place=at)
            if op in ("<", "<=", ">", ">=", "==", "!="):
                ta, tb = int_of(a.type, a), int_of(b.type, b)
                if (ta.width, ta.signed) != (tb.width, tb.signed):
                    refuse(c, "a comparison of two different types")
                x = self.expr(a)
                return Cmp(op, x, self.expr(b), ta.signed, place=at)
        if c.type.get_canonical().kind == TK.BOOL and k in (CK.DECL_REF_EXPR, CK.MEMBER_REF_EXPR, CK.CALL_EXPR):
            return NonZero(self.expr(c), 8, place=at)
        refuse(c, "a condition the generator does not know (comparisons, !, && and ||)")

    # ---- statements

    def declare(self, cursor, name):
        if name in self.scope:
            refuse(cursor, "the name '%s' is declared twice in one method: give the inner one its own name" % name)
        self.scope.append(name)

    def function_names(self, cursors):
        """The names the model writes a loop's or a branch's own function with, asked in the order
        it first writes them: what it changes of what is in scope, the method's name, everything in
        scope."""
        changed = assigned_names(cursors)
        for n in self.scope:
            if n in changed:
                named(n)
        named(self.m.name)
        for n in self.scope:
            named(n)

    def outlined(self, c):
        """Whether the model writes a branch as a function of its own (model.Writer.outlined says
        the same of the tree): more than one statement, and no way out of it but its end. Asked here
        because a value of another class is not made inside one, and of the names that function is
        written with, a name of the model's own is refused before what is inside it."""
        if self.in_ctor or getattr(self.k, "generic", None) or c.kind != CK.COMPOUND_STMT or len(list(c.get_children())) < 2:
            return False
        return not any(x.kind in (CK.BREAK_STMT, CK.CONTINUE_STMT, CK.RETURN_STMT) for x in c.walk_preorder())

    def branch(self, c):
        mark = len(self.scope)
        if self.outlined(c):
            self.function_names([c])
            loops, self.loops = self.loops, []
            self.in_block += 1
            node = self.stmt(c)
            self.in_block -= 1
            self.loops = loops
        else:
            node = self.stmt(c)
        del self.scope[mark:]
        return node

    def loop(self, c, init, cond, inc, body):
        mark = len(self.scope)
        first = self.stmt(init) if init is not None else None
        carried = len(self.scope)
        self.function_names([cond, body, inc])
        self.count += 1
        test = self.cond(cond)
        self.loops.append(inc)
        inside = self.stmt(body)
        del self.scope[carried:]
        step = self.stmt(inc) if inc is not None else None
        self.loops.pop()
        del self.scope[mark:]
        if c.kind == CK.FOR_STMT:
            return ForLoop(first, test, step, inside, place=where(c))
        return WhileLoop(test, inside, place=where(c))

    def stmt(self, c):
        k = c.kind
        at = where(c)
        if k == CK.COMPOUND_STMT:
            stmts, inner = [], list(c.get_children())
            for i, s in enumerate(inner):
                # A call of the system's, of literals alone, just before the process ends: it says
                # why (`fprintf( stderr, "..." ); exit( 1 );`). It reads nothing of the program's,
                # and nothing after it is looked at: what it writes is trusted to be its own.
                if (system_call(unparen(s)) is not None and plain_arguments(unparen(s)) and i + 1 < len(inner)
                        and is_end(inner[i + 1]) and not self.in_ctor):
                    stmts.append(Skip(place=where(s)))
                    continue
                stmts.append(self.stmt(s))
            return Block(stmts, place=at)
        if self.m is not None and not self.in_ctor and assert_of(c) is not None:
            return End(self.cond(assert_of(c)), "assert", place=at)
        if self.m is not None and not self.in_ctor and is_end(c):
            if not plain_arguments(unparen(c)):
                refuse(c, "an end of the process given more than literals")
            return End(None, system_call(unparen(c)), place=at)
        if k == CK.CALL_EXPR and c.spelling == "__builtin_assume":
            return Skip(place=at)       # a pre( condition ), written here by with_pre: it is the method's pre
        if self.in_ctor and not (k == CK.BINARY_OPERATOR or is_throw(c) or guard_of(c) is not None
                                 or (k == CK.CALL_EXPR and c.spelling in ("memset", "memcpy"))):
            refuse(c, "the constructor may assign its fields, copy or set bytes into them, and test what it is "
                      "given and throw (`if ( c ) throw ...;`): nothing else")
        if k == CK.UNARY_OPERATOR and step_of(c) is not None:      # x++ or --x, its value not used
            lhs = list(c.get_children())[0]
            t = int_of(lhs.type, lhs)
            if t.signed:
                refuse(c, "++ or -- of a signed number")
            self.expr(lhs)
            return Step(step_of(c) * 2, self.assign(lhs), t.width, place=at)
        if k == CK.COMPOUND_ASSIGNMENT_OPERATOR:
            lhs, rhs = list(c.get_children())
            op = tokens_after(c, lhs)
            t, tr = int_of(lhs.type, lhs), int_of(rhs.type, rhs)
            if op not in ("+=", "-=", "*=", "&=", "|=", "^=") or t.signed or t.width < 32 or (tr.width, tr.signed) != (t.width, False):
                refuse(c, "'%s' here: the two sides are one unsigned type of 32 bits or more, and the "
                          "operator is one of + - * & | ^" % op)
            self.expr(lhs)
            value = self.expr(rhs)
            return Compound(op, self.assign(lhs), value, place=at)
        if k == CK.CALL_EXPR and c.spelling == "memset":
            return self.memset(c)
        if k == CK.CALL_EXPR and c.spelling == "memcpy":
            return self.memcpy(c)
        if k == CK.CALL_EXPR:
            out = self.outside_call(c)
            if out is not None:
                return OutDo(out, place=at)
        if k == CK.CALL_EXPR and self.own_call(c) is not None:
            return CallStmt(self.own_call(c), place=at)
        if k == CK.CALL_EXPR and self.part_do(c) is not None:
            return self.part_do(c)
        if k == CK.NULL_STMT:
            return Skip(place=at)
        if k == CK.DECL_STMT:
            decls = []
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
                    decls.append(ViewDecl(v.spelling, src.spelling, place=where(v)))
                    continue
                if vt.kind == TK.RECORD:
                    # A value of another class, made by its constructor: `U name( arguments );`. What that
                    # constructor expects of its caller is owed here: its model is `none` where it is not so.
                    u = used_class(v, vt)
                    init = [x for x in init if x.kind != CK.TEMPLATE_REF]
                    made = unparen(init[0]) if len(init) == 1 else None
                    given = list(made.get_children()) if made is not None and made.kind == CK.CALL_EXPR else None
                    by = chosen(u, made, v) if given is not None else None
                    wanted = by and sum(2 if isinstance(t, BytesT) and t.length else 1 for _, t in by.params)
                    if given is None or len(given) != wanted or self.loops or self.in_block:
                        refuse(v, "a local of a class's type that is not made by its constructor, `%s %s( ... );`, "
                                  "outside any loop" % (u.k.name, v.spelling))
                    args = []
                    for _, t in u.params(by):
                        a = given.pop(0)
                        if isinstance(t, BytesT):
                            args.append(self.sub_view(a, given.pop(0), t))
                            continue
                        if int_of(a.type, a).width != t.width:
                            refuse(a, "an argument that is not the parameter's own type")
                        args.append(self.expr(a))
                    self.objects[v.spelling] = u
                    decls.append(ObjDecl(named(v.spelling), u, args, ctor=by, place=where(v)))
                    continue
                if len(init) != 1:
                    refuse(v, "the local '%s' has no first value: it would begin as anything" % v.spelling)
                t = typ(self.k, v.type, v)
                value = self.expr(init[0])
                self.declare(v, v.spelling)
                decls.append(Decl(named(v.spelling), t, value, word=next((w.spelling for w in v.get_tokens()), ""), place=where(v)))
            return decls[0] if len(decls) == 1 else Seq(decls, place=at)
        if k == CK.IF_STMT:
            parts = list(c.get_children())
            test = self.cond(parts[0])
            then = self.branch(parts[1])
            return Ite(test, then, self.branch(parts[2]) if len(parts) > 2 else None, place=at)
        if k == CK.RETURN_STMT:
            value = list(c.get_children())
            called = unparen(value[0]) if value else None
            if called is not None and called.kind == CK.CALL_EXPR and self.own_call(called) is not None:
                call = self.own_call(called)     # `return method( ... );`: its state, then its answer
                if call.method.result is None:
                    refuse(c, "the return of a call that gives nothing")
                return Ret(call, place=at)
            return Ret(self.expr(value[0]) if value else None, place=at)
        if k in (CK.WHILE_STMT, CK.FOR_STMT) and getattr(self.k, "generic", None):
            refuse(c, "a loop in a class template")
        if k == CK.WHILE_STMT:
            cond, body = list(c.get_children())
            return self.loop(c, None, cond, None, body)
        if k == CK.FOR_STMT:
            parts = list(c.get_children())
            if len(parts) != 4:
                refuse(c, "a for with a part left out: write all three, or a while")
            return self.loop(c, parts[0], parts[1], parts[2], parts[3])
        if k == CK.BREAK_STMT and self.loops:
            return Break(place=at)
        if k == CK.CONTINUE_STMT and self.loops:
            if self.loops[-1] is not None:
                self.stmt(self.loops[-1])       # read again where the model writes it again: before the round goes on
            return Continue(place=at)
        if k == CK.UNEXPOSED_EXPR and [x.kind for x in c.get_children()] == [CK.CXX_THROW_EXPR]:
            c, k = next(c.get_children()), CK.CXX_THROW_EXPR      # the temporaries the throw makes, cleaned up after
        if k == CK.CXX_THROW_EXPR:
            # What is thrown is not read: so it may say nothing of the state, and is made of
            # literals alone. What its constructor does is trusted (it commits no memory error).
            thrown = list(c.get_children())
            if len(thrown) != 1 or thrown[0].type.get_canonical().kind != TK.RECORD:
                refuse(c, "a throw that is not of a value of a class (a rethrow, or of a number)")
            for x in thrown[0].walk_preorder():
                if x.kind == CK.CXX_THIS_EXPR or (x.referenced is not None and x.referenced.kind in (CK.PARM_DECL, CK.VAR_DECL, CK.FIELD_DECL)):
                    refuse(x, "a thrown value made of more than literals: what it says is not read, so it "
                              "may not depend on the state")
            return Throw(place=at)
        if k == CK.BINARY_OPERATOR:
            lhs, rhs = list(c.get_children())
            if tokens_after(c, lhs) != "=":
                refuse(c, "an expression as a statement that is not an assignment")
            value = self.expr(rhs)
            return Set(self.assign(lhs), value, place=at)
        refuse(c, "%s (not in the spike's subset: no do-while, calls, switch, goto, try, new or delete)"
               % k.name.lower().replace("_", " "))

    def assign(self, lhs):
        """What an assignment assigns: a Name (a local, a parameter, a field) or an Elem."""
        if lhs.kind == CK.DECL_REF_EXPR and self.m is not None and lhs.spelling in self.m.lengths:
            refuse(lhs, "an assignment to a view's length: it says how many bytes may be read")
        if lhs.kind == CK.DECL_REF_EXPR:
            self.expr(lhs)
            return Name(named(lhs.spelling), "param" if lhs.referenced.kind == CK.PARM_DECL else "local", place=where(lhs))
        if lhs.kind == CK.MEMBER_REF_EXPR:
            f = self.own_field(lhs)
            if f.count is not None:
                refuse(lhs, "an array assigned whole")
            self.assigned.add(f.name)
            return Name(named(f.name), "field", place=where(lhs))
        if lhs.kind == CK.ARRAY_SUBSCRIPT_EXPR:
            e = self.array_place(lhs)
            if self.in_ctor:
                if e.lit is None:
                    refuse(lhs, "the constructor names each element by a number")
                self.assigned.add((e.field, e.lit))
            named(e.field)
            return e
        refuse(lhs, "an assignment to something that is not a local, a field, or an element")

    def outside_call(self, c):
        """OutCall, if a CALL_EXPR calls a function outside the program that the program gives a
        contract for; else None. Once in a method, outside any loop or branch of its own (so the
        world it is answered by is its alone)."""
        c = unparen(c)
        ref = c.referenced if c.kind == CK.CALL_EXPR else None
        if ref is None or ref.kind != CK.FUNCTION_DECL or ref.spelling not in OPTIONS["outside"]:
            return None
        if self.m is None or self.in_ctor or self.plain:
            refuse(c, "a call of a function outside the program in a constructor or the invariant")
        if self.loops or self.outcalls:
            refuse(c, "a second call of a function outside the program in a method, or one in a loop (not yet)")
        contract = OPTIONS["outside"][ref.spelling]
        params = [p for p in ref.get_children() if p.kind == CK.PARM_DECL]
        given = list(c.get_children())[1:]
        if len(given) != len(params):
            refuse(c, "a call with a default argument")
        named_in = {p for p, _ in contract["reads"]} | {p for p, _ in contract["writes"]}
        args = []
        for p, a in zip(params, given):
            if p.type.get_canonical().kind == TK.POINTER and p.spelling in contract["keeps"]:
                # The function's own state: a field of the class that only such calls are handed,
                # which the model does not read (trusted: that it is the function's, and nothing else's).
                h = unparen(a)
                while h.kind in (CK.CSTYLE_CAST_EXPR, CK.CXX_STATIC_CAST_EXPR, CK.UNEXPOSED_EXPR) and len(list(h.get_children())) == 1:
                    h = unparen(list(h.get_children())[0])
                if h.kind != CK.MEMBER_REF_EXPR or h.spelling not in self.k.handles:
                    refuse(a, "what '%s' keeps is not a field of this class that holds the function's own state" % ref.spelling)
                args.append((p.spelling, "keeps", None))
                continue
            if p.type.get_canonical().kind == TK.POINTER:
                place = self.byte_place(a)
                if p.spelling in {q for q, _ in contract["writes"]}:
                    if place is None or place[0] is None:
                        refuse(a, "what '%s' writes is not one of this class's arrays of bytes" % ref.spelling)
                    args.append((p.spelling, "write", place))
                elif p.spelling in named_in:
                    if place is None:
                        refuse(a, "what '%s' reads is not an array of bytes of this class, or a view" % ref.spelling)
                    args.append((p.spelling, "read", place))
                elif unparen(a).kind in (CK.CXX_NULL_PTR_LITERAL_EXPR, CK.GNU_NULL_EXPR) or self.literal(a) == 0:
                    args.append((p.spelling, "null", None))
                else:
                    refuse(a, "a pointer handed to '%s' that its contract does not say how many bytes of it are "
                              "read or written" % ref.spelling)
            else:
                args.append((p.spelling, "int", (self.expr(a), int_of(p.type, p).signed)))
        for q, _ in contract["reads"] + contract["writes"]:
            if q not in [p.spelling for p in params]:
                refuse(c, "the contract of '%s' names a parameter it does not have: %s" % (ref.spelling, q))
        self.outcalls += 1
        self.m.world = True
        spaces, at_ = [], ref.semantic_parent
        while at_ is not None and at_.kind in (CK.NAMESPACE, CK.LINKAGE_SPEC):
            if at_.kind == CK.NAMESPACE:
                spaces.insert(0, at_.spelling)
            at_ = at_.semantic_parent
        contract["sig"] = (ref.result_type.spelling, [(p.type.spelling, p.spelling) for p in params], spaces)
        rt = ref.result_type.get_canonical()
        result = None if rt.kind == TK.VOID else (int_of(rt, c).width, int_of(rt, c).signed)
        return OutCall(ref.spelling, args, result, place=where(c))

    def buffer_call(self, c, which):
        """The buffer field whose data method (which 0) or length method (1) this calls; else None."""
        c = unparen(c)
        if c.kind != CK.CALL_EXPR:
            return None
        parts = list(c.get_children())
        if len(parts) != 1 or parts[0].kind != CK.MEMBER_REF_EXPR:
            return None
        obj = [x for x in parts[0].get_children()]
        if len(obj) != 1 or unparen(obj[0]).kind != CK.MEMBER_REF_EXPR:
            return None
        f = self.k.field.get(unparen(obj[0]).spelling)
        if f is None or not f.buffer or parts[0].spelling != f.buffer[which]:
            return None
        return f

    def byte_place(self, c):
        """A place memcpy is handed: (field, None) for one of the class's byte arrays, or (None,
        view) for a view's pointer; with what is added to it, `X + k` (None if nothing). Else None."""
        c = unparen(c)
        while c.kind in (CK.CSTYLE_CAST_EXPR, CK.CXX_STATIC_CAST_EXPR, CK.CXX_REINTERPRET_CAST_EXPR, CK.UNEXPOSED_EXPR) \
                and len([x for x in c.get_children() if x.kind != CK.TYPE_REF]) == 1:
            c = unparen([x for x in c.get_children() if x.kind != CK.TYPE_REF][0])
        k = None
        if c.kind == CK.BINARY_OPERATOR and tokens_after(c, list(c.get_children())[0]) == "+":
            c, off = list(c.get_children())
            c = unparen(c)
            if int_of(off.type, off).signed and self.literal(off) is None:
                refuse(off, "a place moved by a signed number (it could be negative)")
            k = self.expr(off)      # (the model takes its number: its width does not matter)
        if self.buffer_call(c, 0) is not None:      # a buffer's bytes
            return (self.buffer_call(c, 0).name, None, k)
        if c.kind == CK.MEMBER_REF_EXPR:
            f = self.own_field(c)
            if f.count is None or f.type.width != 8:
                refuse(c, "a memcpy of a field that is not an array of bytes")
            return (f.name, None, k)
        view = self.view_of(c)
        if view is None and c.kind == CK.DECL_REF_EXPR and c.spelling in self.raw:
            view = c.spelling       # a view of signed bytes: copied as bytes, which is all memcpy does
        if view is not None:
            return (None, view, k)
        return None

    def sub_view(self, p, n, t):
        """A view handed on as a pointer and a number of bytes (`p + j, n`): n bytes of one of this
        method's views from j, owed within it."""
        if not t.length:
            refuse(p, "a view handed on to what takes one but not as a pointer and its length (not yet)")
        place = self.byte_place(p)
        if place is None or place[1] is None:
            refuse(p, "a view handed on that is not one of this method's own views, or part of one")
        if int_of(n.type, n).signed and self.literal(n) is None:
            refuse(n, "a view's length of a signed type")
        return Sub(named(place[1]), place[2], self.expr(n), place=where(p))

    def object_bytes(self, c):
        """(the value's name, its array) for `x.data()` with x a value of another class, made here or
        given, and data a method of x's class that gives where one of its arrays of bytes begins
        (with what is added to it, as byte_place); else None."""
        c = unparen(c)
        while c.kind in (CK.CSTYLE_CAST_EXPR, CK.CXX_STATIC_CAST_EXPR, CK.CXX_REINTERPRET_CAST_EXPR, CK.UNEXPOSED_EXPR) \
                and len([x for x in c.get_children() if x.kind != CK.TYPE_REF]) == 1:
            c = unparen([x for x in c.get_children() if x.kind != CK.TYPE_REF][0])
        k = None
        if c.kind == CK.BINARY_OPERATOR and tokens_after(c, list(c.get_children())[0]) == "+":
            c, off = list(c.get_children())
            c = unparen(c)
            if int_of(off.type, off).signed and self.literal(off) is None:
                refuse(off, "a place moved by a signed number (it could be negative)")
            k = off
        parts = list(c.get_children()) if c.kind == CK.CALL_EXPR else []
        if len(parts) != 1 or parts[0].kind != CK.MEMBER_REF_EXPR:
            return None
        obj = [unparen(x) for x in parts[0].get_children()]
        if len(obj) != 1 or obj[0].kind != CK.DECL_REF_EXPR or obj[0].spelling not in self.objects:
            return None
        u = self.objects[obj[0].spelling]
        if parts[0].spelling not in u.k.gives:
            return None
        if self.loops or self.in_block:
            refuse(c, "the bytes of a value of another class read in a loop or a branch of its own (not yet)")
        return (named(obj[0].spelling), u.k.gives[parts[0].spelling], self.expr(k) if k is not None else None)

    def memcpy(self, c):
        """memcpy( FIELD [+ k], SOURCE [+ j], n ): n bytes into one of the class's byte arrays,
        from another or from a view. What is owed is that both are within: the model is `none`
        where either is passed, as a read or a write outside an array is."""
        parts = list(c.get_children())
        ref = unparen(parts[0]).referenced if parts else None
        if ref is None or ref.kind != CK.FUNCTION_DECL or not ref.location.is_in_system_header or len(parts) != 4:
            refuse(c, "a memcpy that is not the library's")
        dst, obj = self.byte_place(parts[1]), self.object_bytes(parts[2])
        src = (None, None, obj[2]) if obj is not None else self.byte_place(parts[2])
        if dst is None or dst[0] is None:
            refuse(c, "a memcpy into something that is not one of this class's arrays of bytes")
        if src is None:
            refuse(c, "a memcpy from something that is not an array of bytes of this class, or a view")
        if obj is None and src[0] == dst[0]:
            refuse(c, "a memcpy within one array (its two places may overlap, which is undefined)")
        n = unparen(parts[3])
        if int_of(n.type, n).signed and self.literal(n) is None:
            refuse(n, "a memcpy of a number of bytes of a signed type")
        if self.in_ctor and src[0] is not None:
            refuse(c, "a copy from a field in the constructor (it may not have a value yet)")
        count = self.expr(n)
        self.assigned.add(dst[0])
        self.cover(dst[0], parts[1], n)
        named(dst[0])
        return Memcpy(dst[0], dst[2], src[0], src[1], src[2], count, src_obj=obj[:2] if obj else None, place=where(c))

    def memset(self, c):
        """memset( FIELD, BYTE, sizeof( FIELD ) ), of one of the class's own arrays, whole: every
        element becomes that byte in each of its bytes. Any other memset could write anywhere."""
        parts = list(c.get_children())
        ref = unparen(parts[0]).referenced if parts else None
        if ref is None or ref.kind != CK.FUNCTION_DECL or not ref.location.is_in_system_header or len(parts) != 4:
            refuse(c, "a memset that is not the library's")
        target, size = unparen(parts[1]), unparen(parts[3])
        byte = plain_literal(parts[2])
        words = [t.spelling for t in size.get_tokens()]
        whole = size.kind == CK.CXX_UNARY_EXPR and [w for w in words if w not in "()"] == ["sizeof", target.spelling]
        place = None if whole else self.byte_place(parts[1])     # (a whole array may be of any width)
        if place is not None and place[0] is not None and not whole and byte is not None and 0 <= byte <= 255:
            # Part of an array of bytes: n bytes from k, owed within it.
            if int_of(size.type, size).signed and self.literal(size) is None:
                refuse(size, "a memset of a number of bytes of a signed type")
            self.assigned.add(place[0])
            self.cover(place[0], parts[1], size)
            return Fill(named(place[0]), place[2], byte, self.expr(size), place=where(c))
        if (target.kind != CK.MEMBER_REF_EXPR or byte is None or not 0 <= byte <= 255 or size.kind != CK.CXX_UNARY_EXPR
                or [w for w in words if w not in "()"] != ["sizeof", target.spelling]):
            refuse(c, "a memset that is not memset( FIELD, BYTE, sizeof( FIELD ) ) of an array of this class")
        f = self.own_field(target)
        if f.count is None:
            refuse(c, "a memset of something that is not an array of this class")
        self.assigned.update((f.name, i) for i in range(f.count))
        return Memset(named(f.name), byte, place=where(c))

    def cover(self, field, at, n):
        """In the constructor: the elements of `field` a copy or a fill of n bytes at `at` assigns,
        where both its place and n are numbers written out (else none is known to be assigned, and
        the constructor is refused if one is left with no value)."""
        if not self.in_ctor:
            return
        k, count = self.offset_of(at), self.literal(n)
        if k is not None and count is not None:
            self.assigned.update((field, i) for i in range(k, k + count))

    def offset_of(self, c):
        """The number a place handed to memcpy or memset is moved by (`X + k`): 0 if it is not
        moved, None if k is not a number written out."""
        c = unparen(c)
        while c.kind in (CK.CSTYLE_CAST_EXPR, CK.CXX_STATIC_CAST_EXPR, CK.CXX_REINTERPRET_CAST_EXPR, CK.UNEXPOSED_EXPR) \
                and len([x for x in c.get_children() if x.kind != CK.TYPE_REF]) == 1:
            c = unparen([x for x in c.get_children() if x.kind != CK.TYPE_REF][0])
        if c.kind == CK.BINARY_OPERATOR and tokens_after(c, list(c.get_children())[0]) == "+":
            return self.literal(list(c.get_children())[1])
        return 0


ENDS = ("exit", "_Exit", "_exit", "abort")         # the system's: each ends the process


def is_throw(c):
    return c.kind == CK.CXX_THROW_EXPR or (c.kind == CK.UNEXPOSED_EXPR and [x.kind for x in c.get_children()] == [CK.CXX_THROW_EXPR])


def guard_of(c):
    """The condition of `if ( c ) throw ...;` (or `{ throw ...; }`), with no else; else None."""
    if c.kind != CK.IF_STMT:
        return None
    parts = list(c.get_children())
    if len(parts) != 2:
        return None
    then = parts[1]
    if then.kind == CK.COMPOUND_STMT and len(list(then.get_children())) == 1:
        then = list(then.get_children())[0]
    return parts[0] if is_throw(then) else None


def system_call(c, names=None):
    """The name of the system's function a CALL_EXPR calls (one declared in a system header, and in
    `names` if they are given); else None."""
    if c.kind != CK.CALL_EXPR:
        return None
    ref = c.referenced
    if ref is None or ref.kind != CK.FUNCTION_DECL or not ref.location.is_in_system_header:
        return None
    return ref.spelling if names is None or ref.spelling in names else None


def plain_arguments(c):
    """Whether every argument of a call is a literal, or a name the system declares (`stderr`): so
    the call reads nothing of the program's."""
    for a in list(c.get_children())[1:]:
        for x in a.walk_preorder():
            r = x.referenced if x.kind == CK.DECL_REF_EXPR else None
            if x.kind in (CK.MEMBER_REF_EXPR, CK.CXX_THIS_EXPR) or (r is not None and r.kind in (CK.PARM_DECL, CK.FIELD_DECL)) \
                    or (r is not None and r.kind == CK.VAR_DECL and not r.location.is_in_system_header):
                return False
    return True


def signed_as_written(c):
    """Whether an operand is of a signed type of 32 bits or more as it is written: a literal, or a
    name or expression of that type, not a narrower or unsigned number C++ converted to one."""
    while c.kind in (CK.UNEXPOSED_EXPR, CK.PAREN_EXPR) and len(list(c.get_children())) == 1:
        inner = list(c.get_children())[0]
        k = inner.type.get_canonical().kind
        if k not in SIGNED:
            return inner.kind == CK.INTEGER_LITERAL     # a literal, made the type it is used at
        c = inner
    k = c.type.get_canonical().kind
    return k in SIGNED and SIGNED[k] >= 32


def is_end(c):
    """Whether a statement ends the process: a call of exit, _Exit, _exit or abort."""
    c = unparen(c)
    return system_call(c, ENDS) is not None


def assert_of(c):
    """The condition of `assert( condition )`, as the library expands it: `condition ? (void)0 :
    __assert_fail( ... )` (or the like); None if this statement is no assert. Refused if it is an
    assert compiled away (NDEBUG): what follows would rest on a test that is not made."""
    if not READ["text"][c.extent.start.offset:].startswith(b"assert"):
        return None
    tests = [x for x in c.walk_preorder() if x.kind == CK.CONDITIONAL_OPERATOR]
    if not tests:
        refuse(c, "an assert compiled away (NDEBUG): what follows may not rest on it, since it is not tested")
    test = list(tests[0].get_children())[0]
    while test.kind in (CK.CXX_STATIC_CAST_EXPR, CK.UNEXPOSED_EXPR, CK.PAREN_EXPR, CK.CSTYLE_CAST_EXPR) and len(
            [x for x in test.get_children() if x.kind != CK.TYPE_REF]) == 1:
        test = [x for x in test.get_children() if x.kind != CK.TYPE_REF][0]
    return test


def step_of(c):
    """"+" or "-" if this UNARY_OPERATOR is ++ or --, before or after; else None."""
    words = [t.spelling for t in c.get_tokens()]
    for w in (words[:1] + words[-1:]):
        if w in ("++", "--"):
            return w[0]
    return None


def assigned_names(cursors):
    """The names of what the cursors assign: model.Writer.changed_in says the same of the tree. Asked
    here only for the order in which names are refused (see BodyReader.function_names)."""
    names = set()
    for top in cursors:
        if top is None:
            continue
        for c in top.walk_preorder():
            if c.kind == CK.CALL_EXPR:
                continue
            if c.kind == CK.UNARY_OPERATOR and step_of(c) is None:
                continue
            if c.kind not in (CK.BINARY_OPERATOR, CK.COMPOUND_ASSIGNMENT_OPERATOR, CK.UNARY_OPERATOR):
                continue
            lhs = list(c.get_children())[0]
            if c.kind == CK.BINARY_OPERATOR and tokens_after(c, lhs) != "=":
                continue
            lhs = unparen(lhs)
            if lhs.kind == CK.DECL_REF_EXPR:
                names.add(lhs.spelling)
    return names


def ready_of(k):
    """The methods of a class read whole, by name: what a call on a value of it may name."""
    return {m.name: m for m in k.methods}


def can_fail(c, plain, parts=False):
    """Whether a condition could fail to have a value: it reads a view, or an array (but in the
    invariant or a precondition, by a number inside it), or calls, or divides or shifts by what is
    known only when it runs. With `parts` (the invariant), a call of a part's const method is let
    through: the invariant is then that the condition has a value, and is true."""
    return any((isinstance(x, (Byte, Call, OtherCall)) and not (parts and isinstance(x, OtherCall) and x.field))
               or (isinstance(x, Elem) and not plain)
               or (isinstance(x, Div) and not x.known) or (isinstance(x, Shift) and x.amount is None)
               for x in cxx.walk(c))


# ---------------------------------------------------------------------------
# The class
# ---------------------------------------------------------------------------

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
        it = int_of(decl.get_template_argument_type(0), cursor)
        if it.signed or it.is_bool:
            refuse(cursor, "a class template used at a type that is not an unsigned integer (not yet: "
                           "the template is proved of every type, but a class that uses it is read with unsigned numbers only)")
        at = (it, [decl.get_template_argument_unsigned_value(i) for i in range(1, n)])
        decl = made_from
    if decl.kind not in (CK.CLASS_DECL, CK.CLASS_TEMPLATE) or not decl.is_definition():
        refuse(cursor, "a parameter of a type that is not a class read here")
    if decl.spelling not in USED:
        USED[decl.spelling] = read_class(decl)      # whole, bodies too: what its methods are, and that it is in the subset
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


def buffer_of(t):
    """(data, len) if a type is one the program says is a buffer of bytes it owns; else None."""
    name = t.get_canonical().spelling.split("::")[-1]
    return OPTIONS["buffers"].get(name)


def buffer_lengths(k, ctor):
    """Each buffer field's number of bytes: what the constructor makes it of, in its initializer
    list, a literal or a constant (of this class or another)."""
    parts = [c for c in ctor.get_children() if c.kind not in (CK.COMPOUND_STMT, CK.PARM_DECL, CK.TYPE_REF, CK.NAMESPACE_REF)]
    for i, c in enumerate(parts):
        if c.kind != CK.MEMBER_REF or c.spelling not in k.field or not k.field[c.spelling].buffer:
            continue
        init = parts[i + 1] if i + 1 < len(parts) and parts[i + 1].kind != CK.MEMBER_REF else None
        made = [x for x in unparen(init).walk_preorder() if x.kind in (CK.INTEGER_LITERAL, CK.DECL_REF_EXPR)] if init is not None else []
        n = None
        if len(made) == 1 and made[0].kind == CK.INTEGER_LITERAL:
            n = plain_literal(made[0])
        elif len(made) == 1 and made[0].referenced is not None and made[0].referenced.kind == CK.VAR_DECL \
                and made[0].referenced.type.is_const_qualified():
            value = [x for x in made[0].referenced.get_children() if x.kind != CK.TYPE_REF]
            n = plain_literal(value[0]) if len(value) == 1 else None
        if n is None or n < 0:
            refuse(c, "a buffer made of a number of bytes that is not a literal or a constant")
        k.field[c.spelling].count = n
    for f in k.fields:
        if f.buffer and f.count is None:
            refuse(ctor, "a buffer the constructor does not make: '%s'" % f.name)


def read_field(cursor, klass):
    t = cursor.type.get_canonical()
    if t.kind == TK.RECORD and buffer_of(t):
        # Bytes the class owns, of a number its constructor gives: read as an array of that many,
        # made zeros (what the bytes are before they are written is not read: trusted).
        f = cxx.Field(cursor.spelling, Int(8), None)
        f.buffer = buffer_of(t)
        return f
    if is_gen(klass, cursor.type):
        return cxx.Field(cursor.spelling, GenT())
    if t.kind == TK.RECORD:
        # A part: a value of another class read here, which this class has. It is proved apart; here
        # it is given its own invariant, and changed by its own methods alone.
        u = used_class(cursor, t)
        if u.at is not None or klass.generic:
            refuse(cursor, "a part that is of a class template, or in one (not yet)")
        not_checked(cursor, klass.name, u.k.name)
        klass.uses[u.k.name] = u.k
        return cxx.Field(cursor.spelling, u)
    if t.kind == TK.CONSTANTARRAY and t.element_type.get_canonical().kind in (TK.CHAR_S, TK.CHAR_U, TK.SCHAR):
        return cxx.Field(cursor.spelling, Int(8), t.element_count, chars=True)    # bytes, only copied
    if t.kind == TK.CONSTANTARRAY:
        f = cxx.Field(cursor.spelling, int_of(t.element_type, cursor), t.element_count)
        if f.type.signed:
            refuse(cursor, "an array of a signed type")
        return f
    f = cxx.Field(cursor.spelling, int_of(t, cursor))
    if f.type.signed:
        refuse(cursor, "a signed field: its arithmetic can overflow, which is undefined")
    return f


class MethodText:
    """A method as it stands in the text, until its body is read: its cursor, its body's, and its
    conditions'."""

    def __init__(self, cursor, body, pre):
        self.cursor, self.body, self.pre = cursor, body, pre


def read_params(cursor, klass, m):
    """A method's parameters, or a constructor's, into m.params (and a view's length into m.lengths)."""
    parms = [c for c in cursor.get_children() if c.kind == CK.PARM_DECL and not is_caller(c.type)]
    while parms:
        c = parms.pop(0)
        if not c.spelling:
            refuse(c, "a parameter with no name")
        ct = c.type.get_canonical()
        if subarray_of(c.type):
            t = BytesT(ctype=subarray_of(c.type))
        elif fixed_of(c.type):
            t = BytesT(ctype=fixed_of(c.type)[0], fixed=fixed_of(c.type)[1])
        elif is_bytes(c.type):
            t = BytesT()
        elif ct.kind == TK.RECORD:
            t = used_class(c, ct)
            if t.k.ctor is not None and (t.k.ctor.throws or any(isinstance(x, BytesT) for _, x in t.k.ctor_params)):     # (it is made by its first)
                refuse(c, "a parameter of a class whose constructor throws or takes a view (not yet: the "
                          "comparison makes each such value by its constructor)")
            not_checked(c, m.name, t.k.name)
            klass.uses[t.k.name] = t.k
        elif ct.kind == TK.POINTER:
            to = ct.get_pointee()
            n = parms.pop(0) if parms else None
            if (to.kind not in (TK.UCHAR, TK.CHAR_S, TK.CHAR_U) or not to.is_const_qualified() or n is None
                    or not n.spelling or n.type.get_canonical().kind not in (TK.ULONG, TK.ULONGLONG)):
                refuse(c, "a pointer parameter that is not to const bytes, with their number (an unsigned "
                          "64-bit parameter) next after it: the two together are a view")
            t = BytesT(length=n.spelling, readable=to.kind == TK.UCHAR, ctype=to.spelling.replace("const ", ""))
            m.lengths[n.spelling] = c.spelling
        else:
            t = typ(klass, c.type, c)
            if t.signed:
                refuse(c, "a signed parameter")
        m.params.append((c.spelling, t))


def read_method(cursor, klass):
    """A method's declaration: (cxx.Method, MethodText). Its body is read after every method's
    declaration is (read_bodies)."""
    rt = cursor.result_type
    m = cxx.Method(cursor.spelling, cursor.is_const_method(), cursor.access_specifier == ci.AccessSpecifier.PUBLIC,
                   None if rt.get_canonical().kind == TK.VOID else typ(klass, rt, cursor), place=where(cursor))
    read_params(cursor, klass, m)
    body = None
    if not any(c.kind == CK.COMPOUND_STMT for c in cursor.get_children()) and cursor.get_definition() is not None:
        cursor = cursor.get_definition()        # defined outside the class (`defined FILE`), after it in the text read
    for c in cursor.get_children():
        if c.kind == CK.COMPOUND_STMT:
            body = c
    if body is None:
        refuse(cursor, "a method with no body here: the model is the body")
    pre, m.tested = pre_of(cursor, body, m.name)
    m.words = words(body)
    m.throws = any(v.kind == CK.CXX_THROW_EXPR for v in body.walk_preorder())
    m.ends = any(system_call(v, ENDS + ("__assert_fail", "__assert_rtn", "_assert")) is not None for v in body.walk_preorder())
    for v in body.walk_preorder():        # a local that is another class's value: that class is used
        if v.kind == CK.VAR_DECL and v.type.get_canonical().kind == TK.RECORD:
            u = used_class(v, v.type.get_canonical())
            not_checked(v, m.name, u.k.name)
            klass.uses[u.k.name] = u.k
            if any(x.throws for x in u.k.ctors):
                made = [x for x in v.get_children() if x.kind not in (CK.TYPE_REF, CK.TEMPLATE_REF, CK.NAMESPACE_REF)]
                if len(made) == 1 and chosen(u, unparen(made[0]), v).throws:
                    m.throws = True     # what its constructor throws, the method throws: it is not caught (no try is read)
    if (m.throws or m.ends) and klass.generic:
        refuse(cursor, "a throw, or an end of the process, in a class template")
    return m, MethodText(cursor, body, pre)


def gives_bytes(cursor, k):
    """The field, for a const method whose body is `return FIELD;` of one of the class's arrays of
    bytes, as a pointer to const bytes: where they begin. Else None."""
    rt = cursor.result_type.get_canonical()
    if rt.kind != TK.POINTER or not cursor.is_const_method():
        return None
    to = rt.get_pointee()
    if to.kind not in (TK.UCHAR, TK.CHAR_S, TK.CHAR_U) or not to.is_const_qualified():
        return None
    body = [x for x in cursor.get_children() if x.kind == CK.COMPOUND_STMT]
    only = list(body[0].get_children()) if len(body) == 1 else []
    if len(only) != 1 or only[0].kind != CK.RETURN_STMT or any(x.kind == CK.PARM_DECL for x in cursor.get_children()):
        return None
    value = list(only[0].get_children())
    f = unparen(value[0]) if len(value) == 1 else None
    while f is not None and f.kind in (CK.UNEXPOSED_EXPR, CK.CSTYLE_CAST_EXPR, CK.CXX_REINTERPRET_CAST_EXPR, CK.CXX_STATIC_CAST_EXPR) \
            and len([x for x in f.get_children() if x.kind != CK.TYPE_REF]) == 1:
        f = unparen([x for x in f.get_children() if x.kind != CK.TYPE_REF][0])
    if f is None or f.kind != CK.MEMBER_REF_EXPR or f.referenced is None or f.referenced.kind != CK.FIELD_DECL:
        return None
    t = f.referenced.type.get_canonical()
    if t.kind != TK.CONSTANTARRAY or t.element_type.get_canonical().kind not in (TK.UCHAR, TK.CHAR_S, TK.CHAR_U, TK.SCHAR):
        return None
    return f.spelling


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


def read(cursor):
    """A class, or a function read as a class, as the command reads it: whole, and then what the
    comparison needs of a class template."""
    if cursor.kind == CK.FUNCTION_DECL:
        return read_function(cursor)
    k, texts = read_whole(cursor)
    if k.generic:       # what the comparison with the C++ knows how to drive
        for m, text in zip(k.methods, texts):
            if m.public and any(not isinstance(t, (GenT, Int)) for _, t in m.params):
                refuse(text.cursor, "a class template's method that takes a view or another class")
        if len(k.generic[1]) != 2:
            refuse(cursor, "a class template of other than two values (the comparison knows two: the bounds)")
    return k


def read_class(cursor):
    return read_whole(cursor)[0]


def ctor_copy(c):
    """Whether a constructor is the copy or move constructor."""
    ps = [x for x in c.get_children() if x.kind == CK.PARM_DECL]
    return len(ps) == 1 and ps[0].type.get_canonical().kind in (TK.LVALUEREFERENCE, TK.RVALUEREFERENCE)


def read_whole(cursor):
    """A class: its declarations, then its bodies, in the order the generator always read them.
    (the class, the text of each of its methods)"""
    k = cxx.Klass(cursor.spelling, qual_of(cursor), place=where(cursor))
    if cursor.kind == CK.CLASS_TEMPLATE:
        types = [c for c in cursor.get_children() if c.kind == CK.TEMPLATE_TYPE_PARAMETER]
        values = [c for c in cursor.get_children() if c.kind == CK.TEMPLATE_NON_TYPE_PARAMETER]
        if len(types) != 1 or any(v.type.spelling != types[0].spelling for v in values):
            refuse(cursor, "a class template that is not of one type and values of that type: "
                           "`template <typename T, T A, T B>`")
        k.generic = (types[0].spelling, [v.spelling for v in values])
    texts = []
    ctor = inv = None
    ctors = []          # each constructor's cursor (where it is defined) and its pre( conditions ), as k.ctors
    only = OPTIONS["only"]
    fields = []
    for c in cursor.get_children():
        kind = c.kind
        if only is not None:
            # Read for some methods only: what is owed of them holds from any state (the class says no
            # invariant), so the rest of the class is passed over. A constructor is kept only for the
            # lengths it gives its buffers; a field none of the read methods names is left out.
            if kind == CK.CXX_METHOD and c.spelling == "invariant":
                refuse(c, "`only` of a class that says an invariant: every method is owed to keep it")
            if kind == CK.CXX_METHOD and c.spelling not in only:
                continue
            if kind in (CK.CONSTRUCTOR, CK.DESTRUCTOR, CK.CONVERSION_FUNCTION, CK.FUNCTION_TEMPLATE):
                if kind == CK.CONSTRUCTOR and c.get_definition() is not None and not ctor_copy(c):
                    ctor = c.get_definition()
                continue
            if kind == CK.FIELD_DECL:
                fields.append(c)
                continue
            if kind == CK.VAR_DECL and c.type.is_const_qualified():
                value = [x for x in c.get_children() if x.kind != CK.TYPE_REF]
                lit = plain_literal(value[0]) if len(value) == 1 else None
                if lit is not None and lit >= 0:
                    k.constants[c.spelling] = lit
                continue
        if kind in (CK.CXX_ACCESS_SPEC_DECL, CK.TEMPLATE_TYPE_PARAMETER, CK.TEMPLATE_NON_TYPE_PARAMETER):
            continue
        if kind == CK.STATIC_ASSERT:
            continue        # the compiler's to check, and nothing here rests on it
        if kind == CK.CXX_BASE_SPECIFIER:
            refuse(c, "a base class (the spike reads one class alone)")
        if kind == CK.FRIEND_DECL:
            refuse(c, "a friend: it could reach the state from outside the class")
        if kind == CK.FIELD_DECL:
            if c.access_specifier != ci.AccessSpecifier.PRIVATE:
                refuse(c, "the field '%s' is not private: anything could change it, and no "
                          "invariant of the class would hold of the program" % c.spelling)
            if c.is_mutable_field():
                refuse(c, "a mutable field: a const method could change the state")
            k.fields.append(read_field(c, k))
        elif kind == CK.CONSTRUCTOR:
            if ctor_copy(c):
                if any(t.spelling in ("delete", "default") for t in c.get_tokens()):
                    continue        # C++'s own (it copies each field), or none
                refuse(c, "a copy or move constructor written out (not read)")
            # Its parameters as a method's are: numbers, and views (a pointer to const bytes and their number).
            m = cxx.Method("new", False, True, None, place=where(c))
            for x in c.get_children():
                if x.kind == CK.PARM_DECL and not x.spelling:
                    refuse(x, "a constructor's parameter that has no name")
                if x.kind == CK.PARM_DECL and x.type.get_canonical().kind == TK.RECORD and not is_caller(x.type):
                    refuse(x, "a constructor's parameter that is a value of another class (not yet)")
            read_params(c, k, m)
            d = c.get_definition() or c       # (defined outside the class, after it in the text read: `defined FILE`)
            m.usr = c.get_usr()
            m.throws = any(v.kind == CK.CXX_THROW_EXPR for v in d.walk_preorder())
            pre, m.tested = pre_of(d, ([x for x in d.get_children() if x.kind == CK.COMPOUND_STMT] or [None])[0], k.name)
            k.ctors.append(m)
            ctors.append((d, pre))
            ctor = ctor or d
        elif kind == CK.DESTRUCTOR:
            body = [x for x in c.get_children() if x.kind == CK.COMPOUND_STMT]
            if not body or list(body[0].get_children()):
                refuse(c, "a destructor that does something")
        elif kind == CK.CXX_METHOD:
            if c.is_virtual_method() or c.is_static_method():
                refuse(c, "a virtual or static method (the spike reads plain methods)")
            if c.spelling.startswith("operator"):
                refuse(c, "an operator")
            if gives_bytes(c, k) is not None:
                k.gives[c.spelling] = gives_bytes(c, k)      # owed nothing: it reads and writes nothing
            elif c.spelling == "invariant":
                inv = invariant_of(c)
                k.inv_words = words([x for x in c.get_children() if x.kind == CK.COMPOUND_STMT][0])
            else:
                m, text = read_method(c, k)
                k.methods.append(m)
                texts.append(text)
        elif kind == CK.VAR_DECL:
            if not c.type.is_const_qualified():
                refuse(c, "a static member that is not const: it is state outside the object")
            it = int_of(c.type, c)
            value = [x for x in c.get_children() if x.kind != CK.TYPE_REF]
            lit = plain_literal(value[0]) if len(value) == 1 else None
            if lit is None or it.signed:
                refuse(c, "a constant that is not an unsigned number given by a literal")
            k.constants[c.spelling] = lit % (1 << it.width)
        else:
            refuse(c, "%s in a model class" % kind.name.lower().replace("_", " "))
    if only is not None:
        missing = only - {m.name for m in k.methods}
        if missing:
            refuse(cursor, "`only` names what is not a method of the class with a body: %s" % ", ".join(sorted(missing)))
        used = {x.spelling for t in texts for x in t.body.walk_preorder()
                if x.kind == CK.MEMBER_REF_EXPR and x.referenced is not None and x.referenced.kind == CK.FIELD_DECL
                and x.referenced.semantic_parent == cursor}
        for c in fields:
            if c.spelling in used and c.type.get_canonical().kind == TK.POINTER:
                k.handles.add(c.spelling)       # held for a function outside: not state the model reads
                continue
            if c.spelling in used:
                if c.access_specifier != ci.AccessSpecifier.PRIVATE:
                    refuse(c, "the field '%s' is not private" % c.spelling)
                k.fields.append(read_field(c, k))
        k.only = True
    elif not k.ctors:
        refuse(cursor, "no constructor: the state would begin as anything")
    if len(k.ctors) > 1 and k.generic:
        refuse(cursor, "a class template of more than one constructor (not yet)")
    if len(k.ctors) > 1:        # each is named by what it takes, as the model has it
        for m in k.ctors:
            m.name = "new_" + "_".join(n for n, _ in m.params) if m.params else "new"
        names = [m.name for m in k.ctors]
        if len(set(names)) != len(names):
            refuse(cursor, "two constructors whose parameters have the same names: name them apart")
    if inv is None and not OPTIONS["no_invariant"]:
        refuse(cursor, "no `bool invariant() const`: what is owed is derived from it, so the class "
                       "must say it (one that claims nothing is `return true;`)")
    k.field = {f.name: f for f in k.fields}
    k.public = [m for m in k.methods if m.public]
    read_bodies(k, cursor, ctors, inv, texts, buffer_ctor=ctor)
    return k, texts


def read_function(cursor):
    """A function that is not a method, read as a class with no state and one method: what is owed
    of it is that it ends and commits no memory error, for every argument."""
    k = cxx.Klass(cursor.spelling, cursor.spelling, place=where(cursor))
    k.is_function = True
    if cursor.is_static_method() or cursor.kind != CK.FUNCTION_DECL:
        refuse(cursor, "not a function")
    m, text = read_method(cursor, k)
    m.const = m.public = True
    m.name = "call"            # the structure has the function's name: its one method is the call of it
    k.methods = k.public = [m]
    read_bodies(k, None, [], None, [text])
    return k


def read_bodies(k, kc, ctors, inv, texts, buffer_ctor=None):
    """The invariant, each constructor and each method's body, in that order; and with each, the
    names the model is written with, where it first writes them (see named)."""
    ready = {}                          # the methods read so far: what a call may name
    for f in k.fields:
        named(f.name)
    if not k.is_function and any(f.buffer for f in k.fields):
        if buffer_ctor is None:
            refuse(kc, "a buffer, and no constructor here to say how many bytes it is made of")
        if len(k.ctors) > 1:
            refuse(kc, "a buffer, in a class of more than one constructor (not yet)")
        buffer_lengths(k, buffer_ctor)
    if inv is not None:
        k.inv = BodyReader(k, kc, ready, plain=True).cond(inv)
        if can_fail(k.inv, True, parts=True):
            refuse(inv, "an invariant that could fail to have a value")
    for v in (k.generic[1] if k.generic else []):
        named(v)
    for m, (ctor, ctor_pre) in zip(k.ctors, ctors):
        read_ctor(k, kc, ready, m, ctor, ctor_pre)
    for m, text in zip(k.methods, texts):
        body = BodyReader(k, kc, ready, method=m)
        m.body = body.stmt(text.body)
        m.fuel = body.count > 0 or body.calls_fuel
        ready[m.name] = m
        if text.pre:
            if m.name + "_pre" in ready:
                refuse(text.cursor, "a method named as another's precondition is")
            for v in (k.generic[1] if k.generic else []):
                named(v)
            for n, _ in m.params:
                named(n)
            m.pre = [BodyReader(k, kc, ready, method=m, plain=True).cond(c) for c in text.pre]
            if any(can_fail(c, True) for c in m.pre):
                refuse(text.pre[0], "a pre( condition ) that could fail to have a value (it reads an array, or calls)")
        named(m.name)
        for v in (k.generic[1] if k.generic else []):
            named(v)
        for n, _ in m.params:
            named(n)


def read_ctor(k, kc, ready, m, ctor, ctor_pre):
    """A constructor's initializer list, its body, and what it expects of its caller."""
    body = BodyReader(k, kc, ready, in_ctor=True, method=m)
    ctor_body = [c for c in ctor.get_children() if c.kind == CK.COMPOUND_STMT]
    if len(ctor_body) != 1:
        refuse(ctor, "a constructor with no body here")
    m.words = words(ctor_body[0])
    # The initializer list: FIELD( value ), or FIELD() for zeros. None may read a field (expr refuses
    # it in a constructor), so the order C++ runs them in does not matter.
    parts = [c for c in ctor.get_children() if c.kind not in (CK.COMPOUND_STMT, CK.PARM_DECL, CK.TYPE_REF, CK.NAMESPACE_REF)]
    while parts:
        c = parts.pop(0)
        if c.kind != CK.MEMBER_REF or c.spelling not in k.field:
            refuse(c, "an initializer that is not of a field of this class")
        f = k.field[c.spelling]
        init = parts.pop(0) if parts and parts[0].kind != CK.MEMBER_REF else None
        if f.buffer:
            m.inits.append(cxx.Init(named(f.name), None, place=where(c)))
            body.assigned.update((f.name, i) for i in range(f.count))
            continue
        zeros = init is None or (init.kind == CK.UNEXPOSED_EXPR and not list(init.get_children()))
        if isinstance(f.type, ClassT):      # a part, made by its constructor: what that expects is owed here
            made = unparen(init) if init is not None else None
            given = [x for x in made.get_children() if x.kind != CK.TYPE_REF] if made is not None and made.kind == CK.CALL_EXPR else None
            by = chosen(f.type, made, c)
            if any(isinstance(t, BytesT) for _, t in by.params):
                refuse(c, "a part made by a constructor that takes a view (not yet)")
            if given is None or len(given) != len(by.params):
                refuse(c, "a part that is not made by its constructor, `%s( ... )`, with every argument" % f.name)
            if by.throws:
                m.throws = True        # what a part's constructor throws, this one throws
            args = []
            for a, (_, t) in zip(given, f.type.params(by)):
                if int_of(a.type, a).width != t.width:
                    refuse(a, "an argument that is not the parameter's own type")
                args.append(body.expr(a))
            m.inits.append(cxx.Init(named(f.name), Made(f.type, args, ctor=by, place=where(init)), place=where(c)))
            body.assigned.add(f.name)
            continue
        if f.count is not None:
            if not zeros:
                refuse(c, "an array initialised by anything but `()`, which is zeros")
            m.inits.append(cxx.Init(named(f.name), None, place=where(c)))
            body.assigned.update((f.name, i) for i in range(f.count))
        else:
            if not zeros and not isinstance(f.type, GenT) and not (f.type.is_bool and k.generic) and int_of(init.type, init).width != f.type.width:
                refuse(init, "an initializer that is not the field's own type")
            given = None if zeros else Value(body.cond(init), place=where(init)) if f.type.is_bool and k.generic else body.expr(init)
            m.inits.append(cxx.Init(named(f.name), given, place=where(c)))
            body.assigned.add(f.name)
    m.body = body.stmt(ctor_body[0])
    for f in k.fields:
        missing = ([f.name] if f.count is None and f.name not in body.assigned else
                   ["%s[%d]" % (f.name, i) for i in range(f.count or 0) if (f.name, i) not in body.assigned])
        if missing:
            refuse(ctor, "the constructor does not assign %s: it would begin as anything" % ", ".join(missing))
    for n, _ in m.params:
        named(n)
    if ctor_pre:
        m.pre = [BodyReader(k, kc, ready, in_ctor=True, method=m).cond(c) for c in ctor_pre]
        if any(can_fail(c, False) for c in m.pre):
            refuse(ctor_pre[0], "a pre( condition ) that could fail to have a value (it reads an array, or calls)")


def chosen(u, call, at):
    """The constructor of `u` (a ClassT) that a call making a value of it calls, as Clang says."""
    if len(u.k.ctors) == 1:     # (of a class template, Clang names the constructor of the type it is made at)
        return u.k.ctors[0]
    ref = call.referenced if call is not None else None
    for m in u.k.ctors:
        if ref is not None and ref.get_usr() == m.usr:
            return m
    refuse(at, "a value of %s made by a constructor that is not read" % u.k.name)
