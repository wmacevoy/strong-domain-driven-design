"""The reader: Clang's cursors in, the tree of cxx.py out. Every question asked of Clang, and every
refusal, is here (and in subject.py and clang_edge.py); nothing here knows how Lean is written.

It reads in the order the generator always has, statement by statement in the order of the text,
so that of a class with several faults, the first refused is the one it always was.
"""

from clang.cindex import CursorKind as CK, TypeKind as TK

from clang_edge import where
from cxxtypes import (BytesT, ClassT, Int, first_token, is_bytes, is_gen, lean_name, not_checked,
                      outer_constant, plain_literal, refuse, tokens_after, unparen)
from cxx import (Byte, Call, Cmp, Compl, Conv, Div, Elem, Lit, LNot, Logic, Name, NonZero,
                 OtherCall, Paren, Bin, Shift, Size, Truth, Value)


def named(name):
    """A name the model will be written with: refused if it is one of the model's own. Asked where
    the generator, when it wrote as it read, first wrote the name, so that the same name is refused
    first."""
    lean_name(name)
    return name


class BodyReader:
    """A method's body, the constructor's, or the invariant, read into the tree."""

    def __init__(self, klass, kc, ready, in_ctor=False, method=None, plain=False):
        self.k = klass
        self.kc = kc                # the class's cursor, or None for a function
        self.ready = ready          # the methods read before this one, by name: what a call may name
        self.in_ctor = in_ctor
        self.plain = plain          # the invariant or a precondition: a condition on the fields, which cannot fail
        self.m = method
        self.calls_fuel = False     # it calls a method that has a loop
        self.objects = {n: t for n, t in method.params if isinstance(t, ClassT)} if method else {}
        self.views = {n: n for n, t in method.params if isinstance(t, BytesT) and t.length and t.readable} if method else {}

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
        """Elem, for an ARRAY_SUBSCRIPT_EXPR on one of the class's own arrays."""
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
            if isinstance(t, BytesT) or Int(a.type, a).width != t.width:
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
        base = [unparen(x) for x in parts[0].get_children()]
        if len(base) != 1 or base[0].kind != CK.DECL_REF_EXPR or base[0].spelling not in self.objects:
            return None
        ct = self.objects[base[0].spelling]
        k = ct.k
        ref = parts[0].referenced
        m = ready_of(k).get(ref.spelling) if ref is not None and ref.kind == CK.CXX_METHOD else None
        if m is None or not m.const or not m.public or m.result is None or len(parts) - 1 != len(m.params):
            refuse(c, "a call on a parameter that is not to a public const method of its class that gives a number")
        given = []
        for a, (_, t) in zip(parts[1:], m.params):
            t = ct.of(t)
            if not isinstance(t, Int) or Int(a.type, a).width != t.width:
                refuse(a, "an argument that is not the parameter's own type")
            given.append(self.expr(a))
        if m.fuel:
            self.calls_fuel = True
        named(m.name)
        return OtherCall(named(base[0].spelling), ct, m, given, place=where(c))

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
            t = Int(c.type, c)
            return Lit(self.literal(c), t.width, place=at)
        if k == CK.PAREN_EXPR:
            return Paren(self.expr(list(c.get_children())[0]), place=at)
        if k in (CK.UNEXPOSED_EXPR, CK.CSTYLE_CAST_EXPR, CK.CXX_STATIC_CAST_EXPR, CK.CXX_FUNCTIONAL_CAST_EXPR):
            inner = [x for x in c.get_children() if x.kind != CK.TYPE_REF]
            if len(inner) != 1:
                refuse(c, "an expression the generator does not know")
            dst = Int(c.type, c)
            lit = self.literal(inner[0])
            if lit is not None and dst.is_bool:
                return Lit(1 if lit else 0, 8, place=at)
            if lit is not None:
                return Lit(lit % (1 << dst.width), dst.width, place=at)     # a literal, converted here
            e = self.expr(inner[0])
            return Conv(Int(inner[0].type, inner[0]), dst, e, place=at)
        if k == CK.CXX_BOOL_LITERAL_EXPR:
            return Truth(first_token(c) == "true", place=at)
        if k == CK.DECL_REF_EXPR and self.constant(c) is not None:
            return Lit(self.constant(c), Int(c.type, c).width, place=at)
        if (k == CK.DECL_REF_EXPR and self.m is not None and c.spelling in self.m.lengths
                and c.referenced is not None and c.referenced.kind == CK.PARM_DECL):
            return Size(named(self.m.lengths[c.spelling]), place=at)     # a view's length, by its name
        if k == CK.DECL_REF_EXPR:
            ref = c.referenced
            if ref is None or ref.kind not in (CK.VAR_DECL, CK.PARM_DECL) or ref.semantic_parent.kind == CK.TRANSLATION_UNIT:
                refuse(c, "a name that is not a local or a parameter (a global is state outside the class)")
            Int(c.type, c)
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
            if Int(index.type, index).signed:
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
                if len(parts) != 1 or Int(c.type, c).width != 64:
                    refuse(c, "size() takes nothing and gives 64 bits")
                return Size(name, place=at)
            if len(parts) != 2:
                refuse(c, "at() takes one unsigned index")
            lit = self.literal(parts[1])
            if lit is not None and lit >= 0:       # as `p[4]` is read
                return Byte(name, None, lit, place=at)
            if Int(parts[1].type, parts[1]).signed:
                refuse(c, "at() takes one unsigned index")
            return Byte(name, self.expr(parts[1]), None, place=at)
        if k == CK.BINARY_OPERATOR:
            a, b = list(c.get_children())
            op = tokens_after(c, a)
            if op in ("<", "<=", ">", ">=", "==", "!=", "&&", "||"):
                return Value(self.cond(c), place=at)
            t = Int(c.type, c)
            if op in ("/", "%"):
                if t.signed or Int(a.type, a).width != t.width or Int(b.type, b).width != t.width:
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
                if Int(b.type, b).signed:
                    refuse(c, "a shift by a signed amount (it could be negative, which is undefined): "
                              "use an unsigned one of 32 bits or more")
                if self.plain:
                    refuse(c, "a shift in the invariant by an amount that is not a literal")
                x = self.expr(a)
                return Shift(op, x, self.expr(b), None, place=at)
            if op in ("&", "|", "^"):
                x = self.expr(a)
                return Bin(op, x, self.expr(b), place=at)
            if op in ("+", "-", "*"):
                if t.signed:
                    refuse(c, "'%s' on signed numbers can overflow, which is undefined: make them unsigned" % op)
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
            return self.cond(list(c.get_children())[0])
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
            return NonZero(e, Int(inner.type, inner).width, place=at)
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
                ta, tb = Int(a.type, a), Int(b.type, b)
                if (ta.width, ta.signed) != (tb.width, tb.signed):
                    refuse(c, "a comparison of two different types")
                x = self.expr(a)
                return Cmp(op, x, self.expr(b), ta.signed, place=at)
        if c.type.get_canonical().kind == TK.BOOL and k in (CK.DECL_REF_EXPR, CK.MEMBER_REF_EXPR, CK.CALL_EXPR):
            return NonZero(self.expr(c), 8, place=at)
        refuse(c, "a condition the generator does not know (comparisons, !, && and ||)")


def ready_of(k):
    """The methods of a class read whole, by name: what a call on a value of it may name."""
    return k.ready
