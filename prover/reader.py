"""The reader: Clang's cursors in, the tree of cxx.py out. Every question asked of Clang, and every
refusal, is here (and in subject.py and clang_edge.py); nothing here knows how Lean is written.

It reads in the order the generator always has, statement by statement in the order of the text,
so that of a class with several faults, the first refused is the one it always was.
"""

from clang.cindex import CursorKind as CK, TypeKind as TK

from clang_edge import where
from cxxtypes import (BytesT, ClassT, Int, first_token, is_bytes, is_gen, lean_name, not_checked,
                      outer_constant, plain_literal, refuse, tokens_after, typ, unparen)
from cxx import (Byte, Call, Cmp, Compl, Conv, Div, Elem, Lit, LNot, Logic, Name, NonZero,
                 OtherCall, Paren, Bin, Shift, Size, Truth, Value,
                 Block, Break, CallStmt, Compound, Continue, Decl, ForLoop, Ite, Memset, ObjDecl, Ret,
                 Seq, Set, Skip, Step, ViewDecl, WhileLoop)


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
        self.assigned = set()       # constructor only: fields, and (field, index) for array elements
        self.scope = [n for n, _ in method.params] if method else []     # the names a loop would carry
        self.loops = []             # the loops we are inside: the increment's cursor, or None
        self.count = 0              # the loops read
        self.in_block = 0           # inside a branch the model writes as a function of its own
        self.calls_fuel = False     # it calls a method that has a loop
        self.objects = {n: t for n, t in method.params if isinstance(t, ClassT)} if method else {}
        self.views = {n: n for n, t in method.params if isinstance(t, BytesT) and t.length and t.readable} if method else {}
        self.raw = {n for n, t in method.params if isinstance(t, BytesT) and t.length} if method else set()

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
            return Block([self.stmt(s) for s in c.get_children()], place=at)
        if k == CK.CALL_EXPR and c.spelling == "__builtin_assume":
            return Skip(place=at)       # a pre( condition ), written here by with_pre: it is the method's pre
        if self.in_ctor and k != CK.BINARY_OPERATOR:
            refuse(c, "the constructor may only assign each field once, in order")
        if k == CK.UNARY_OPERATOR and step_of(c) is not None:      # x++ or --x, its value not used
            lhs = list(c.get_children())[0]
            t = Int(lhs.type, lhs)
            if t.signed:
                refuse(c, "++ or -- of a signed number")
            self.expr(lhs)
            return Step(step_of(c) * 2, self.assign(lhs), t.width, place=at)
        if k == CK.COMPOUND_ASSIGNMENT_OPERATOR:
            lhs, rhs = list(c.get_children())
            op = tokens_after(c, lhs)
            t, tr = Int(lhs.type, lhs), Int(rhs.type, rhs)
            if op not in ("+=", "-=", "*=", "&=", "|=", "^=") or t.signed or t.width < 32 or (tr.width, tr.signed) != (t.width, False):
                refuse(c, "'%s' here: the two sides are one unsigned type of 32 bits or more, and the "
                          "operator is one of + - * & | ^" % op)
            self.expr(lhs)
            value = self.expr(rhs)
            return Compound(op, self.assign(lhs), value, place=at)
        if k == CK.CALL_EXPR and c.spelling == "memset":
            return self.memset(c)
        if k == CK.CALL_EXPR and self.own_call(c) is not None:
            return CallStmt(self.own_call(c), place=at)
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
                    u = self.used_class(v, vt)
                    init = [x for x in init if x.kind != CK.TEMPLATE_REF]
                    made = unparen(init[0]) if len(init) == 1 else None
                    given = list(made.get_children()) if made is not None and made.kind == CK.CALL_EXPR else None
                    if given is None or len(given) != len(u.k.ctor_params) or self.loops or self.in_block:
                        refuse(v, "a local of a class's type that is not made by its constructor, `%s %s( ... );`, "
                                  "outside any loop" % (u.k.name, v.spelling))
                    args = []
                    for a, (_, t) in zip(given, u.params()):
                        if Int(a.type, a).width != t.width:
                            refuse(a, "an argument that is not the parameter's own type")
                        args.append(self.expr(a))
                    self.objects[v.spelling] = u
                    decls.append(ObjDecl(named(v.spelling), u, args, place=where(v)))
                    continue
                if len(init) != 1:
                    refuse(v, "the local '%s' has no first value: it would begin as anything" % v.spelling)
                t = typ(self.k, v.type, v)
                value = self.expr(init[0])
                self.declare(v, v.spelling)
                decls.append(Decl(named(v.spelling), t, value, place=where(v)))
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
        if k == CK.BINARY_OPERATOR:
            lhs, rhs = list(c.get_children())
            if tokens_after(c, lhs) != "=":
                refuse(c, "an expression as a statement that is not an assignment")
            value = self.expr(rhs)
            return Set(self.assign(lhs), value, place=at)
        refuse(c, "%s (not in the spike's subset: no do-while, calls, switch, goto, throw, new or delete)"
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
        if (target.kind != CK.MEMBER_REF_EXPR or byte is None or not 0 <= byte <= 255 or size.kind != CK.CXX_UNARY_EXPR
                or [w for w in words if w not in "()"] != ["sizeof", target.spelling]):
            refuse(c, "a memset that is not memset( FIELD, BYTE, sizeof( FIELD ) ) of an array of this class")
        f = self.own_field(target)
        if f.count is None or self.in_ctor:
            refuse(c, "a memset of something that is not an array of this class")
        return Memset(named(f.name), byte, place=where(c))


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
    return k.ready
