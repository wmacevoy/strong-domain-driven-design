"""The model: the tree of cxx.py in, the Lean model of the class out (CModel.lean). It asks nothing
of Clang and refuses nothing: what it is given was read, and checked, by reader.py.
"""

from cxx import (Byte, Call, Cmp, Compl, Conv, Div, Elem, Lit, LNot, Logic, Name, NonZero,  # noqa: F401
                 OtherCall, Paren, Bin, Shift, Size, Truth, Value)
from cxxtypes import convert, lean_name


class Writer:
    """A method's statements, the constructor's, or the invariant, as Lean text: the lines of a
    `do` block in Option."""

    def __init__(self, klass, in_ctor=False, method=None, plain=False):
        self.k = klass
        self.in_ctor = in_ctor
        self.plain = plain          # the invariant: a condition on the fields, which cannot fail
        self.m = method

    # ---- expressions

    def call(self, e):
        """The Lean text of a call of a method of this class."""
        m = e.method
        return "%s.%s%s%s me%s" % (self.k.name, lean_name(m.name), self.k.ga, " ‹FUEL›" if m.fuel else "",
                                   "".join(" " + self.expr(a) for a in e.args))

    def truth(self, c):
        """A condition as a value: a bool, 1 or 0."""
        text, pure = self.cond(c)
        return "(if %s then 1#8 else 0#8)" % (text if pure else "(← %s)" % text)

    def expr(self, e):
        """Lean text of an integer expression, a BitVec of its width."""
        if isinstance(e, Lit):
            return "%d#%d" % (e.value, e.width)
        if isinstance(e, Truth):
            return "1#8" if e.value else "0#8"
        if isinstance(e, Name):
            return "me.%s" % lean_name(e.x) if e.what == "field" else lean_name(e.x)
        if isinstance(e, Paren):
            return "(%s)" % self.expr(e.e)
        if isinstance(e, Conv):
            return convert(self.expr(e.e), e.src, e.dst)
        if isinstance(e, Size):
            return "(Prooc.Bytes.size %s)" % lean_name(e.view)
        if isinstance(e, Byte):
            if e.lit is not None:
                return "(← Prooc.Bytes.read %s %d)" % (lean_name(e.view), e.lit)
            return "(← Prooc.Bytes.read %s (%s).toNat)" % (lean_name(e.view), self.expr(e.index))
        if isinstance(e, Elem):
            if self.plain:
                return "me.%s[%d]" % (lean_name(e.field), e.lit)
            return "(← Prooc.get me.%s %s)" % (lean_name(e.field), self.index(e))
        if isinstance(e, OtherCall):
            m = e.method
            return "((← %s.%s%s%s %s%s)).2" % (e.klass.k.name, lean_name(m.name), e.klass.ga, " ‹FUEL›" if m.fuel else "",
                                              lean_name(e.obj), "".join(" " + self.expr(a) for a in e.args))
        if isinstance(e, Call):
            return "((← %s)).2" % self.call(e)
        if isinstance(e, Value):
            return self.truth(e.c)
        if isinstance(e, Div):
            if e.known:
                return "(%s %s %s)" % (self.expr(e.a), e.op, self.expr(e.b))
            return "(← Prooc.%s %s %s)" % ("div" if e.op == "/" else "mod", self.expr(e.a), self.expr(e.b))
        if isinstance(e, Shift):
            if e.amount is not None:
                return "(%s %s %d)" % (self.expr(e.a), "<<<" if e.op == "<<" else ">>>", e.amount)
            return "(← Prooc.%s %s (%s).toNat)" % ("shl" if e.op == "<<" else "shr", self.expr(e.a), self.expr(e.b))
        if isinstance(e, Bin):
            return "(%s %s %s)" % (self.expr(e.a), {"&": "&&&", "|": "|||", "^": "^^^"}.get(e.op, e.op), self.expr(e.b))
        if isinstance(e, Compl):
            return "(~~~%s)" % self.expr(e.e)
        raise TypeError("not an expression of the tree: %r" % (e,))

    def index(self, e):
        """An element's index, as a Nat."""
        return str(e.lit) if e.lit is not None else "(%s).toNat" % self.expr(e.index)

    def cond(self, c):
        """A condition: (text, pure). Pure text is a decidable Prop. Text that is not pure is an
        Option Bool: a condition that reads memory, kept in C++'s order, so that the right side of
        && or || is not read when the left decides."""
        if isinstance(c, Truth):
            return ("True" if c.value else "False"), True
        if isinstance(c, NonZero):
            return self.leaf("(%s ≠ 0#%d)" % (self.expr(c.e), c.width))
        if isinstance(c, LNot):
            text, pure = self.cond(c.c)
            return ("(¬ %s)" % text, True) if pure else ("(do pure (!(← %s)))" % text, False)
        if isinstance(c, Logic):
            (x, px), (y, py) = self.cond(c.a), self.cond(c.b)
            if px and py:
                return "(%s %s %s)" % (x, "∧" if c.op == "&&" else "∨", y), True
            x = "(pure (decide %s))" % x if px else x
            y = "(pure (decide %s))" % y if py else y
            if c.op == "&&":
                return "(do if (← %s) then %s else pure false)" % (x, y), False
            return "(do if (← %s) then pure true else %s)" % (x, y), False
        if isinstance(c, Cmp):
            x, y = self.expr(c.a), self.expr(c.b)
            if c.op == "==":
                return self.leaf("(%s = %s)" % (x, y))
            if c.op == "!=":
                return self.leaf("(%s ≠ %s)" % (x, y))
            if c.signed:
                f = {"<": "BitVec.slt %s %s", "<=": "BitVec.sle %s %s",
                     ">": "BitVec.slt %s %s", ">=": "BitVec.sle %s %s"}[c.op]
                return self.leaf("(%s = true)" % (f % ((x, y) if c.op in ("<", "<=") else (y, x))))
            return self.leaf("(%s %s %s)" % (x, {"<": "<", "<=": "≤", ">": ">", ">=": "≥"}[c.op], y))
        raise TypeError("not a condition of the tree: %r" % (c,))

    def leaf(self, prop):
        if "←" in prop:
            return "(do pure (decide %s))" % prop, False
        return prop, True

    def if_line(self, c, negate=False):
        text, pure = self.cond(c)
        if pure:
            return "if %s%s then" % ("¬ " if negate else "", text)
        return "if %s(← %s) then" % ("!" if negate else "", text)
