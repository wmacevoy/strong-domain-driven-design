"""The model: the tree of cxx.py in, the Lean model of the class out (CModel.lean). It asks nothing
of Clang and refuses nothing: what it is given was read, and checked, by reader.py.
"""

from cxx import (Byte, Call, Cmp, Compl, Conv, Div, Elem, Lit, LNot, Logic, Name, NonZero,  # noqa: F401
                 OtherCall, Paren, Bin, Shift, Size, Truth, Value,
                 Block, Break, CallStmt, Compound, Continue, Decl, ForLoop, Ite, Memset, ObjDecl, Ret,
                 Seq, Set, Skip, Step, ViewDecl, WhileLoop, walk)
from cxxtypes import convert, lean_name, result_type


class Writer:
    """A method's statements, the constructor's, or the invariant, as Lean text: the lines of a
    `do` block in Option."""

    def __init__(self, klass, in_ctor=False, method=None, plain=False):
        self.k = klass
        self.in_ctor = in_ctor
        self.plain = plain          # the invariant: a condition on the fields, which cannot fail
        self.m = method
        self.scope = [(n, t.lean()) for n, t in method.params] if method else []   # locals a loop carries
        self.loops = []             # the loops we are inside: (tuple text, increment or None)
        self.defs = []              # the loops' and blocks' own functions, innermost first
        self.count = 0
        self.blocks = 0
        self.in_block = 0

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

    def say_return(self, value):
        return "return .ret (me, %s)" % value if self.loops else "return (me, %s)" % value

    def changed_in(self, nodes):
        """What statements assign: (whether the object, the names of locals and parameters)."""
        me, names = False, set()
        for top in nodes:
            if top is None:
                continue
            for x in walk(top):
                if isinstance(x, (Set, Compound, Step)):
                    if isinstance(x.target, Name) and x.target.what != "field":
                        names.add(x.target.x)
                    else:
                        me = True
                elif isinstance(x, Memset) or (isinstance(x, Call) and not x.method.const):
                    me = True
        return me, names

    def outlined(self, b):
        """Whether a branch becomes a function of its own: more than one statement, and no way out
        of it but its end. Small functions are what can be reasoned about: one large one cannot."""
        if self.in_ctor or getattr(self.k, "generic", None) or not isinstance(b, Block) or len(b.stmts) < 2:
            return False
        return not any(isinstance(x, (Break, Continue, Ret)) for x in walk(b))

    def outline(self, b, depth, out):
        pad = "  " * depth
        mark = len(self.scope)
        me_changed, names = self.changed_in([b])
        state = [(n, t) for n, t in self.scope if n in names]
        state_names = (["me"] if me_changed else []) + [lean_name(n) for n, _ in state]
        types = ([self.k.name] if me_changed else []) + [t for _, t in state]
        self.blocks += 1
        name = "%s.block%d" % (lean_name(self.m.name), self.blocks)
        binders = " (me : %s)" % self.k.name + "".join(" (%s : %s)" % (lean_name(n), t) for n, t in self.scope)
        args = " ".join(["me"] + [lean_name(n) for n, _ in self.scope])
        B = ["/-- A branch of `%s` (%s): what it changes. -/" % (self.m.name, b.place),
             "def %s (fuel : Nat)%s : Option (%s) := do" % (name, binders, " × ".join(types) or "Unit"),
             "  let mut me := me"]
        B += ["  let mut %s := %s" % (lean_name(n), lean_name(n)) for n, _ in state]
        loops, self.loops = self.loops, []
        self.in_block += 1
        self.stmts(b, 1, B)
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

    def branch(self, b, depth, out):
        if self.outlined(b):
            self.outline(b, depth, out)
        else:
            self.block(b, depth, out)

    def loop(self, s, depth, out, init, cond, inc, body):
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
        B = ["/-- One round of a loop of `%s` (%s). -/" % (self.m.name, s.place),
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

    def stmts(self, s, depth, out):
        pad = "  " * depth
        if isinstance(s, Block):
            n = len(out)
            for x in s.stmts:
                self.stmts(x, depth, out)
            if len(out) == n:
                out.append(pad + "pure ()")
        elif isinstance(s, Seq):
            for x in s.stmts:
                self.stmts(x, depth, out)
        elif isinstance(s, (Skip, ViewDecl)):
            pass
        elif isinstance(s, Step):
            self.assign(s.target, "(%s %s 1#%d)" % (self.expr(s.target), s.op[0], s.width), pad, out)
        elif isinstance(s, Compound):
            lean = {"+=": "+", "-=": "-", "*=": "*", "&=": "&&&", "|=": "|||", "^=": "^^^"}[s.op]
            self.assign(s.target, "(%s %s %s)" % (self.expr(s.target), lean, self.expr(s.value)), pad, out)
        elif isinstance(s, Memset):
            f = self.k.field[s.field]
            value = sum(s.byte << (8 * i) for i in range(f.type.width // 8))
            out.append("%sme := { me with %s := Vector.replicate %d %d#%d }" % (pad, lean_name(f.name), f.count, value, f.type.width))
        elif isinstance(s, CallStmt):
            call = self.call(s.call)
            out.append("%sme := (← %s).1" % (pad, call) if not s.call.method.const else "%slet _ ← %s" % (pad, call))
        elif isinstance(s, ObjDecl):
            out.append("%slet %s ← %s.new%s%s" % (pad, lean_name(s.x), s.klass.k.name, s.klass.ga,
                                                  "".join(" " + self.expr(a) for a in s.args)))
        elif isinstance(s, Decl):
            value = self.expr(s.value)
            self.scope.append((s.x, s.type.lean()))
            out.append("%slet mut %s : %s := %s" % (pad, lean_name(s.x), s.type.lean(), value))
        elif isinstance(s, Ite):
            out.append(pad + self.if_line(s.c))
            self.branch(s.then, depth + 1, out)
            if s.other is not None:
                out.append(pad + "else")
                self.branch(s.other, depth + 1, out)
        elif isinstance(s, Ret) and isinstance(s.value, Call):
            call = self.call(s.value)       # `return method( ... );`: its state, then its answer
            out.append("%slet «called» ← %s" % (pad, call))
            if not s.value.method.const:
                out.append("%sme := «called».1" % pad)
            out.append(pad + self.say_return("«called».2"))
        elif isinstance(s, Ret):
            out.append(pad + self.say_return(self.expr(s.value) if s.value is not None else "()"))
        elif isinstance(s, WhileLoop):
            self.loop(s, depth, out, None, s.c, None, s.body)
        elif isinstance(s, ForLoop):
            self.loop(s, depth, out, s.init, s.c, s.inc, s.body)
        elif isinstance(s, Break):
            out.append("%sreturn .done %s" % (pad, self.loops[-1][0]))
        elif isinstance(s, Continue):
            if self.loops[-1][1] is not None:
                self.stmts(self.loops[-1][1], depth, out)
            out.append("%sreturn .next %s" % (pad, self.loops[-1][0]))
        elif isinstance(s, Set):
            self.assign(s.target, self.expr(s.value), pad, out)
        else:
            raise TypeError("not a statement of the tree: %r" % (s,))

    def assign(self, target, value, pad, out):
        if isinstance(target, Name) and target.what != "field":
            out.append("%s%s := %s" % (pad, lean_name(target.x), value))
        elif isinstance(target, Name):
            out.append("%sme := { me with %s := %s }" % (pad, lean_name(target.x), value))
        else:
            out.append("%sme := { me with %s := (← Prooc.set me.%s %s (%s)) }"
                       % (pad, lean_name(target.field), lean_name(target.field), self.index(target), value))

    def block(self, b, depth, out):
        n = len(out)
        mark = len(self.scope)
        self.stmts(b, depth, out)
        del self.scope[mark:]
        if len(out) == n:
            out.append("  " * depth + "pure ()")
