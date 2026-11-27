"""The model: the tree of cxx.py in, the Lean model of the class out (CModel.lean). It asks nothing
of Clang and refuses nothing: what it is given was read, and checked, by reader.py.
"""

import re

from cxx import (Byte, Call, Cmp, Compl, Conv, Div, Elem, Lit, LNot, Logic, Name, NonZero,  # noqa: F401
                 OtherCall, Made, FieldDo, Paren, Bin, SignedBin, Shift, Size, Truth, Value,
                 Block, Break, CallStmt, Compound, Continue, Decl, ForLoop, Ite, Fill, Memcpy, Memset, ObjDecl, OutCall, OutDo, Ret,
                 Seq, Set, Skip, Step, Sub, Throw, End, ViewDecl, WhileLoop, walk)
from cxxtypes import OPTIONS, ClassT, GenT, binders, convert, lean_name, result_type


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
            if e.whole:         # of a fixed window, below its length: there by its type
                return "(Prooc.Bytes.byte %s %d)" % (lean_name(e.view), e.lit)
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
                                              ("me." if e.field else "") + lean_name(e.obj), "".join(" " + self.expr(a) for a in e.args))
        if isinstance(e, Sub):      # part of a view, handed on: none unless it is within
            return "(← Prooc.Bytes.sub %s %s (%s).toNat)" % (lean_name(e.view), "(%s).toNat" % self.expr(e.j) if e.j is not None else "0",
                                                              self.expr(e.n))
        if isinstance(e, Made):
            return "(← %s.%s%s%s)" % (e.klass.k.name, e.ctor.name, e.klass.ga, "".join(" " + self.expr(a) for a in e.args))
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
        if isinstance(e, SignedBin):
            return "(← Prooc.%s %s %s)" % ("sadd" if e.op == "+" else "ssub", self.expr(e.a), self.expr(e.b))
        if isinstance(e, OutCall):
            return "«outside»"        # its answer, taken before the statement it stands in (hoist)
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

    def say_return(self, value, outcome=None):
        if self.m.throws or self.m.ends:        # what it gives back is a Prooc.Outcome
            value = "." + outcome if outcome else "(.gave %s)" % value
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
                elif isinstance(x, (Memset, Memcpy, Fill, FieldDo)) or (isinstance(x, Call) and not x.method.const) or \
                        (isinstance(x, OutCall) and OPTIONS["outside"][x.name]["writes"]):
                    me = True
        return me, names

    def outlined(self, b):
        """Whether a branch becomes a function of its own: more than one statement, and no way out
        of it but its end. Small functions are what can be reasoned about: one large one cannot."""
        if self.in_ctor or getattr(self.k, "generic", None) or not isinstance(b, Block) or len(b.stmts) < 2:
            return False
        return not any(isinstance(x, (Break, Continue, Ret, Throw, End)) for x in walk(b))

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

    def term(self, call, t):
        """A number the contract says (a literal, a parameter, or PARAM-LIT, PARAM+LIT), as an Int,
        of the call's arguments."""
        m = re.match(r"^(-?\d+)$|^(\w+)(?:([+-])(\d+))?$", t)
        if m is None:
            raise TypeError("a number in a contract that is not a literal, a parameter, or PARAM-LIT: %s" % t)
        if m.group(1) is not None:
            return "(%s : Int)" % m.group(1)
        given = {p: v for p, kind, v in call.args if kind == "int"}
        e, signed = given[m.group(2)]
        base = "(%s).toInt" % self.expr(e) if signed else "((%s).toNat : Int)" % self.expr(e)
        return "(%s %s %s)" % (base, m.group(3), m.group(4)) if m.group(3) else base

    def hoist(self, nodes, pad, out):
        """A call of a function outside the program in these: taken first, as C++ takes it before the
        comparison or assignment it stands in. `none` where what it is handed breaks its contract;
        then what it writes, and its answer, are the world's."""
        calls = [x for top in nodes if top is not None for x in walk(top) if isinstance(x, OutCall)]
        for call in calls:
            contract = OPTIONS["outside"][call.name]
            sizes = {}
            for p, kind, place in call.args:
                if kind in ("read", "write"):
                    field, view, k = place
                    size = "(%d : Int)" % self.k.field[field].count if field else "((Prooc.Bytes.size %s).toNat : Int)" % lean_name(view)
                    off = "((%s).toNat : Int)" % self.expr(k) if k is not None else "(0 : Int)"
                    sizes[p] = (field, off, size)
            ok = []
            for p, count in contract["reads"] + contract["writes"]:
                field, off, size = sizes[p]
                n = self.term(call, count)
                ok.append("0 ≤ %s ∧ %s + %s ≤ %s" % (n, off, n, size))
            width, signed = call.result if call.result else (8, False)
            if call.result is None:
                answer = "()"
            elif contract["gives"]:
                answer = "(Prooc.pick %d %s %s (world 0))" % (width, self.term(call, contract["gives"][0]), self.term(call, contract["gives"][1]))
            else:
                answer = "((world 0).setWidth %d)" % width
            out.append("%slet «outside» ← Prooc.outside (%s) %s" % (pad, " ∧ ".join("(%s)" % x for x in ok) or "True", answer))
            for p, count in contract["writes"]:
                field, off, size = sizes[p]
                out.append("%sme := { me with %s := Prooc.scribble me.%s (%s).toNat (%s).toNat world }"
                           % (pad, lean_name(field), lean_name(field), off, self.term(call, count)))

    def stmts(self, s, depth, out):
        pad = "  " * depth
        if isinstance(s, (Decl, Set, Compound, Ret, OutDo)):
            self.hoist([getattr(s, "value", None), getattr(s, "call", None)], pad, out)
        elif isinstance(s, Ite):
            self.hoist([s.c], pad, out)
        elif isinstance(s, End) and s.c is not None:
            self.hoist([s.c], pad, out)
        if isinstance(s, Block):
            n = len(out)
            for x in s.stmts:
                self.stmts(x, depth, out)
            if len(out) == n:
                out.append(pad + "pure ()")
        elif isinstance(s, Seq):
            for x in s.stmts:
                self.stmts(x, depth, out)
        elif isinstance(s, (Skip, ViewDecl, OutDo)):
            pass
        elif isinstance(s, Step):
            self.assign(s.target, "(%s %s 1#%d)" % (self.expr(s.target), s.op[0], s.width), pad, out)
        elif isinstance(s, Compound):
            lean = {"+=": "+", "-=": "-", "*=": "*", "&=": "&&&", "|=": "|||", "^=": "^^^"}[s.op]
            self.assign(s.target, "(%s %s %s)" % (self.expr(s.target), lean, self.expr(s.value)), pad, out)
        elif isinstance(s, Memcpy):
            k = "(%s).toNat" % self.expr(s.k) if s.k is not None else "0"
            j = "(%s).toNat" % self.expr(s.j) if s.j is not None else "0"
            how = "copyOwn" if s.src_field or s.src_obj else "copyIn"
            what = ("%s.%s" % (lean_name(s.src_obj[0]), lean_name(s.src_obj[1])) if s.src_obj else
                    "me.%s" % lean_name(s.src_field) if s.src_field else lean_name(s.src_view))
            out.append("%sme := { me with %s := (← Prooc.%s me.%s %s %s %s (%s).toNat) }"
                       % (pad, lean_name(s.field), how, lean_name(s.field), k, what, j, self.expr(s.n)))
        elif isinstance(s, Fill):
            k = "(%s).toNat" % self.expr(s.k) if s.k is not None else "0"
            out.append("%sme := { me with %s := (← Prooc.fill me.%s %s %d#8 (%s).toNat) }"
                       % (pad, lean_name(s.field), lean_name(s.field), k, s.byte, self.expr(s.n)))
        elif isinstance(s, Memset):
            f = self.k.field[s.field]
            value = sum(s.byte << (8 * i) for i in range(f.type.width // 8))
            out.append("%sme := { me with %s := Vector.replicate %d %d#%d }" % (pad, lean_name(f.name), f.count, value, f.type.width))
        elif isinstance(s, CallStmt):
            call = self.call(s.call)
            out.append("%sme := (← %s).1" % (pad, call) if not s.call.method.const else "%slet _ ← %s" % (pad, call))
        elif isinstance(s, FieldDo):        # the part becomes what its method leaves it
            out.append("%sme := { me with %s := (← %s.%s%s%s me.%s%s).1 }"
                       % (pad, lean_name(s.field), s.klass.k.name, lean_name(s.method.name), s.klass.ga,
                          " ‹FUEL›" if s.method.fuel else "", lean_name(s.field), "".join(" " + self.expr(a) for a in s.args)))
        elif isinstance(s, ObjDecl):
            made = "%s.%s%s%s" % (s.klass.k.name, s.ctor.name, s.klass.ga, "".join(" " + self.expr(a) for a in s.args))
            if s.ctor.throws:       # what it throws, this throws: it is not caught
                out.append("%slet .gave %s ← %s | %s" % (pad, lean_name(s.x), made, self.say_return(None, "thrown")))
            else:
                out.append("%slet %s ← %s" % (pad, lean_name(s.x), made))
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
        elif isinstance(s, Throw) and self.in_ctor:     # no object is made
            out.append(pad + "return .thrown")
        elif isinstance(s, Throw):      # the state as it is: what is owed says it keeps the invariant
            out.append(pad + self.say_return(None, "thrown"))
        elif isinstance(s, End):        # nothing runs after it: the state it leaves is not looked at
            if s.c is None:
                out.append(pad + self.say_return(None, "ended"))
            else:
                out.append(pad + self.if_line(s.c, negate=True))
                out.append(pad + "  " + self.say_return(None, "ended"))
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


# ---------------------------------------------------------------------------
# The model of a class
# ---------------------------------------------------------------------------

def field_type(f):
    """A field's type, in Lean."""
    if f.count is None:
        return f.type.lean()
    return "Vector (%s) %d" % (f.type.lean(), f.count)


def field_zero(f):
    """A field's value before the constructor has run."""
    if isinstance(f.type, ClassT):
        return "%s.raw" % f.type.k.name      # a part's storage before its constructor has run
    if isinstance(f.type, GenT):
        return "default"        # storage of a type of which nothing is known: any value of it
    z = "0#%d" % f.type.width
    return z if f.count is None else "Vector.replicate %d %s" % (f.count, z)


def pre_def(k, name, bound, conds, of, tested=False):
    """What a method expects of its caller, as a Prop of the state and the arguments. The method's
    model is `none` where it is not so: so a caller that is proved safe has kept it. Or, of a way
    in for code that is not proved, what it tests: the process ends where it is not so. (Each
    condition is pure: the reader refused one that could fail to have a value.)"""
    names = " ".join(re.findall(r"\((\w+) :", bound))
    return ["/-- WHAT IS TESTED, when the program runs, at the head of %s: the process ends, saying who called, if it is not so. -/" % of.replace("`pre(...)`", "`STRONG_CHECK`") if tested else
            "/-- WHAT IS EXPECTED OF THE CALLER of %s. Not checked when the program runs: owed by whoever calls. -/" % of,
            "def %s_pre%s : Prop := %s" % (name, bound, " ∧ ".join(t for t, _ in conds)), "",
            "instance%s : Decidable (%s_pre %s) := by unfold %s_pre; infer_instance" % (bound, name, names, name), ""]


def emit_ctor(k, c):
    """A constructor's model (`c` a Method; None for a function's): `new`, or its own name."""
    name = c.name if c else "new"
    body = Writer(k, in_ctor=True)
    lines, L = [], []
    throws = c is not None and c.throws
    for i in (c.inits if c else []):
        f = k.field[i.field]
        if isinstance(i.value, Made) and i.value.ctor.throws:     # what the part's constructor throws, this throws
            made = "%s.%s%s%s" % (i.value.klass.k.name, i.value.ctor.name, i.value.klass.ga, "".join(" " + body.expr(a) for a in i.value.args))
            lines += ["  let .gave «%s» ← %s | return .thrown" % (f.name, made),
                      "  me := { me with %s := «%s» }" % (lean_name(f.name), f.name)]
            continue
        lines.append("  me := { me with %s := %s }" % (lean_name(f.name), field_zero(f) if i.value is None else body.expr(i.value)))
    if c is not None and c.body is not None:
        body.stmts(c.body, 1, lines)
    if lines and lines[-1].strip() == "pure ()":
        lines.pop()
    params = c.params if c else []
    cb = "".join(" (%s : %s)" % (lean_name(n), t.lean()) for n, t in params)
    ca = "".join(" " + lean_name(n) for n, _ in params)
    must = []
    if c is not None and c.pre:
        L += pre_def(k, name, k.gb + cb, [Writer(k, in_ctor=True).cond(x) for x in c.pre],
                     "the constructor%s: `pre(...)`" % ("" if len(k.ctors) == 1 else " `%s`" % name), c.tested)
        must = ["  let _ ← (if %s.%s_pre%s%s then some () else none)" % (k.name, name, k.ga, ca)]
    made = "(%s)" % k.lt if k.generic else k.name
    if throws:      # it may throw: then no object is made (Prooc.Outcome.thrown)
        L += ["/-- The constructor may throw: what it gives back is the object made, or that it threw. -/"]
    L += ["def %s%s%s : Option %s := do" % (name, k.gb, cb, "(Prooc.Outcome %s)" % made if throws else made),
          "  let mut me := %s" % ("%s.raw%s" % (k.name, k.ga) if params or k.generic else "raw")] + must + lines + [
          "  return .gave me" if throws else "  return me", ""]
    return L


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
        L.append("  %s : %s" % (lean_name(f.name), field_type(f)))
    inv, pure = Writer(k, plain=True).cond(k.inv) if k.inv is not None else ("True", True)
    if not pure:        # it calls a part's const method: that it has a value, and the value is true
        inv = "(%s) = some true" % inv
    parts = [f for f in k.fields if isinstance(f.type, ClassT)]
    if parts:           # each part keeps its own invariant, which its own proof shows of its methods
        inv = " ∧ ".join([f.type.inv("me." + lean_name(f.name)) for f in parts] + ["(%s)" % inv])
    L += ["", "namespace %s" % k.name, "",
          ("/-- THE INVARIANT, as the class says it: `invariant()` in %s; and first, that each part (%s)\n"
           "keeps its own. -/" % (src, ", ".join("`%s`, a %s" % (f.name, f.type.k.name) for f in parts))) if k.inv is not None and parts else
          "/-- THE INVARIANT, as the class says it: `invariant()` in %s. -/" % src if k.inv is not None else
          "/-- A function has no state: there is nothing for an invariant to say (%s). -/" % src if k.is_function else
          "/-- The class in %s says NO INVARIANT (it has no `bool invariant() const`): nothing is claimed\n"
          "of its state, and what is owed of it is memory and ending alone. -/" % src,
          "def Inv%s (me : %s) : Prop := %s" % (k.gb, k.lt, inv), "",
          "instance%s (me : %s) : Decidable (Inv%s me) := by unfold Inv; infer_instance" % (k.gb, k.lt, k.ga), "",
          "/-- Storage before the constructor has run. The constructor assigns every field, and reads none",
          "(the generator checked), so nothing depends on these values. -/",
          "def raw%s : %s := { %s }" % (k.gb, k.lt, ", ".join("%s := %s" % (lean_name(f.name), field_zero(f)) for f in k.fields)) if k.fields
          else "def raw%s : %s := {}" % (k.gb, k.lt),
          ""]
    if k.only:
        L += ["/-- The class is read for some of its methods only (`only`): its constructor is not read, and",
              "what is owed of each method read holds from any state. -/", ""]
    else:
        for c in k.ctors or [None]:     # (a function is read as a class with no state: made by `new`, of nothing)
            L += emit_ctor(k, c)
    for m in k.methods:
        lines = []
        body = Writer(k, method=m)
        body.stmts(m.body, 1, lines)
        fuel = "fuel" if m.fuel else "0"
        lines = [x.replace("‹FUEL›", fuel) for x in lines]
        L += [x.replace("‹FUEL›", "fuel") for x in body.defs]
        if m.pre:
            L += pre_def(k, m.name, k.gb + " (me : %s)%s" % (k.lt, binders(m)),
                         [Writer(k, method=m, plain=True).cond(c) for c in m.pre], "`%s`: `pre(...)`" % m.name, m.tested)
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
        if not m.body.stmts or not isinstance(m.body.stmts[-1], (Ret, Throw)) and not (isinstance(m.body.stmts[-1], End) and m.body.stmts[-1].c is None):
            L.append(("  return (me, .gave ())" if m.throws or m.ends else "  return (me, ())") if m.result is None else
                     "  none  -- the C++ falls off the end: undefined")
        L.append("")
    L.append("end %s" % k.name)
    return "\n".join(L) + "\n"
