#!/usr/bin/env python3
"""
proofs -- what is claimed of a class, written as a test that cannot be run, made what is owed.

    python3 proofs.py proofs/C.proof.cpp --class C -o gen [-I dir]...      writes gen/CProofOwed.lean

The file is C++ (model/forall.h makes it compile): each `PROOF( name ) { ... }` is a test of the
class C that steps through every value of its loops' types, so nobody can run it. This reads it
as it would run, and writes in Lean what must be proved for every PROVE in it to hold in every
round: `C Proof.Owed`, over the model prooc.py made of the class (gen/CModel.lean). A claims
file proves that, and is audited as any other (prove.sh).

What a loop is made into. A loop over every x cannot be followed round by round, so it is proved
by what holds from one round to the next:
  - at the loop: the class's invariant holds, and so does each "carried" condition: a conjunct of
    the PROVEs that end the loop's body which does not name the loop's own variable;
  - one statement per loop: from ANY state of which those hold, for every x, the body's PROVEs
    hold, and at its end those hold again;
  - after the loop: the state is any of which those hold, and no more is known.
So each PROVE holds in every round, by induction on the rounds. An object made inside a loop is
new in each round, and nothing is carried. A round of a loop is a round of every loop around
it: what those say of their variables (`all<T>( a, b )`) is given in its statement too.

A proof is of a set of domains: the class whose file it is, and every domain proved before it in
the same run (prove.sh hands them on, `--with`). So it may make objects of any class of the set,
each once, and call any function of the set in a condition, or to make what a method is handed;
a statement about a loop then holds of every object made before it, each from any state its own
invariant allows. The file imports the models of the domains it uses, and no others.

It reads a subset, and refuses the rest, saying where: objects of the set's classes, each made by
`C name;` or `C name( ... );`; `for ( T x : all<T>() )` and `all<T>( a, b )` with T an unsigned
integer and a, b literals; `for ( const std::vector<unsigned char>& b : every_bytes() )`, every
sequence of bytes of every length; calls of an object's methods with arguments that are loop
variables, literals, what a const method of an object that takes nothing gives, or what a function
of the set gives; or a window on such bytes (`W( b.data(), b.size() )`, for a parameter that
is a Strong::subarray or a Bytes). A call says that the method ends and commits no memory error:
where its model takes `fuel`, that some number of rounds is enough; `PROVE( condition )`, a condition of comparisons, `&&`, `||`, `!`, `?:`, the
objects' const methods that take nothing, a function of the set, and `invariant()`.

proofs_reader.py reads the file into a tree (cxx.py's last section), and alone refuses; this is the
command, and writes what is owed from the tree.
"""
import argparse
import os
import re
import sys

import clang.cindex as ci

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clang_edge import configure_libclang, probe   # noqa: E402
import proofs_reader   # noqa: E402
from cxx import (Cmp, Lit, LNot, Logic, Name,   # noqa: E402
                 AllBytes, Ask, AskInv, CallFn, Choose, Do, Make, Prove, SeqSize, Window)

WORDS = set("at end from to in do then else if fun let have show match with where by def theorem open".split())


def lean(name):
    return name + "'" if name in WORDS else name


class Owed:
    """What one PROOF (a cxx.Proof, read by proofs_reader.py) owes, written: a list of (name, what it
    says, the statement). Nothing here refuses: what could not be written was not read.

    A state is what each object made so far is, at this point: {object: its name in Lean}, in the
    order made, or None before any is made. Each object's class is in `self.of`."""

    def __init__(self, proof, klass, fuelled=None):
        self.proof, self.C = proof, klass
        self.fuelled = {k: set(v) for k, v in (fuelled or {}).items()}     # {class or function: its methods that take fuel}
        self.name = proof.name
        self.owed = []                  # (name, what it says, the statement)
        self.n = 0
        self.loops = 0
        self.of = {}                    # each object: its class (the name it is proved under)
        self.around = []                # what the loops around say of their variables (`a ≤ x`, `x ≤ b`)

    def fresh(self, stem):
        self.n += 1
        return "%s%d" % (stem, self.n)

    def fuel(self, klass, method):
        return method in self.fuelled.get(klass, ())

    # numbers ------------------------------------------------------------------------------------
    def number(self, e, state, gets):
        if isinstance(e, Lit):
            return "%d#%d" % (e.value, e.width)
        if isinstance(e, Name):
            return lean(e.x)
        if isinstance(e, SeqSize):
            return "(Prooc.Bytes.size %s)" % lean(e.x)     # how many bytes a loop's sequence has
        if isinstance(e, Ask):
            r = self.fresh("r")
            # a const method that loops takes fuel, as any method that loops does: some number of
            # rounds is enough (each its own, so that two such calls do not share one)
            fuel = self.fresh("fuel") + " " if self.fuel(e.klass, e.method) else ""
            me = state[e.obj]
            gets.append("%s.%s %s%s = some (%s, %s)" % (e.klass, e.method, fuel, me, me, r))
            return r
        if isinstance(e, CallFn):
            # a function of the set: a class with no state and one method, `call`
            args = "".join(" (%s)" % self.number(a, state, gets) for a in e.args)
            r = self.fresh("r")
            fuel = self.fresh("fuel") + " " if self.fuel(e.fn, "call") else ""
            gets.append("%s.call %s%s.raw%s = some (%s.raw, %s)" % (e.fn, fuel, e.fn, args, e.fn, r))
            return r
        assert isinstance(e, Choose), e
        return "(if %s then %s else %s)" % (self.cond(e.c, state, gets), self.number(e.a, state, gets), self.number(e.b, state, gets))

    def argument(self, a, state, gets):
        """What a method is handed: a number; or, for a window on bytes, the bytes it is a window on.
        A number may be what a const method of an object gives: `gets` is then what says so."""
        if isinstance(a, Window):
            return lean(a.x)
        return self.number(a, state, gets)

    @staticmethod
    def asked(gets, text):
        """`text`, with what the const methods it names give: they run, leave the object, and give these."""
        if not gets:
            return text
        names = " ".join(" ".join(re.findall(r"\b(fuel\d+)\b", g) + [g.rsplit(", ", 1)[1].rstrip(")")]) for g in gets)
        return "(∃ %s, %s ∧ %s)" % (names, " ∧ ".join(gets), text)

    # conditions ---------------------------------------------------------------------------------
    def cond(self, e, state, gets):
        if isinstance(e, Logic):
            return "(%s %s %s)" % (self.cond(e.a, state, gets), "∧" if e.op == "&&" else "∨", self.cond(e.b, state, gets))
        if isinstance(e, Cmp):
            sign = {"<=": "≤", ">=": "≥", "==": "=", "!=": "≠"}.get(e.op, e.op)
            return "(%s %s %s)" % (self.number(e.a, state, gets), sign, self.number(e.b, state, gets))
        if isinstance(e, LNot):
            return "(¬ %s)" % self.cond(e.c, state, gets)
        assert isinstance(e, AskInv), e
        return "%s.Inv %s" % (e.klass, state[e.obj])

    def holds(self, e, state):
        """A condition, with what its const methods give named: they run, leave the object, and give these."""
        gets = []
        text = self.cond(e, state, gets)
        return self.asked(gets, text)

    def invs(self, state):
        """Each object's class's invariant, of it as it is."""
        return ["%s.Inv %s" % (self.of[o], g) for o, g in state.items()]

    def binders(self, state):
        """`(g : C)` for each object of the state."""
        return " ".join("(%s : %s)" % (g, self.of[o]) for o, g in state.items())

    # statements ---------------------------------------------------------------------------------
    def chain(self, stmts, state, binders, end):
        if not stmts:
            return end(state)
        s = stmts[0]
        rest = stmts[1:]
        if isinstance(s, Make):
            self.of[s.x] = s.klass
            gets = []
            args = "".join(" (%s)" % self.number(a, state, gets) for a in s.args)
            g = self.fresh(lean(s.x))
            now = dict(state or {})
            now[s.x] = g
            return self.asked(gets, "(∃ %s, %s.new%s = some %s ∧ %s)" % (g, s.klass, args, g, self.chain(rest, now, binders, end)))
        if isinstance(s, Prove):
            return "(%s ∧ %s)" % (self.holds(s.c, state), self.chain(rest, state, binders, end))
        if isinstance(s, Do):
            gets = []
            args = "".join(" (%s)" % self.argument(a, state, gets) for a in s.args)
            g = self.fresh(lean(s.obj))
            fuel, some = ("fuel ", "fuel ") if self.fuel(s.klass, s.method) else ("", "")
            now = dict(state)
            now[s.obj] = g
            if s.void:
                return self.asked(gets, "(∃ %s%s, %s.%s %s%s%s = some (%s, ()) ∧ %s)" % (fuel, g, s.klass, s.method, some, state[s.obj], args, g, self.chain(rest, now, binders, end)))
            r = self.fresh("r")
            return self.asked(gets, "(∃ %s%s %s, %s.%s %s%s%s = some (%s, %s) ∧ %s)" % (fuel, g, r, s.klass, s.method, some, state[s.obj], args, g, r, self.chain(rest, now, binders, end)))
        # a loop: AllValues or AllBytes
        seq = isinstance(s, AllBytes)
        x = lean(s.x)
        within = []
        if not seq and s.bounds:
            within = ["%s ≤ %s" % (self.number(s.bounds[0], None, []), x), "%s ≤ %s" % (x, self.number(s.bounds[1], None, []))]
        if seq and s.length is not None:        # every_bytes( n ): sequences of n bytes alone
            within = ["Prooc.Bytes.size %s = %d#64" % (x, s.length)]
        self.loops += 1
        name = "%s_loop%d" % (self.name, self.loops)
        inner = binders + [(x, "Prooc.Bytes" if seq else "BitVec %d" % s.width)]
        keep = s.carried
        # a round of this loop is a round of every loop around it: what they say of their variables holds in it
        within = self.around + within
        outer, self.around = self.around, within
        try:
            return self.loop(s, rest, state, binders, end, inner, keep, within, name)
        finally:
            self.around = outer

    def loop(self, s, rest, state, binders, end, inner, keep, within, name):
        if not state:
            said = self.chain(s.body, None, inner, lambda st: "True")
            self.owed.append((name, "the loop over `%s` at line %d: in every round" % (s.x, s.line),
                              "∀ %s, %s%s" % (" ".join("(%s : %s)" % b for b in inner), "".join(h + " → " for h in within), said)))
            return self.chain(rest, None, binders, end)
        # each object made before the loop is, at a round, any of which its invariant holds
        at = {o: self.fresh(lean(o)) for o in state}
        def again(st):
            return "(%s)" % " ∧ ".join(self.invs(st) + [self.holds(c, st) for c in keep])
        given = self.invs(at) + [self.holds(c, at) for c in keep] + within
        said = self.chain(s.body, at, inner, again)
        self.owed.append((name, "the loop over `%s` at line %d: from any state the rounds before could leave, in every round, and it leaves such a state"
                          % (s.x, s.line),
                          "∀ %s %s, %s%s" % (" ".join("(%s : %s)" % b for b in inner), self.binders(at), "".join(h + " → " for h in given), said)))
        after = {o: self.fresh(lean(o)) for o in state}
        if len(after) == 1:
            (o, g), = after.items()
            every = "∀ %s : %s, " % (g, self.of[o])
        else:
            every = "∀ %s, " % self.binders(after)
        return "(%s ∧ (%s%s%s))" % (again(state), every,
                                  "".join(h + " → " for h in self.invs(after) + [self.holds(c, after) for c in keep]),
                                  self.chain(rest, after, binders, end))

    def write(self):
        whole = self.chain(self.proof.body, None, [], lambda st: "True")
        return [(self.name, "PROOF( %s ), up to and between its loops" % self.name, whole)] + self.owed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("source")
    ap.add_argument("--class", dest="klass", required=True)
    ap.add_argument("--named", help="the class's own name in the C++, if not the name it is proved under")
    ap.add_argument("-o", "--out", default="gen")
    ap.add_argument("-I", dest="include", action="append", default=[])
    ap.add_argument("--std", default="c++17")
    ap.add_argument("--model", help="the class's model, to know which methods take fuel (default: OUT/CModel.lean)")
    ap.add_argument("--with", dest="also", action="append", default=[], metavar="NAME[:CXXNAME[:function]]",
                    help="a domain proved before this one, which the proof may use: a class it may make objects of, "
                         "or (`:function`) a function it may call; CXXNAME, its name in the C++ if not NAME; its model is OUT/NAMEModel.lean")
    args = ap.parse_args()
    configure_libclang()
    builtin = probe([os.environ.get("CC", "cc"), "-print-resource-dir"], "-resource-dir") \
        or probe([os.environ.get("CC", "cc"), "-print-file-name=include"], "-isystem")
    tu = ci.Index.create().parse(args.source, args=["-x", "c++", "-std=" + args.std] + ["-I" + d for d in args.include] + builtin)
    errors = [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
    if errors:
        sys.exit("proofs: %s does not compile: %s" % (args.source, errors[0].spelling))
    def fuelled_of(name, model):
        return re.findall(r"^def (\w+) \(fuel : Nat\)", open(model).read(), flags=re.M) if os.path.exists(model) else []
    fuelled = {args.klass: fuelled_of(args.klass, args.model or os.path.join(args.out, "%sModel.lean" % args.klass))}
    classes, functions = {}, {}
    for w in args.also:
        name, cxx, kind = (w.split(":") + ["", ""])[:3]
        (functions if kind == "function" else classes)[cxx or name] = name
        fuelled[name] = fuelled_of(name, os.path.join(args.out, "%sModel.lean" % name))
    try:
        read = proofs_reader.read(tu, args.source, (args.klass, args.named or args.klass), classes, functions)
    except proofs_reader.Refused as e:
        sys.exit("proofs: REFUSED: %s" % e)
    owed, proofs = [], len(read)
    for p in read:
        owed += Owed(p, args.klass, fuelled).write()
    # the domains the file uses beside its own, whose models it imports, in the order given
    used = set()
    def walk(n):
        if isinstance(n, (Make, Do, Ask, AskInv)) and n.klass:
            used.add(n.klass)
        if isinstance(n, CallFn):
            used.add(n.fn)
        for v in vars(n).values() if hasattr(n, "__dict__") else ():
            for x in (v if isinstance(v, list) else [v]):
                if hasattr(x, "__dict__"):
                    walk(x)
    for p in read:
        walk(p)
    beside = [w.split(":")[0] for w in args.also if w.split(":")[0] in used and w.split(":")[0] != args.klass]
    if not owed:
        sys.exit("proofs: %s has no PROOF( name ) { ... }" % args.source)
    C = args.klass
    L = ["import %sModel" % C] + ["import %sModel" % u for u in beside] + ["",
         "/-! GENERATED by prover/proofs.py from %s. Do not edit." % os.path.basename(args.source),
         "WHAT MUST BE PROVEN for every PROVE of that file to hold in every round of its loops, were it",
         "run: this file imports the model of %s%s, and nothing written by hand. A loop is one statement:" % (C, "".join(", and of %s" % u for u in beside)),
         "from any state the rounds before could leave (the class's invariant, and what the loop's last",
         "PROVEs say without naming its variable), every round's PROVEs hold, and it leaves such a state. -/", "",
         "structure %sProof.Owed : Prop where" % C]
    owed = [o for o in owed if re.split(", | → ", o[2])[-1] != "True" or "∃" in o[2]]      # (a loop that only holds other loops says nothing of its own)
    for name, what, text in owed:
        L += ["  /-- %s. -/" % what, "  %s : %s" % (name, text)]
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "%sProofOwed.lean" % C), "w").write("\n".join(L) + "\n")
    print("%sProofOwed.lean: %d statements from %d PROOFs" % (C, len(owed), proofs))


if __name__ == "__main__":
    main()
