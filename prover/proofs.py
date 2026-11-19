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

It reads a subset, and refuses the rest, saying where: one object of the class, made by
`C name;` or `C name( ... );`; `for ( T x : all<T>() )` and `all<T>( a, b )` with T an unsigned
integer and a, b literals; `for ( const std::vector<unsigned char>& b : every_bytes() )`, every
sequence of bytes of every length; calls of the object's methods with arguments that are loop
variables, literals, or what a const method of the object that takes nothing gives; or a window on such bytes (`W( b.data(), b.size() )`, for a parameter that
is a Strong::subarray or a Bytes). A call says that the method ends and commits no memory error:
where its model takes `fuel`, that some number of rounds is enough; `PROVE( condition )`, a condition of comparisons, `&&`, `||`, `!`, `?:`, the
object's const methods that take nothing, and `invariant()`.

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
                 AllBytes, Ask, AskInv, Choose, Do, Make, Prove, SeqSize, Window)

WORDS = set("at end from to in do then else if fun let have show match with where by def theorem open".split())


def lean(name):
    return name + "'" if name in WORDS else name


class Owed:
    """What one PROOF (a cxx.Proof, read by proofs_reader.py) owes, written: a list of (name, what it
    says, the statement). Nothing here refuses: what could not be written was not read."""

    def __init__(self, proof, klass, fuelled=()):
        self.proof, self.C, self.fuelled = proof, klass, set(fuelled)
        self.name = proof.name
        self.owed = []                  # (name, what it says, the statement)
        self.n = 0
        self.loops = 0
        self.obj = None                 # the object's name
        self.around = []                # what the loops around say of their variables (`a ≤ x`, `x ≤ b`)

    def fresh(self, stem):
        self.n += 1
        return "%s%d" % (stem, self.n)

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
            gets.append("%s.%s %s = some (%s, %s)" % (self.C, e.method, state, state, r))
            return r
        assert isinstance(e, Choose), e
        return "(if %s then %s else %s)" % (self.cond(e.c, state, gets), self.number(e.a, state, gets), self.number(e.b, state, gets))

    def argument(self, a, state, gets):
        """What a method is handed: a number; or, for a window on bytes, the bytes it is a window on.
        A number may be what a const method of the object gives: `gets` is then what says so."""
        if isinstance(a, Window):
            return lean(a.x)
        return self.number(a, state, gets)

    @staticmethod
    def asked(gets, text):
        """`text`, with what the const methods it names give: they run, leave the object, and give these."""
        if not gets:
            return text
        names = " ".join(g.rsplit(", ", 1)[1].rstrip(")") for g in gets)
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
        return "%s.Inv %s" % (self.C, state)

    def holds(self, e, state):
        """A condition, with what its const methods give named: they run, leave the object, and give these."""
        gets = []
        text = self.cond(e, state, gets)
        return self.asked(gets, text)

    # statements ---------------------------------------------------------------------------------
    def chain(self, stmts, state, binders, end):
        if not stmts:
            return end(state)
        s = stmts[0]
        rest = stmts[1:]
        if isinstance(s, Make):
            self.obj = s.x
            args = "".join(" (%s)" % self.number(a, None, []) for a in s.args)
            g = self.fresh(lean(s.x))
            return "(∃ %s, %s.new%s = some %s ∧ %s)" % (g, self.C, args, g, self.chain(rest, g, binders, end))
        if isinstance(s, Prove):
            return "(%s ∧ %s)" % (self.holds(s.c, state), self.chain(rest, state, binders, end))
        if isinstance(s, Do):
            gets = []
            args = "".join(" (%s)" % self.argument(a, state, gets) for a in s.args)
            g = self.fresh(lean(self.obj))
            fuel, some = ("fuel ", "fuel ") if s.method in self.fuelled else ("", "")
            if s.void:
                return self.asked(gets, "(∃ %s%s, %s.%s %s%s%s = some (%s, ()) ∧ %s)" % (fuel, g, self.C, s.method, some, state, args, g, self.chain(rest, g, binders, end)))
            r = self.fresh("r")
            return self.asked(gets, "(∃ %s%s %s, %s.%s %s%s%s = some (%s, %s) ∧ %s)" % (fuel, g, r, self.C, s.method, some, state, args, g, r, self.chain(rest, g, binders, end)))
        # a loop: AllValues or AllBytes
        seq = isinstance(s, AllBytes)
        x = lean(s.x)
        within = []
        if not seq and s.bounds:
            within = ["%s ≤ %s" % (self.number(s.bounds[0], None, []), x), "%s ≤ %s" % (x, self.number(s.bounds[1], None, []))]
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
        if state is None:
            said = self.chain(s.body, None, inner, lambda st: "True")
            self.owed.append((name, "the loop over `%s` at line %d: in every round" % (s.x, s.line),
                              "∀ %s, %s%s" % (" ".join("(%s : %s)" % b for b in inner), "".join(h + " → " for h in within), said)))
            return self.chain(rest, None, binders, end)
        g = self.fresh(lean(self.obj))
        def again(st):
            return "(%s)" % " ∧ ".join(["%s.Inv %s" % (self.C, st)] + [self.holds(c, st) for c in keep])
        given = ["%s.Inv %s" % (self.C, g)] + [self.holds(c, g) for c in keep] + within
        said = self.chain(s.body, g, inner, again)
        self.owed.append((name, "the loop over `%s` at line %d: from any state the rounds before could leave, in every round, and it leaves such a state"
                          % (s.x, s.line),
                          "∀ %s (%s : %s), %s%s" % (" ".join("(%s : %s)" % b for b in inner), g, self.C, "".join(h + " → " for h in given), said)))
        after = self.fresh(lean(self.obj))
        return "(%s ∧ (∀ %s : %s, %s%s))" % (again(state), after, self.C,
                                                "".join(h + " → " for h in ["%s.Inv %s" % (self.C, after)] + [self.holds(c, after) for c in keep]),
                                                self.chain(rest, after, binders, end))

    def write(self):
        whole = self.chain(self.proof.body, None, [], lambda st: "True")
        return [(self.name, "PROOF( %s ), up to and between its loops" % self.name, whole)] + self.owed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("source")
    ap.add_argument("--class", dest="klass", required=True)
    ap.add_argument("-o", "--out", default="gen")
    ap.add_argument("-I", dest="include", action="append", default=[])
    ap.add_argument("--std", default="c++17")
    ap.add_argument("--model", help="the class's model, to know which methods take fuel (default: OUT/CModel.lean)")
    args = ap.parse_args()
    configure_libclang()
    builtin = probe([os.environ.get("CC", "cc"), "-print-resource-dir"], "-resource-dir") \
        or probe([os.environ.get("CC", "cc"), "-print-file-name=include"], "-isystem")
    tu = ci.Index.create().parse(args.source, args=["-x", "c++", "-std=" + args.std] + ["-I" + d for d in args.include] + builtin)
    errors = [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
    if errors:
        sys.exit("proofs: %s does not compile: %s" % (args.source, errors[0].spelling))
    model = args.model or os.path.join(args.out, "%sModel.lean" % args.klass)
    fuelled = re.findall(r"^def (\w+) \(fuel : Nat\)", open(model).read(), flags=re.M) if os.path.exists(model) else []
    try:
        read = proofs_reader.read(tu, args.source, args.klass)
    except proofs_reader.Refused as e:
        sys.exit("proofs: REFUSED: %s" % e)
    owed, proofs = [], len(read)
    for p in read:
        owed += Owed(p, args.klass, fuelled).write()
    if not owed:
        sys.exit("proofs: %s has no PROOF( name ) { ... }" % args.source)
    C = args.klass
    L = ["import %sModel" % C, "",
         "/-! GENERATED by prover/proofs.py from %s. Do not edit." % os.path.basename(args.source),
         "WHAT MUST BE PROVEN for every PROVE of that file to hold in every round of its loops, were it",
         "run: this file imports the model of %s, and nothing written by hand. A loop is one statement:" % C,
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
