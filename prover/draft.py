#!/usr/bin/env python3
"""draft.py C [-o FILE]: a first claims file for a class, written by trying one automatic proof of
each statement it owes, and leaving `sorry` where that does not close it.

Run where prove.sh runs (the domain's directory), after prove.sh has compiled what is owed
(build/COwed.olean). It writes FILE (claims/CClaims.lean if it is not given, and only if there is
none there yet), then says which statements are left. A statement left is `sorry`, which the audit
refuses: so a draft is never taken for a proof, and what is left is for a person or an agent.

Nothing here is trusted, as nothing in a claims file is: what the automatic proof finds is checked
by Lean's kernel and audited as any proof is. It is only a way to spend less attention on the
statements whose proof is to unfold the method, split on each `if`, and do the arithmetic.
"""
import argparse
import os
import re
import subprocess
import sys

# The primitives a model is written with, and the facts of BitVec the arithmetic needs: unfolded
# or used by the automatic proof, beside the class's own definitions.
PRIMITIVES = ["Prooc.get", "Prooc.set", "Prooc.shl", "Prooc.shr", "Prooc.div", "Prooc.mod",
              "Prooc.sadd", "Prooc.ssub", "Prooc.copyIn", "Prooc.copyOwn", "Prooc.Bytes.read",
              "Prooc.Bytes.size_toNat", "BitVec.lt_def", "BitVec.le_def"]
TACTIC = "intros; simp_all [%s] <;> (try split) <;> (try split at *) <;> grind"
LEFT = "  sorry  -- LEFT: the automatic proof did not close it (draft.py); a person or an agent proves it"


def statements(c):
    """(name, statement) of each field of C.Owed, as gen/COwed.lean says them."""
    text = open("gen/%sOwed.lean" % c).read()
    body = text[text.index("structure %s.Owed : Prop where" % c):]
    return re.findall(r"^  (\w+) : (.+)$", body, re.M)


def definitions(c):
    """Every definition of the model of C, by its full name: what a proof unfolds."""
    text = open("gen/%sModel.lean" % c).read()
    return ["%s.%s" % (c, n) for n in re.findall(r"^def (\S+)", text, re.M)]


def write(c, owed, unfold, left, path):
    L = ["import %sOwed" % c, "",
         "/-! The proofs about %s: a DRAFT by draft.py. Nothing here is trusted, and nothing here says" % c,
         "what is owed: that is `%s.Owed`, generated from the class. Each statement was tried by one" % c,
         "automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/", "",
         "set_option maxHeartbeats 400000", "",
         "namespace %s" % c, "namespace Claims", ""]
    for name, st in owed:
        L.append("theorem %s : %s := by" % (name, st))
        L.append(LEFT if name in left else "  " + TACTIC % ", ".join(unfold))
        L.append("")
    L += ["/-- Everything owed. -/", "theorem owed : %s.Owed :=" % c,
          "  { %s }" % ", ".join(n for n, _ in owed), "", "end Claims", "end %s" % c, ""]
    open(path, "w").write("\n".join(L))


def failing(lean, path, owed):
    """The statements whose proof Lean does not accept in the file at path."""
    r = subprocess.run([lean, path], capture_output=True, text=True, env=dict(os.environ, LEAN_PATH="build"))
    lines = open(path).read().split("\n")
    starts = [(i + 1, n) for i, x in enumerate(lines) for n, _ in owed if x.startswith("theorem %s :" % n)]
    bad = set()
    for m in re.finditer(r":(\d+):\d+: error", r.stdout + r.stderr):
        at = int(m.group(1))
        before = [n for line, n in starts if line <= at]
        if before:
            bad.add(before[-1])
    return bad, r


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("klass")
    ap.add_argument("-o", dest="out")
    a = ap.parse_args()
    c, lean = a.klass, os.environ.get("LEAN", "lean")
    path = a.out or "claims/%sClaims.lean" % c
    if a.out is None and os.path.exists(path):
        sys.exit("draft: %s is there already: a draft is written only where there are no claims (or name one with -o)" % path)
    if not os.path.exists("build/%sOwed.olean" % c):
        sys.exit("draft: build/%sOwed.olean is not there: prove.sh compiles what is owed first" % c)
    owed = statements(c)
    unfold = list(dict.fromkeys(definitions(c) + PRIMITIVES))
    write(c, owed, unfold, set(), path)
    left, _ = failing(lean, path, owed)
    write(c, owed, unfold, left, path)
    still, r = failing(lean, path, owed)
    if still or r.returncode not in (0, 1):
        print(r.stdout + r.stderr)
        sys.exit("draft: %s does not compile with what is left as sorry: the draft is wrong, not the class" % path)
    print("draft: %s: %d of %d statements proved by the automatic proof%s" % (
        c, len(owed) - len(left), len(owed), "; LEFT: " + ", ".join(n for n, _ in owed if n in left) if left else ""))


if __name__ == "__main__":
    main()
