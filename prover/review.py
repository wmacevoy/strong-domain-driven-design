#!/usr/bin/env python3
"""review.py C: what a reviewer of C's invariant should look at, said beside its PROVED.

A proof shows that the invariant holds; it cannot show that the invariant says enough. When every
statement is proved by the automatic proof, the review of a class is the review of what it claims:
its `invariant()`. This says, of the class as the model has it:

  - its invariant, as the C++ says it, or that it says none (then only memory and ending are proved);
  - the fields it does not name: what is claimed says nothing of them;
  - an invariant of `true`: it claims nothing;
  - which public methods' safety rests on it: for each, whether the automatic proof shows it commits
    no memory error from any state at all. If it does, the invariant does nothing for that method's
    safety (it may still say what the class is for).

It judges nothing and fails nothing: it is what a critical review starts from. Run where prove.sh
runs, after it has compiled the model.
"""
import os
import re
import subprocess
import sys
import tempfile

import draft


def main():
    c = sys.argv[1]
    lean = os.environ.get("LEAN", "lean")
    model = open("gen/%sModel.lean" % c).read()
    inv = re.search(r"^def Inv .*?: Prop := (.*)$", model, re.M)
    struct = re.search(r"^structure %s(?: \(.*?\))? where\n((?:  .*\n)*)" % re.escape(c), model, re.M)
    fields = re.findall(r"^  (\S+) :", struct.group(1), re.M) if struct else []
    text = inv.group(1).strip() if inv else None
    out = []
    if text is None or "the class says none" in model or text == "True":
        out.append("its invariant claims nothing%s: what is proved is memory and ending alone"
                   % ("" if text == "True" else " (it says none)"))
    else:
        named = [f for f in fields if re.search(r"\bme\.%s\b" % re.escape(f), text)]
        out.append("invariant: %s" % text)
        rest = [f for f in fields if f not in named]
        if rest:
            out.append("names no claim of: %s" % ", ".join(rest))
    owed = draft.statements(c)
    safe = [(n, st) for n, st in owed if n.endswith("_safe") and n != "new_safe" and "%s.Inv me →" % c in st]
    if safe and text not in (None, "True"):
        unfold = list(dict.fromkeys(draft.definitions(c) + draft.PRIMITIVES))
        with tempfile.NamedTemporaryFile("w", suffix=".lean", dir="build", delete=False) as f:
            f.write("import %sOwed\nset_option maxHeartbeats 400000\n\n" % c)
            for n, st in safe:
                f.write("theorem %s_alone : %s := by\n  %s\n\n" % (n, st.replace("%s.Inv me → " % c, ""), draft.TACTIC % ", ".join(unfold)))
            path = f.name
        bad, _ = draft.failing(lean, path, [("%s_alone" % n, st) for n, st in safe])
        os.remove(path)
        rests = [n[:-len("_safe")] for n, _ in safe if "%s_alone" % n in bad]
        free = [n[:-len("_safe")] for n, _ in safe if "%s_alone" % n not in bad]
        if rests:
            out.append("the safety of %s rests on it (or is beyond the automatic proof without it)" % ", ".join(rests))
        if free:
            out.append("the safety of %s does not: it holds from any state" % ", ".join(free))
    print("REVIEW %s: %s" % (c, "; ".join(out)))


if __name__ == "__main__":
    main()
