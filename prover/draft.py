#!/usr/bin/env python3
"""draft.py C [-o FILE]: a first claims file for a class, written by trying one automatic proof of
each statement it owes, and leaving `sorry` where that does not close it.

Run where prove.sh runs (the domain's directory), after prove.sh has compiled what is owed
(build/COwed.olean). It writes FILE (claims/CClaims.lean if it is not given, and only if there is
none there yet), then says which statements are left. A statement left is `sorry`, which the audit
refuses: so a draft is never taken for a proof, and what is left is for a person or an agent.

For each statement left it writes a folder, build/left/C/NAME/: the draft, a check that compiles
it and says what NAME's proof rests on, and a brief: what an agent needs to prove NAME and nothing
else, so that one agent may be given each, all at once. `draft.py --gather C` then puts each proof
an agent wrote back into claims/CClaims.lean, if its check passes, and says which are still left.

Nothing here is trusted, as nothing in a claims file is: what the automatic proof finds is checked
by Lean's kernel and audited as any proof is. It is only a way to spend less attention on the
statements whose proof is to unfold the method, split on each `if`, and do the arithmetic.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys

# The primitives a model is written with, and the facts of BitVec the arithmetic needs: unfolded
# or used by the automatic proof, beside the class's own definitions.
PRIMITIVES = ["Prooc.get", "Prooc.set", "Prooc.shl", "Prooc.shr", "Prooc.div", "Prooc.mod",
              "Prooc.sadd", "Prooc.ssub", "Prooc.copyIn", "Prooc.copyOwn", "Prooc.fill", "Prooc.Bytes.read", "Prooc.outside", "Prooc.pick",
              "Prooc.Bytes.size_toNat", "BitVec.lt_def", "BitVec.le_def"]
TACTIC = "intros; simp_all [%s] <;> (try split) <;> (try split at *) <;> grind"
LEFT = "  sorry  -- LEFT: the automatic proof did not close it (draft.py); a person or an agent proves it"


def statements(c):
    """(name, statement) of each field of C.Owed, as gen/COwed.lean says them."""
    text = open("gen/%sOwed.lean" % c).read()
    body = text[text.index("structure %s.Owed : Prop where" % c):]
    return re.findall(r"^  (\w+) : (.+)$", body, re.M)


def definitions(c, seen=None):
    """Every definition of the model of C, and of the models it imports (the classes it uses), by
    its full name: what a proof unfolds."""
    seen = set() if seen is None else seen
    if c in seen or not os.path.exists("gen/%sModel.lean" % c):
        return []
    seen.add(c)
    text = open("gen/%sModel.lean" % c).read()
    out = ["%s.%s" % (c, n) for n in re.findall(r"^def (\S+)", text, re.M)]
    for u in re.findall(r"^import (\S+)Model$", text, re.M):
        out += definitions(u, seen)
    return out


def binders(text):
    """(name, type) of each `(name : type)` in a definition's head."""
    out, depth, cur = [], 0, ""
    for ch in text:
        if ch == "(":
            depth += 1
            if depth == 1:
                cur = ""
                continue
        elif ch == ")":
            depth -= 1
            if depth == 0:
                n, _, t = cur.partition(" : ")
                out.append((n.strip(), t.strip()))
                continue
        if depth >= 1:
            cur += ch
    return out


def counting_loops(c):
    """The loops of the model of C that count: a round's first test is `i < b`, the variable is
    only made one more, at the end of the round, b does not change in the loop, and no round
    returns. Of each: the names its lemma is written with. What a loop rests on is then derived:
    the measure b less i, and the class's invariant if the loop changes the object."""
    text = open("gen/%sModel.lean" % c).read()
    found = []
    for m in re.finditer(r"^def (\S+)\.round(\d+) \(fuel : Nat\)(.*?) : Option \(Prooc\.Step \((.*?)\) \(.*\)\) := do\n(.*?)\n\n",
                         text, re.M | re.S):
        method, k, head, state, body = m.group(1), m.group(2), m.group(3), m.group(4), m.group(5)
        lines = body.split("\n")
        tests = [x for x in lines if x.startswith("  if ¬")]
        if not tests:
            continue
        t = re.match(r"  if ¬ \((\S+) < (.+)\) then$", tests[0])
        done = re.search(r"return \.done \((.*)\)$", body, re.M)
        if not t or not done or ".ret" in body:
            continue
        var, bound = t.group(1), t.group(2)
        carried = [x.strip() for x in done.group(1).split(",")]
        width = re.search(r"\(%s : BitVec (\d+)\)" % re.escape(var), head)
        steps = [x for x in lines if re.match(r"\s*%s := " % re.escape(var), x)]
        if (var not in carried or not width or steps != ["  %s := (%s + 1#%s)" % (var, var, width.group(1))]
                or any(re.search(r"\b%s\b" % re.escape(n), bound) for n in carried) or "me." in bound and "me" in carried):
            continue
        bs = binders(head)
        whole = re.search(r"^def %s (.*?) := do\n(.*?)\n\n" % re.escape(method), text, re.M | re.S)
        init = dict(re.findall(r"^  let mut (\S+) : [^:]+ := (.+)$", whole.group(2), re.M)) if whole else {}
        def proj(i, n=len(carried)):
            return "s" + ".2" * i + (".1" if i < n - 1 else "") if n > 1 else "s"
        at = {name: proj(i) for i, name in enumerate(carried)}
        args = " ".join(at.get(n, n) for n, _ in bs)
        fixed = [(n, t) for n, t in bs if n not in at]
        me = at.get("me", "me")
        start = "(%s)" % ", ".join(init.get(n, n) for n in carried)
        found.append(dict(method=method, k=k, var=var, bound=bound, state=state, carried=carried, start=start,
                          args=args, fixed=fixed, me=me, at=at, views=[n for n, t in bs if t == "Prooc.Bytes"]))
    return found


def loop_lemma(c, L, unfold):
    """The lemma that a counting loop is done, and its proof: from Prooc.done_within, with what is
    derived from the loop's header, and one round proved by the automatic proof."""
    fx = "".join(" (%s : %s)" % (n, t) for n, t in L["fixed"])
    name = "%s_loop%s_done" % (L["method"].replace(".", "_"), L["k"])
    inv = "%s.Inv %s" % (c, L["me"])
    measure = "(%s).toNat - (%s).toNat" % (L["bound"], L["at"][L["var"]])
    loop = "(fun left (s : %s) => %s.%s.loop%s fuel left %s)" % (L["state"], c, L["method"], L["k"], L["args"])
    facts = "".join("    have := Prooc.Bytes.size_toNat %s; have := %s.small\n" % (v, v) for v in L["views"])
    return name, "\n".join([
        "/-- The loop of `%s` counts: it is done within its bound less its variable, and one more, of" % L["method"],
        "rounds (derived by draft.py from its header, by `Prooc.done_within`). -/",
        "theorem %s (fuel : Nat)%s : ∀ (left : Nat) (s : %s), %s → %s < left →" % (name, fx, L["state"], inv, measure),
        "    Prooc.DoneWith (%s left s) (fun s => %s) := by" % (loop, inv),
        "  apply Prooc.done_within (fun (s : %s) => %s.%s.round%s fuel %s)" % (L["state"], c, L["method"], L["k"], L["args"]),
        "  · intro left s; simp only [%s.%s.loop%s]; cases %s.%s.round%s fuel %s with" % (c, L["method"], L["k"], c, L["method"], L["k"], L["args"]),
        "    | none => rfl",
        "    | some r => cases r <;> rfl",
        "  · intro s hp",
        facts + "    by_cases h : %s < %s" % (L["at"][L["var"]], L["bound"]),
        "    · left; " + TACTIC.replace("intros; ", "") % ", ".join(unfold),
        "    · right; " + TACTIC.replace("intros; ", "") % ", ".join(unfold), ""])


def write(c, owed, unfold, left, path):
    L = ["import %sOwed" % c, "",
         "/-! The proofs about %s: a DRAFT by draft.py. Nothing here is trusted, and nothing here says" % c,
         "what is owed: that is `%s.Owed`, generated from the class. Each statement was tried by one" % c,
         "automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/", "",
         "set_option maxHeartbeats 400000", "",
         "namespace %s" % c, "namespace Claims", ""]
    lemmas = {}
    for lp in counting_loops(c):
        name, text = loop_lemma(c, lp, unfold)
        lemmas[lp["method"]] = (name, lp)
        L.append(text)
    for name, st in owed:
        L.append("theorem %s : %s := by" % (name, st))
        m = name[:-len("_ends")] if name.endswith("_ends") else None
        if name in left:
            L.append(LEFT)
        elif m in lemmas:          # a method with a counting loop: enough rounds, and the loop's lemma
            lemma, lp = lemmas[m]
            enough = "(%s).toNat + 1" % lp["bound"]
            names = [n for n, _ in binders(st.split(",")[0])]
            L += ["  intro %s hi" % " ".join(names),
                  "  refine ⟨%s, ?_⟩" % enough,
                  "  obtain ⟨s, hs, hq⟩ := %s (%s)%s (%s) %s hi (by omega)"
                  % (lemma, enough, "".join(" " + n for n, _ in lp["fixed"]), enough, lp["start"]),
                  "  simp only at hs",
                  "  " + TACTIC.replace("intros; ", "") % ", ".join(unfold)]
        else:
            L.append("  " + TACTIC % ", ".join(unfold))
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


FORBIDDEN = ("sorry", "admit", "native_decide", "bv_decide", "axiom ", "set_option", "import ", "decide := true")

BRIEF = """Prove one Lean 4 theorem. Edit only the file {file}, and only the proof of `{name}`
there: replace its line `sorry  -- LEFT: ...` with a proof. Change nothing else.

The statement: {statement}

Check (run it, by this path, after every edit): sh {check}
It prints Lean's errors, and last what `{name}` rests on. Done when no line says `error` and the
last lists only some of propext, Classical.choice, Quot.sound.

Not allowed in the proof: {forbidden}.

What the names mean: the model of {klass} is {model} (each method of the C++ as a function, `none`
where the C++ would commit a memory error); its primitives are {prooc}. Read them; edit neither.
Useful: unfold, by_cases, simp, split, omega, bv_omega, grind; BitVec.lt_def, BitVec.le_def,
BitVec.toNat_sub_of_le, BitVec.toNat_setWidth, Prooc.Bytes.size_toNat.

Give up after {tries} runs of the check. Report the proof you wrote and the check's last line, or
the last error.
"""

CHECK = """#!/bin/sh
# Compiles the draft here, from the domain's build/, and says what {name} rests on.
here=$(cd "$(dirname "$0")" && pwd)
cp "$here/{klass}Claims.lean" "$here/.check.lean"
printf '\n#print axioms {klass}.Claims.{name}\n' >> "$here/.check.lean"
cd "{build}" && LEAN_PATH=. "{lean}" "$here/.check.lean" 2>&1
"""


def theorem_text(text, name):
    """The proof of theorem `name` in a claims file: the lines after its statement, to the next
    theorem or to `owed`."""
    lines = text.split("\n")
    i = next(k for k, x in enumerate(lines) if x.startswith("theorem %s :" % name))
    j = next(k for k in range(i + 1, len(lines)) if lines[k].startswith(("theorem ", "/-- Everything owed")))
    return i, j, lines


def briefs(c, owed, left, lean, tries=12):
    home = os.path.dirname(os.path.abspath(__file__))
    for name, st in owed:
        if name not in left:
            continue
        d = os.path.abspath(os.path.join("build", "left", c, name))
        os.makedirs(d, exist_ok=True)
        shutil.copy("claims/%sClaims.lean" % c, os.path.join(d, "%sClaims.lean" % c))
        open(os.path.join(d, "check.sh"), "w").write(CHECK.format(name=name, klass=c, build=os.path.abspath("build"),
                                                                  lean=os.path.abspath(lean) if os.sep in lean else lean))
        open(os.path.join(d, "BRIEF.md"), "w").write(BRIEF.format(
            file=os.path.join(d, "%sClaims.lean" % c), name=name, statement=st, check=os.path.join(d, "check.sh"),
            forbidden=", ".join(FORBIDDEN), klass=c, model=os.path.abspath("gen/%sModel.lean" % c),
            prooc=os.path.join(home, "Prooc.lean"), tries=tries))


def gather(c, lean):
    """Each proof an agent wrote in build/left/C/NAME, put back into claims/CClaims.lean if its
    check passes there and it uses nothing forbidden."""
    path, root = "claims/%sClaims.lean" % c, os.path.join("build", "left", c)
    text = open(path).read()
    taken, refused = [], []
    for name in sorted(os.listdir(root)) if os.path.isdir(root) else []:
        d = os.path.join(root, name)
        i, j, there = theorem_text(open(os.path.join(d, "%sClaims.lean" % c)).read(), name)
        proof = there[i + 1:j]
        said = subprocess.run(["sh", os.path.join(d, "check.sh")], capture_output=True, text=True).stdout
        rests = said.strip().split("\n")[-1] if said.strip() else ""
        clean = not any(w in "\n".join(proof) for w in FORBIDDEN)
        if ": error" in said or "sorryAx" in rests or "depends on axioms" not in rests and "does not depend" not in rests or not clean:
            refused.append(name)
            continue
        a, b, lines = theorem_text(text, name)
        text = "\n".join(lines[:a + 1] + proof + lines[b:])
        taken.append(name)
    open(path, "w").write(text)
    print("draft: %s: gathered %s%s" % (c, ", ".join(taken) or "nothing",
                                        "; still LEFT: " + ", ".join(refused) if refused else ""))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("klass")
    ap.add_argument("-o", dest="out")
    ap.add_argument("--gather", action="store_true", help="put back the proofs agents wrote in build/left/C")
    a = ap.parse_args()
    c, lean = a.klass, os.environ.get("LEAN", "lean")
    if a.gather:
        return gather(c, lean)
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
    if a.out is None:
        briefs(c, owed, left, lean)
    print("draft: %s: %d of %d statements proved by the automatic proof%s" % (
        c, len(owed) - len(left), len(owed), "; LEFT: " + ", ".join(n for n, _ in owed if n in left) +
        (" (a brief for each: build/left/%s/)" % c if a.out is None else "") if left else ""))


if __name__ == "__main__":
    main()
