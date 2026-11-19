#!/usr/bin/env python3
"""
ingress -- the rule between code that is proved and code that is not.

A method or a constructor that says `pre( condition )` is not tested when the program runs: every
call of it must be proved to keep the condition. A proved class's calls are (prove.sh). Code that
is not proved cannot be, so it may not make such a call at all: it comes in by the ways that expect
nothing and test for themselves (a `_checked` type or method). This refuses the program otherwise.

    DOMAIN=dir SUBJECT=dir python3 ingress.py CLASS...      after prove.sh CLASS..., which wrote gen/

CLASS... are the proved classes (DOMAIN/from/C names each one's file under SUBJECT). Every other
line of every .h, .hpp, .cc and .cpp under SUBJECT is code that is not proved.

And code that is not proved calls what is proved by a name that ends `_checked`, and by no other,
even where nothing can fail: so every place the two meet is found by that word. It refuses, in code
that is not proved, a call of a proved function by another name, and `NAME.method(` or
`NAME->method(` by another name where NAME was declared there with a proved class's type.

It reads words, not meanings (SE1/U4, chosen): in code that is not proved it refuses
  - making a value of a type whose constructor says `pre`, by that type's name or a name for it;
  - `.NAME(` or `->NAME(` for a method NAME that says `pre` in any proved class, whatever it is
    called on. So it can refuse a call that is of another class's method of the same name
    (DOMAIN/ingress-ok lists such lines, one `FILE:LINE-TEXT-FRAGMENT` each, read by a person);
With STRONG=dir (a directory under SUBJECT, and a namespace of that name with its first letter
large): what is proved is there, and only there. It refuses a proved class that stands anywhere
else or in another namespace, and anything under that directory with a body that is not one of
the proved classes: so "under STRONG" and "proved" say the same thing. But for one file there,
caller.h: who called a way in, and the end of the process when what it tests is not so. That is
trusted, and is the only failure there is when the program runs: not an answer, not an exception.

And it cannot see a value made through a name it was not told of (a `typedef` not named by a
`needs` line), or through `auto` from a function that is not proved. Exit 1 if anything is refused.
"""
import os
import re
import sys

DOMAIN = os.environ.get("DOMAIN") or os.path.dirname(os.path.abspath(__file__))
SUBJECT = os.environ.get("SUBJECT")
if not SUBJECT or len(sys.argv) < 2:
    sys.exit("ingress: set SUBJECT, and name the proved classes")


def plain(text):
    """The text with comments and what is in quotes made blank, no line moved."""
    def blank(m):
        return re.sub(r"[^\n]", " ", m.group(0))
    return re.sub(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\'', blank, text, flags=re.S)


proved = {}         # file under SUBJECT: [(first line, last line, class)]
needs = []          # (file, name): names the proved classes are written with
for c in sys.argv[1:]:
    said = open(os.path.join(DOMAIN, "from", c)).read().split("\n")
    rel = said[0].split()[0]
    head = open(os.path.join(DOMAIN, "gen", c + ".subject.hpp")).readline()
    m = re.search(r"(?:class|function) %s, lines (\d+) to (\d+) of " % re.escape(c), head)
    if not m:
        sys.exit("ingress: gen/%s.subject.hpp does not say where %s stands: run prove.sh first" % (c, c))
    proved.setdefault(rel, []).append((int(m.group(1)), int(m.group(2)), c))
    needs += [tuple(x.split()[1:3]) for x in said if x.startswith("needs ")]

texts = {}
for rel in proved:
    texts[rel] = plain(open(os.path.join(SUBJECT, rel), encoding="utf-8", errors="replace").read()).split("\n")

made, called = set(), {}       # types whose constructor says pre; methods that say pre: name -> class
for rel, spans in proved.items():
    for first, last, c in spans:
        body = "\n".join(texts[rel][first - 1:last])
        for m in re.finditer(r"(\w+)\s*\(([^()]*)\)\s*(?:const\s*)?pre\s*\(", body):
            if m.group(1) == c:
                made.add(c)
            else:
                called[m.group(1)] = c
more = True
while more:         # a name for such a type is such a type
    more = False
    for rel, name in set(needs):
        if name in made:
            continue
        text = plain(open(os.path.join(SUBJECT, rel), encoding="utf-8", errors="replace").read())
        said = re.search(r"(?:typedef\b[^;]*\b%s\s*;|using\s+%s\s*=[^;]*;)" % (re.escape(name), re.escape(name)), text)
        if said and any(re.search(r"\b%s\b" % re.escape(t), said.group(0).replace(name, " ", 1) if said.group(0).startswith("using") else said.group(0)) for t in made):
            made.add(name)
            more = True

refused = 0
STRONG = os.environ.get("STRONG")
if STRONG:
    last = STRONG.strip("/").split("/")[-1]
    space = "namespace %s {" % (last[:1].upper() + last[1:])
    for rel, spans in sorted(proved.items()):
        for _, _, c in spans:
            if not rel.startswith(STRONG.rstrip("/") + "/") and ("/" + STRONG.strip("/") + "/") not in "/" + rel:
                print("ingress: %s: %s is proved, and does not stand under %s/" % (rel, c, STRONG))
                refused += 1
            if space not in open(os.path.join(DOMAIN, "gen", c + ".subject.hpp")).read():
                print("ingress: %s: %s is proved, and is not in `%s`" % (rel, c, space[:-2]))
                refused += 1
    for root, _, files in sorted(os.walk(SUBJECT)):
        for f in sorted(files):
            rel = os.path.relpath(os.path.join(root, f), SUBJECT)
            if ("/" + STRONG.strip("/") + "/") not in "/" + rel or not f.endswith((".h", ".hpp", ".cc", ".cpp")):
                continue
            if f == "caller.h":     # who called, and the end of the process: the one thing there that is trusted
                continue
            lines = plain(open(os.path.join(root, f), encoding="utf-8", errors="replace").read()).split("\n")
            for first, last, _ in proved.get(rel, []):
                for i in range(first - 1, last):
                    lines[i] = ""
            left = "\n".join(lines)                # what is left may name things, and may not do anything
            for m in re.finditer(r"\b(?:class|struct|union)\s+\w+[^;<>]*\{|\)\s*(?:const\s*)?(?:noexcept\s*)?\{", left):
                i = left.count("\n", 0, m.start())
                print("ingress: %s:%d: under %s/, and not one of the proved classes:\n    %s" % (rel, i + 1, STRONG, lines[i].strip()))
                refused += 1

# The ways in: what is `_checked` in the proved classes, and the names for it. Each use of one by
# code that is not proved is a place where that code still stands against what is proved: it is
# said, every time, so that what is left to make strong is evident. None of them should ever fail.
ways = {c for spans in proved.values() for _, _, c in spans if "_checked" in c}
for rel, spans in proved.items():
    for first, last, c in spans:
        ways |= set(re.findall(r"\b(\w+_checked)\s*\(", "\n".join(texts[rel][first - 1:last])))
more = True
while more:
    more = False
    for rel, name in set(needs):
        if name in ways:
            continue
        text = plain(open(os.path.join(SUBJECT, rel), encoding="utf-8", errors="replace").read())
        said = re.search(r"(?:typedef\b[^;]*\b%s\s*;|using\s+%s\s*=[^;]*;)" % (re.escape(name), re.escape(name)), text)
        if said and any(re.search(r"\b%s\b" % re.escape(t), said.group(0).replace(name, " ", 1)) for t in ways):
            ways.add(name)
            more = True
weak = []
functions = {c for c in sys.argv[1:] if open(os.path.join(DOMAIN, "from", c)).read().split("\n")[0].split()[1:] == ["function"]}
types = {c for spans in proved.values() for _, _, c in spans} - functions       # proved classes, and names for them
more = True
while more:
    more = False
    for rel, name in set(needs):
        if name in types:
            continue
        text = plain(open(os.path.join(SUBJECT, rel), encoding="utf-8", errors="replace").read())
        said = re.search(r"(?:typedef\b[^;]*\b%s\s*;|using\s+%s\s*=[^;]*;)" % (re.escape(name), re.escape(name)), text)
        if said and any(re.search(r"\b%s\b" % re.escape(t), said.group(0).replace(name, " ", 1)) for t in types):
            types.add(name)
            more = True

ok = []
if os.path.exists(os.path.join(DOMAIN, "ingress-ok")):
    ok = [x.strip() for x in open(os.path.join(DOMAIN, "ingress-ok")) if x.strip() and not x.startswith("#")]

for root, _, files in sorted(os.walk(SUBJECT)):
    for f in sorted(files):
        if not f.endswith((".h", ".hpp", ".cc", ".cpp")):
            continue
        path = os.path.join(root, f)
        rel = os.path.relpath(path, SUBJECT)
        raw = open(path, encoding="utf-8", errors="replace").read().split("\n")
        lines = plain("\n".join(raw)).split("\n")
        for first, last, _ in proved.get(rel, []):       # the proved classes are not looked at here
            for i in range(first - 1, last):
                lines[i] = ""
        text = "\n".join(lines)
        if not (STRONG and ("/" + STRONG.strip("/") + "/") in "/" + rel):
            for i, line in enumerate(lines):
                if any(re.search(r"\b%s\b" % re.escape(w), line) for w in ways):
                    weak.append("%s:%d: %s" % (rel, i + 1, raw[i].strip()))
        found = []
        for t in made:
            for m in re.finditer(r"\b%s\b\s*(?:<[^;{}()]*>)?\s*(?:\w+\s*)?[({]" % re.escape(t), text):
                found.append((m.start(), "makes a %s, whose constructor expects something of its caller" % t))
        for name, c in called.items():
            for m in re.finditer(r"(?:\.|->)\s*%s\s*\(" % re.escape(name), text):
                found.append((m.start(), "calls %s, which in %s expects something of its caller" % (name, c)))
        for fn in functions:
            if not fn.endswith("_checked"):
                for m in re.finditer(r"\b%s\s*\(" % re.escape(fn), text):
                    found.append((m.start(), "calls %s, which is proved, by a name that is not `_checked`" % fn))
        held = set()
        for t in types:
            held |= set(re.findall(r"\b%s\b(?:\s*<[^;{}()]*>)?\s*[&*]?\s*(\w+)\s*(?=[;,)({=])" % re.escape(t), text))
        for name in held:
            for m in re.finditer(r"\b%s\s*(?:\.|->)\s*(\w+)\s*\(" % re.escape(name), text):
                if not m.group(1).endswith("_checked"):
                    found.append((m.start(), "calls %s on %s, which is of a proved class, and not by a `_checked` name" % (m.group(1), name)))
        for at, why in sorted(found):
            n = text.count("\n", 0, at)
            if any(x.startswith(rel + ":") and x[len(rel) + 1:] in raw[n] for x in ok):
                continue
            print("ingress: %s:%d: code that is not proved %s:\n    %s" % (rel, n + 1, why, raw[n].strip()))
            refused += 1
if refused:
    print("ingress: REFUSED: %d. Code that is not proved comes in by a `_checked` name, and by no other." % refused)
    sys.exit(1)
print("ingress: ok: code that is not proved makes no %s and calls no %s"
      % (", ".join(sorted(made)) or "(nothing expects)", ", ".join(sorted(called)) or "(no such method)"))
print("ingress: code that is not proved comes in at %d place%s (each by a `_checked` name; a test there should never fail):"
      % (len(weak), "" if len(weak) == 1 else "s"))
for w in weak:
    print("    " + w[:150])
