# Proposal: the prover as domains

**Done on 2026-11-19** (the client: "yes to both, steps 1 to 5"); what came of it is in `docs/FINDINGS.md` and `prover/README.md`. As it was proposed:

A proposal, not a decision: nothing in `prover/` has been changed for it. Written by Claude
Fable 5.2 on 2026-11-19, on the client's word: "think about domain based design for the prover
... it will get too big to reason about too." Queue item 32.

## What is there today (measured)

| File | Lines | What it does |
| ---- | ----- | ------------ |
| `prooc.py` | 1,966 | reads a class with Clang's library, and writes the model, what is owed, both comparison programs and the script |
| `lint.py` | 739 | seven rules over a whole program, in one walk |
| `proofs.py` | 381 | reads a proof file and writes what is owed of it |
| `ingress.py` | 205 | the rule between proved and unproved code, by words (regular expressions) |
| `clang_edge.py` | 69 | the edge to Clang's library: finding it, the include directory, and the cursor questions the binding lacks |
| `prove.sh` | 93 | the order of the steps |

What makes it hard to reason about, in the terms we hold gosh to:

- **One class does two jobs.** `Body` (`prooc.py`, 700 lines) walks Clang's tree and writes Lean
  text in the same step: `expr()` takes a cursor and gives back a string of Lean. So "did it read
  the C++ rightly?" and "did it write the model rightly?" cannot be asked apart. That one question
  is the largest thing the project trusts.
- **Four readers of C++, each its own.** `prooc.py`, `proofs.py`, `lint.py` and the spike's
  `tree.py` each strip casts, find an operator and read a literal in their own way. A bug fixed
  in one stays in the others (the lint skipped a call inside a call for a day).
- **State shared by everything.** `USED`, `OPTIONS`, `READ` in the generator; `seen`, `refused`,
  `NEEDS`, `CALLERS` and ten more in the lint. It is what the lint refuses in gosh.
- **The rules are tangled in one walk.** `visit()` in the lint serves seven rules at once; a rule
  cannot be read, or tested, alone.

## The shape proposed

One boundary matters more than the rest: **what was read, as data.** Everything before it touches
Clang; everything after it is a function from data to text.

| Domain | Answers for | Touches |
| ------ | ----------- | ------- |
| `clang` (an edge) | parsing a file; the few questions asked of a cursor (what is under the casts, which operator, which literal) | Clang's library: the only part that does |
| `cxx` | the tree of the subset: a class, its fields, methods, statements, expressions, types. Plain data, and a reader from `clang` to it that refuses what is outside the subset, saying where | nothing |
| `model` | the tree, as the model in Lean | nothing |
| `owed` | the tree, as what must be proved | nothing |
| `compare` | the tree, as the two programs and the script that compare model and C++ | nothing |
| `proofs` | a proof file's tree (the same reader, with `all<T>` and `PROVE`), as what is owed of it | nothing |
| `subject` | a class where it stands in another program: its text, the names it needs, `pre(...)` written at the head of the body | files |
| `program` | a whole program as data: its files, calls, who calls whom, what each name is | `clang` |
| `rules/` | one file per rule (boundary, one name, one owner, own bytes, a window, nothing leaves, a context): each a function from `program` to findings, refused or said | nothing |
| `drive` | the order: compile, lint, prove | the shell |

`Prooc.lean` and `Audit.lean` stay as they are: small, and already one thing each.

## Why this line, and not another

- **It is the line between what is checked and what is trusted.** The spike of queue item 25
  already wrote this tree, in Lean (`spike-tree/Cxx.lean`), with an interpreter that says what
  it means; and showed the kernel accepting, per class, that the generator's model is what the
  interpreter gives of the tree. If `cxx` IS that tree, then `model` need not be trusted or
  proved as code: its output is checked on every run. What is left to trust is the reader, and
  the spike checks that too, against the source's own words.
- **A rule that is a function can be said as a proof file.** "No two arguments of a call are one
  thing" over `program`-as-data is a statement about data. Today it is a walk with side effects.
- **The boundary rule stops reading words.** `ingress.py` matches text. On `program` it is a rule
  like the others, over meanings.

## How to get there without a leap

Each step keeps everything passing, and changes no output: `gen/` is committed, so a step that
changes one byte of it shows in `git status`. That, the suite (160 cases) and the check are the
judge of every step.

1. **`clang`, and one copy of each helper.** Mechanical. A day.
2. **The lint as `program` and seven rule files.** Mechanical, judged by its 50 cases. A day.
3. **`model`, `owed`, `compare`, `subject` out of `prooc.py`** as they stand (they are already
   functions of a class). Mechanical. A day.
4. **`cxx`: `Body` split into a reader and a writer.** The real work, and the only step where a
   mistake could change meaning. Range: 4 to 8 days. Done class by class, with the spike's
   kernel check as the witness where it already reaches (no arrays, views or calls yet).
5. **`proofs` onto the same reader.** A day, after 4.

Steps 1 to 3 suit cheaper agents: exact moves, and a byte-for-byte judge they can run.

## What this does not do

- It does not prove the prover. It puts the trusted part in one place, small enough to prove.
- No new language, no framework, no plug-ins. Python files, each under about 400 lines.
- `oopcc.py` is not carried: its four helpers go to `clang`, and the rest stays in oopc.

## For the client to decide

1. Is `cxx` the spike's tree, so that this and "prove the prover" (queue item 25) are one piece
   of work? *Recommended: yes.*
2. Steps 1 to 3 now, before the next domain of gosh, or after? *Recommended: now; each new
   feature today is written three times.*
