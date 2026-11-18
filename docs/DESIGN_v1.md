# Design — v1

How we intend to satisfy the requirements, and what we rejected. Every mechanism here should be
replaceable without renegotiating a requirement
([SE1/R5](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/04-requirements.md#r5)).
Written by Claude Fable 5.2 on 2026-11-18 from what exists; reasons nobody stated are *(inferred)*.

## Components and the dependency rule

| Component | Layer | Kind | Contract (one line) | Holds state? |
| --------- | ----- | ---- | ------------------- | ------------ |
| `oopc/` (a git submodule) | 0 | tool | `cpp-proof-gen/prove.sh`, with `DOMAIN` a directory: generate what is owed from each model, check and audit its claims, compare the model with the C++; exits non-zero and says which step failed | no |
| `domains/gosh/` | 1 | domains and claims | `from/C`: one line, the path in gosh of the file whose class `C` is read where it stands; or `model/C.hpp`, a rewrite, until it can be; `claims/CClaims.lean`, `scripts/C.py`; `gen/` is generated and committed, to be read; `build/` is not kept | no |
| `tools/check.sh`, `tools/red-test.py` | 2 | check | refuses to start without the pinned Lean, a Python with libclang, and the submodule; proves every domain; breaks each and sees it fail; prints `check: PASS` | no |

A component depends only on lower layers. The check reads the subject's repository, and never
writes to it: `SUBJECT`, by default `../gosh`.

## State

| State | Owner (authoritative) | Copies | Max staleness | While wrong, the reader sees |
| ----- | --------------------- | ------ | ------------- | ---------------------------- |
| the generator | oopc, at the commit the submodule names | none | — | — |
| Lean | the release named in `tools/check.sh` | an unpacked copy in `.tools/`, not committed | the check refuses another version | — |
| the subject's code | gosh, at `SUBJECT` | `gen/C.subject.hpp`, the class's text as last read (generated). `model/StunAnswer.hpp`, a rewrite | a class read where it stands: none, it is read again at every check. The rewrite: **unbounded**, nothing says when gosh's file changes (REQ1/DOM-3, queue) | for the rewrite, a proof of something gosh no longer is |
| `gen/` | generated from the model on every check | the committed copy | one check | `git status` shows it changed |

## Essential complexity

- A proof is of a model, and a model is a text: so every "proved" names the text (REQ1/DOM-1, the bundle's hashes).
- Claims are written by what is not trusted, so they are checked as a compiled object, not read (REQ1/AUD-1).
- gosh's code and its model are two texts, and can part (REQ1/DOM-2, REQ1/DOM-3).
- What is not proved must be listed, or "proved" says more than it shows (REQ1/MAP-1, REQ1/SHAPE-4).

## One-way doors

None yet. The repository is private, and nothing in gosh depends on this.

## Decisions

- **oopc is a submodule, not a copy** — REQ1 *Scope decisions* — the generator is still changing,
  and one text of it is better than two — rejected: vendoring a copy, which would fork it — source:
  client, 2026-11-18 ("has oopc as a subproject").
- **The models of gosh are kept here, not in oopc** — REQ1 *Security, law, and ethics* — gosh is
  private and GPL; oopc is public with no licence — source: the agent, 2026-11-17 *(inferred; the
  client has not ruled)*.
- **The invariant is in the C++; what is owed is one generated statement; the claims are audited
  compiled** — REQ1/SHAPE-1, REQ1/AUD-1 — a claims file that held the invariant, or was imported by the
  statements, could change what was proved — source: oopc `docs/FINDINGS.md`, 2026-11-18.
- **A loop's bound is a hint** — REQ1/SHAPE-1 — what is owed says "for some number of rounds there is a
  result", so no statement names a number a person would have to check — source: the same.
- **Proofs by compiled code are refused** (`native_decide`, `bv_decide`) — REQ1/AUD-1 — a claims
  file can swap compiled code for its own — cost: two lemmas took 40 lines instead of 2 — source: the same.

- **A domain is read from gosh's own file, where it stands** — REQ1/SHAPE-1, REQ1/DOM-1 — a rewrite
  is a second text that must be audited whenever gosh changes — rejected: comparing a rewrite with
  gosh's code by test, which shows agreement on the inputs tried and no more — source: client,
  2026-11-18 ("the generator can generate the model").
- **gosh is found by a path, `SUBJECT`, by default `../gosh`** — REQ1/DOM-3 — the check then proves
  gosh as it is in the working tree, uncommitted changes included, and says which commit — rejected
  for now: a submodule, which would pin a commit and prove that — source: the agent, 2026-11-18
  *(inferred; the cheapest to undo)*.

## Deferred

- Not yet: whether the subject is a second submodule, pinned, and not a path. Today it is a path
  (below); the client decides.
