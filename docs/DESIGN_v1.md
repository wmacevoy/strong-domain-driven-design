# Design — v1

How we intend to satisfy the requirements, and what we rejected. Every mechanism here should be
replaceable without renegotiating a requirement
([SE1/R5](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/04-requirements.md#r5)).
Written by Claude Fable 5.2 on 2026-11-18 from what exists; reasons nobody stated are *(inferred)*.

## Components and the dependency rule

| Component | Layer | Kind | Contract (one line) | Holds state? |
| --------- | ----- | ---- | ------------------- | ------------ |
| `oopc/` (a git submodule) | 0 | tool | `cpp-proof-gen/prove.sh`, with `DOMAIN` a directory: generate what is owed from each model, check and audit its claims, compare the model with the C++; exits non-zero and says which step failed | no |
| `domains/gosh/` | 1 | models and claims | `model/C.hpp`, `claims/CClaims.lean`, `scripts/C.py`; `gen/` is generated and committed, to be read; `build/` is not kept | no |
| `tools/check.sh`, `tools/red-test.py` | 2 | check | refuses to start without the pinned Lean, a Python with libclang, and the submodule; proves every domain; breaks each and sees it fail; prints `check: PASS` | no |

A component depends only on lower layers. Nothing here depends on the subject's repository yet
(REQ1/DOM-2 and REQ1/DOM-3 will, by a path given to the check, read only).

## State

| State | Owner (authoritative) | Copies | Max staleness | While wrong, the reader sees |
| ----- | --------------------- | ------ | ------------- | ---------------------------- |
| the generator | oopc, at the commit the submodule names | none | — | — |
| Lean | the release named in `tools/check.sh` | an unpacked copy in `.tools/`, not committed | the check refuses another version | — |
| the subject's code | gosh | each model is a copy, written again | **unbounded today**: nothing says when gosh's file changes (REQ1/DOM-3, queue) | a proof of something gosh no longer is |
| `gen/` | generated from the model on every check | the committed copy | one check | `git status` shows it changed |

## Essential complexity

- A proof is of a model, and a model is a text: so every "proved" names the text (REQ1/DOM-1, the bundle's hashes).
- Claims are written by what is not trusted, so they are checked as a compiled object, not read (REQ1/AUD-1).
- gosh's code and its model are two texts, and can part (REQ1/DOM-2, REQ1/DOM-3).
- What is not proved must be listed, or "proved" says more than it shows (REQ1/MAP-1, SHAPE-4).

## One-way doors

None yet. Nothing is published, and nothing in gosh depends on this.

## Decisions

- **oopc is a submodule, not a copy** — REQ1 *Scope decisions* — the generator is still changing,
  and one text of it is better than two — rejected: vendoring a copy, which would fork it — source:
  client, 2026-11-18 ("has oopc as a subproject").
- **The models of gosh are kept here, not in oopc** — REQ1 *Security, law, and ethics* — gosh is
  private and GPL; oopc is public with no licence — source: the agent, 2026-11-17 *(inferred; the
  client has not ruled)*.
- **The invariant is in the C++; what is owed is one generated statement; the claims are audited
  compiled** — SHAPE-1, REQ1/AUD-1 — a claims file that held the invariant, or was imported by the
  statements, could change what was proved — source: oopc `docs/FINDINGS.md`, 2026-11-18.
- **A loop's bound is a hint** — SHAPE-1 — what is owed says "for some number of rounds there is a
  result", so no statement names a number a person would have to check — source: the same.
- **Proofs by compiled code are refused** (`native_decide`, `bv_decide`) — REQ1/AUD-1 — a claims
  file can swap compiled code for its own — cost: two lemmas took 40 lines instead of 2 — source: the same.

## Deferred

- Not yet: where the subject's code is read from for REQ1/DOM-2 and DOM-3 — a path given to the
  check, or a second submodule; the client decides with the first domain that needs it.
