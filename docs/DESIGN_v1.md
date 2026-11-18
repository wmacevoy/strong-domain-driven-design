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
writes to it: `GOSH` (by default `../gosh`) at the branch `GOSH_REF`, as committed, copied to
`.subject/` (not kept).

## State

| State | Owner (authoritative) | Copies | Max staleness | While wrong, the reader sees |
| ----- | --------------------- | ------ | ------------- | ---------------------------- |
| the generator | oopc, at the commit the submodule names | none | — | — |
| Lean | the release named in `tools/check.sh` | an unpacked copy in `.tools/`, not committed | the check refuses another version | — |
| the subject's code | gosh, at the branch `GOSH_REF` | `gen/C.subject.hpp`, the text as last read (generated) | none: it is read again at every check, at the branch's newest commit | — |
| which branch of gosh is proved | `tools/check.sh` (`GOSH_REF`, today `strong/main`) | none | **what gosh's main holds may differ from what is proved**, for as long as a `strong/...` branch is not merged | a proof of a gosh that is not the one released: the check prints the branch and commit, and the map says which domains are on main |
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
- **gosh is read as committed on one named branch** (`GOSH_REF`, in the repository at `GOSH`) —
  REQ1/DOM-3, REQ1/SHAPE-5 — a domain reshaped for a proof lives on a `strong/...` branch, so the
  working tree is not what is proved; an uncommitted change is never proved — rejected: the working
  tree (it proved whatever was checked out); a submodule (a second pin to move) — source: the
  agent, 2026-11-18 *(inferred)*, after the client's "make changes to gosh in strong/* branch".
  That branch is `strong/main`, into which each `strong/...` change is merged once gosh's own
  check passes on it — source: client, 2026-11-18 ("start merging into strong/main").
- **Where gosh's text cannot be read, gosh is reshaped, not rewritten here** — REQ1/SHAPE-1,
  REQ1/SHAPE-5 — the STUN reader became a class of gosh's own, with the socket address made by an
  edge around it; the generator was not taught socket structs or byte-order macros, which it could
  not claim to read rightly — source: client, 2026-11-18.

- **What a method expects of its caller is a type first, a contract second** — REQ1/SHAPE-4 — a
  type's invariant is proved once, where the value is made, and costs every user nothing; a
  contract (`pre`) is for what relates two arguments or an argument to the object, and is owed at
  each call. Neither is checked when the program runs — source: client, 2026-11-18.
- **Contracts are compiled by g++ 16 and read by Clang's library** — REQ1/SHAPE-4 — g++ 16 has
  them and Clang has not; there is no tool that hands over g++'s reading of a program. Clang's
  library shows nothing of a `pre(...)`, so the generator writes each condition again at the head
  of its method's body and reads it there (`gen/C.read.hpp`): one more thing trusted, named in
  oopc's README. No contract is written in gosh yet: `strong/main` builds and passes gosh's check
  with g++ 16 — source: client, 2026-11-18 ("go for it: gcc 16 on a strong/ branch").
- **A broken precondition is a result the model does not have** — REQ1/SHAPE-4 — so nothing new is
  owed of a caller: its own "no memory error" cannot be proved unless it keeps what it calls
  expects. A method called from outside the proved domains is owed given its precondition, and
  that is then an assumption, on the map — rejected: a separate statement for each call, which
  would be a second place for the same fact — source: client, 2026-11-18 ("the burden of proof
  moves to the caller").

- **Two kinds of code, and one rule between them** — REQ1/SHAPE-4 — a proved class calls what says
  `pre(...)`, and each call is proved. Everything else (mosh's core, ssh, and whatever of gosh is
  not yet a proved class) makes only `_checked` values and calls only what expects nothing; a
  `_checked` method tests, and is proved to test before it takes. The check refuses gosh otherwise
  (`oopc/cpp-proof-gen/ingress.py`, after the proofs). It reads words, not meanings: it is
  conservative about a method's name, and blind to a value made through a name no `needs` line
  told it of — rejected: trusting each unproved caller, named on the map (it was one line, and
  would have been every line) — source: client, 2026-11-18.
- **What is proved stands in one place: gosh's `src/strong/`, in the namespace `Strong`** —
  REQ1/SHAPE-4, REQ1/MAP-1 — so "is this proved?" is answered by where a line stands, and the
  check refuses a proved class anywhere else, anything under `src/strong/` that is not proved, and
  a proved method that takes, makes or calls anything `_checked` (the generator refuses that one).
  gosh's layer test lets any part include `strong/`, and `strong/` include only itself. Everything
  else is weak: mosh's core and ssh as a K4, the rest of gosh until it is moved there — source:
  client, 2026-11-18 ("Strong namespace, strong directory. go for it").
- **The check lists every place weak code comes in** — REQ1/MAP-1, REQ1/SHAPE-4 — each use of a
  `_checked` way in by code that is not proved is printed on every run: it is what is left to make
  strong, and a test there is a tripwire that should never fail, not a gate. Today: 2 places, both
  in `meetup/registrations.h` — source: client, 2026-11-18.
- **A test that fails when the program runs ends the process, and says who called** —
  REQ1/SHAPE-4 — gosh's `src/strong/caller.h`: `STRONG_CHECK( condition, from )` writes the
  caller's file and line and what was expected, and aborts; not an answer, not an exception. It is
  the one file under `src/strong/` that is not proved. So code that is not proved hands a way in
  only what it has itself made right: for the meetup's counter that is `meetup_open`'s mask, read
  by a person. The generator reads the test as what the rest of the body may rest on — rejected:
  an answer (`false`), the agent's first choice, which the client undid — source: client,
  2026-11-18.

## Deferred

- Not yet: when a `strong/...` branch becomes gosh's main, and so whether what is proved is what
  is released — the client decides, in gosh.
