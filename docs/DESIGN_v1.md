# Design — v1

How we intend to satisfy the requirements, and what we rejected. Every mechanism here should be
replaceable without renegotiating a requirement
([SE1/R5](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/04-requirements.md#r5)).
Written by Claude Fable 5.2 on 2026-11-18 from what exists; reasons nobody stated are *(inferred)*.

## Components and the dependency rule

| Component | Layer | Kind | Contract (one line) | Holds state? |
| --------- | ----- | ---- | ------------------- | ------------ |
| `prover/` | 0 | tool | `prover/prove.sh`, with `DOMAIN` a directory: generate what is owed from each model, check and audit its claims, compare the model with the C++; exits non-zero and says which step failed | no |
| `domains/gosh/` | 1 | domains and claims | `from/C`: one line, the path in gosh of the file whose class `C` is read where it stands; or `model/C.hpp`, a rewrite, until it can be; `claims/CClaims.lean`, `scripts/C.py`; `gen/` is generated and committed, to be read; `build/` is not kept | no |
| `tools/check.sh`, `tools/red-test.py` | 2 | check | refuses to start without the pinned Lean, a Python with libclang, the submodule, and a gosh that has been built; then, in order: compiles what is proved, lints all of gosh's `src`, proves every domain; breaks each and sees it fail; prints `check: PASS` | no |

A component depends only on lower layers. The check reads the subject's repository, and never
writes to it: `GOSH` (by default `../gosh`) at the branch `GOSH_REF`, as committed, copied to
`.subject/` (not kept).

## State

| State | Owner (authoritative) | Copies | Max staleness | While wrong, the reader sees |
| ----- | --------------------- | ------ | ------------- | ---------------------------- |
| the generator | `prover/`, in this repository | oopc's branch `explore/proof-compiler`, where it was written until 2026-11-19 (local, not pushed) | that copy is no longer moved | — |
| Lean | the release named in `tools/check.sh` | an unpacked copy in `.tools/`, not committed | the check refuses another version | — |
| the subject's code | gosh, at the branch `GOSH_REF` | `gen/C.subject.hpp`, the text as last read (generated) | none: it is read again at every check, at the branch's newest commit | — |
| which branch of gosh is proved | `tools/check.sh` (`GOSH_REF`, today `strong/main`) | none | **what gosh's main holds may differ from what is proved**, for as long as a `strong/...` branch is not merged | a proof of a gosh that is not the one released: the check prints the branch and commit, and the map says which domains are on main |
| mosh's core and its `config.h`, which gosh's files include | gosh's pinned core, as a build of gosh leaves it | `.build/core` in gosh's working tree, read by the lint | **it is of whatever gosh's working tree last built, not of `GOSH_REF`** | a lint that read gosh's files against another core's headers; the core is pinned, so they differ only when the pin or the seam's patches moved |
| `gen/` | generated from the model on every check | the committed copy | one check | `git status` shows it changed |

## Essential complexity

- A proof is of a model, and a model is a text: so every "proved" names the text (REQ1/DOM-1, the bundle's hashes).
- Claims are written by what is not trusted, so they are checked as a compiled object, not read (REQ1/AUD-1).
- gosh's code and its model are two texts, and can part (REQ1/DOM-2, REQ1/DOM-3).
- What is not proved must be listed, or "proved" says more than it shows (REQ1/MAP-1, REQ1/SHAPE-4).

## One-way doors

None yet. The repository is private, and nothing in gosh depends on this.

## Decisions

- **The prover is part of this repository, in `prover/`** — REQ1 *Scope decisions* — it was a
  submodule of oopc, on a branch that may not be pushed there, so no clone but this one could
  fetch it; here it is committed and pushed with what it proves — rejected: the submodule (the
  client's first shape, "has oopc as a subproject", 2026-11-18) — source: client, 2026-11-19 ("move
  the proof project to the strong-domain-driven-design project where you can commit and push as
  you see fit (private repo)").
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
  (`prover/ingress.py`, after the proofs). It reads words, not meanings: it is
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
  strong, and a test there is a tripwire that should never fail, not a gate. Weak code calls what
  is proved by a `_checked` name and by no other, even where nothing can fail, so the list is every
  place the two meet: a method that expects nothing and is called only by weak code is named so
  (`StunAnswer::parse_checked`, `is_stun_request_checked`). Today: 18 lines in 9 files, 8 of them
  in tests and fuzzers — source: client, 2026-11-18.
- **A test that fails when the program runs ends the process, and says who called** —
  REQ1/SHAPE-4 — gosh's `src/strong/caller.h`: `STRONG_CHECK( condition, from )` writes the
  caller's file and line and what was expected, and aborts; not an answer, not an exception. It is
  the one file under `src/strong/` that is not proved. So code that is not proved hands a way in
  only what it has itself made right: for the meetup's counter that is `meetup_open`'s mask, read
  by a person. The generator reads the test as what the rest of the body may rest on — rejected:
  an answer (`false`), the agent's first choice, which the client undid — source: client,
  2026-11-18.
- **The full compile is three steps: the C++ compiler, the lint, the prover** — REQ1/SHAPE-4 — a
  proof is of one class alone; what it takes as given of the code around it is not the class's to
  prove, so it is looked for in the program, first. The check compiles what is under `src/strong/`
  (by the usual compiler and by g++ 16 with contracts); then the generator reads each class
  (private fields, no pointer kept, no global), `ingress.py` holds the line between the two kinds
  of code, and `lint.py` holds that at a call of gosh's own, proved or not, no two arguments are one thing,
  that nothing starts a thread, and that nothing outside takes a proved value's address, casts it
  or puts it in a union; then the proofs. The lint reads what is written at a call: one thing
  under two names is not seen, and a signal handler is listed for a person to read. gosh's weak
  code had 36 such calls; the client had them changed ("go ahead and migrate away"), so the rule
  holds of all of gosh and a part can be made strong without first being taken apart. A pair handed
  to the system's (`execl( shell, shell, ... )`) is listed — rejected: refusing only at calls of
  what is proved, the first shape, which left the rest to be found part by part — source: client, 2026-11-19.
- **Bytes are handed to what is proved as a window, not a pointer and a length** — REQ1/SHAPE-4 —
  gosh's `Strong::subarray<iterator>( a, n )`: the `n` elements from `a`, read by `at( i )`, which
  is `*( a + i )`. Making one expects what no test can show when the program runs: that the
  elements are there, one after another, and stay where they are while it exists. That is held
  before the program runs: by the lint, which lets a window be only a local or a parameter and
  lets nothing change what a named one was made from while it is in scope; and, where weak code
  makes one, by that code, each place listed by the lint (3 today). Nothing is tested, and no
  bytes are copied. It is not proved: it keeps a pointer, so `subarray.h` is the second trusted
  file under `src/strong/`, with `caller.h`. The generator reads one as the byte view; the two
  readers' models and proofs did not change — rejected: a window on an array whose size is in its
  type, with a tested count (the agent's first shape: it needed a copy wherever bytes were a
  string's, and rested on a test); the iterator and count as the template's values (only what is
  known when compiling) — source: client, 2026-11-19 ("maybe the template is subarray<iter a,size_t
  n> with the understanding that the s[i]=*(a+i), and that *(a+i) is always
  (*a)+sizeof(a::type)*i for the duration of the existance of the subarray"; "that the problem with
  run-time tests and why we are trying to remove them. 'does not move' is not provably testable,
  almost nothing interesting is ... at run time").
- **No state of a class leaves it** — REQ1/SHAPE-4 — a public method does not give back a pointer,
  a reference, a view or an iterator to its own object's state: what a class keeps is reached
  through its methods while they run, not after. The lint refuses it of a class under
  `src/strong/` (the generator already refused a pointer or a reference there) and lists it of any
  other class: gosh has one, `Bytes::data` in `forwarding/tcp/bytes.h` — source: client, 2026-11-19
  ("no domain structure leaves it (no imp reference leaves through abi). no ghosts in the machine
  to haunt later").
- **One owner, not one thread** — REQ1/SHAPE-4 — an object is used by one thread at a time, and
  objects apart by as many threads as is useful; so nothing that can be written is shared: no
  global, no static in a function, no static member, but one that is each thread's own
  (`thread_local`) or made for many threads (`std::atomic`). The lint refuses one under
  `src/strong/`, lists each one elsewhere, and refuses the start of a thread while there is one.
  gosh starts no thread, and has 89: 70 are the test library's (one per group of tests), 12 more
  are in tests and fuzzers, 3 in the fuzz replay's harness, and 4 in what ships
  (`the_session`, `core-main.h`'s `kept` and `argv`, `relay_log_who`). That a thread is handed
  only what is its alone is not seen by the lint: each start would be listed for a person —
  rejected: refusing every thread, the first shape of this rule — source: client, 2026-11-19.

## Deferred

- Not yet: when a `strong/...` branch becomes gosh's main, and so whether what is proved is what
  is released — the client decides, in gosh.
