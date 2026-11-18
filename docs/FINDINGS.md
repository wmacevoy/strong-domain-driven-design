# Findings

What we learned the expensive way: surprises, dead ends, measurements, the attack that worked. The
only document reality writes
([SE1/W10](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/08-work.md#w10)).
Blameless: say what would have found it, not who should have asked. What was learned about the
generator itself is in `oopc/docs/FINDINGS.md`; here is what bears on gosh and on the method.

## 2026-11-18 — the first boundary of gosh proved as a model, and what it took

- **What happened:** gosh's `stun_parse` was written again as a class in the generator's subset
  (144 lines) and proved, for every sequence of bytes of any length: it ends, it reads and writes
  nothing out of bounds, it keeps only nothing, IPv4 or IPv6, and never an IPv6 address of one link
  alone (gosh's REQ17/PATH-8). The claims are 388 lines, checked in 9 seconds. Five ways of breaking
  the parser each make the proof fail (`tools/red-test.py`). Before this project existed (2026-11-17),
  gosh's real function, the model and the Lean model gave the same answers on 15,500 seeded calls
  and on gosh's own fuzz corpus; that comparison is not in this repository yet (queue 2).
- **What it suggests about gosh's shape** *(the agent's reading; the owner judges)*:
  - gosh's function takes `const char*`, a length, and a result by reference. The model takes a
    byte view (a pointer and a length in one value, read only through `at()` and `size()`) and
    keeps its result as its own private state. A boundary that takes bytes from outside may want
    that shape in gosh itself.
  - The model had to say an invariant, and gosh's function has none written: "never an address of
    one link alone" was in a comment and a requirement. Writing it as code is what made it provable.
  - The model uses only unsigned arithmetic, because signed overflow has no meaning to prove.
  - Not proved, and so still only tested: that IPv4 in IPv6's form is kept as IPv4, and anything
    about the port. The invariant does not say them.
- **Kind:** K2 (surprises), three of them, in oopc's findings: a loop needs a stated bound; one
  large function could not be reasoned about until the generator cut it into branches; and the
  claims name intermediate values by the expressions Lean shows, so a change to the C++ may make
  much of them untrue (not yet measured: queue 5).
- **Cost:** two sessions for the generator's loops, byte view, invariant and audit, and this proof.
- **Findable by:** trying a real parser rather than the two toy classes of the first spike.
- **Changed:** this project exists; the map in the README has its first row; queue items 2 to 7.

## 2026-11-18 — the proof was first kept in a public repository, written from private code

- **What happened:** the STUN model, its claims and its inputs were committed on a local branch of
  oopc, which is public and has no licence file; they are written from gosh, which is private and
  GPL-3.0-or-later. Nothing had been pushed.
- **Kind:** K3 (the agent put them beside the generator without asking whose code they came from).
- **Cost:** the oopc branch was rewritten without them; `prove.sh` learned to prove a class kept in
  another directory.
- **Findable by:** asking, before a file is added, where its text came from (AGENTS.md, *Stop and ask*).
- **Changed:** `CONTRIBUTING.md`: nothing written from gosh's code goes into oopc. oopc's suite has
  a loop example of its own (`Zeros`).

## 2026-11-18: the map: few of gosh's boundaries are classes, and most call the cipher

**Seen** (read, not run; gosh at `d0cfd4f`; `docs/MAP.md`): 29 places take bytes or calls from
outside. Six take them from a stranger before any key; one of those has a proved model. Most of
gosh's readers are free functions over `const char*` and a length, or a `std::string`; five are
classes with state of their own (`CounterWindow`, `ReplayWindow`, `RelayFrameParser`, `Fragments`,
`Connections`). Nearly every reader behind a key calls the cipher beside its own logic.

**What it suggests about gosh's shape:** a boundary that is to be proved as it stands needs to be a
class with private state reading a checked view of bytes, not a function over `std::string`. That
is a proposal for gosh's owner, not a change (REQ1/SHAPE-5).

**What it changed:** the queue's second domain is no longer unknown: the map recommends
`CounterWindow`, which may be provable as gosh's own text. Calls in the generator (queue item 6)
are now known to stand before most of the rows behind a key.

## 2026-11-18: CounterWindow, the meetup's guard against replay: proved for memory, not for replay

**Asked:** "do CounterWindow next" (the owner, 2026-11-18). gosh's class at `d0cfd4f`,
`src/meetup/registrations.h`.

**Seen** (the check, run): a model of it is proved. For every counter, from every state: `take`
ends, reads and writes nothing outside its sixteen words, shifts by less than 64, and leaves its
flag 0 or 1. Four broken versions each fail (`tools/red-test.py`).

**Cost** (REQ1/LRN-1): 93 lines of model for gosh's 43; 68 lines of claims; 4 seconds to check;
about two hours of an agent's work, most of it the generator. How much of the claims a change to
the model makes untrue was not measured (queue item 5).

**It could not be proved as gosh's own text.** The map hoped it might. The generator reads no call
between methods (gosh's `test`, `set`, `clear`), no `%` or `/`, no `bool` value, no `memset`, and
read no shift by a variable amount until today (added in oopc, with an example of its own). So the
model is gosh's class written again, statement for statement, and that the two agree is tested:
8,000,000 seeded calls against gosh's own class under AddressSanitizer, 0 differences, by hand on
2026-11-18 and outside this repository (queue item 2).

**What the window is for is not proved.** "No counter is taken twice" is about every history of
calls. The generator derives an invariant of the state, with elements named by literal numbers
only, so the class's `invariant()` says no more than that its flag is a flag. Security first is
shown here; correctness, second, is not (queue item 10).

**About gosh's shape: the class asks something of its caller and does not say so.** With a counter
of 2^64-1 the loop's `i` wraps past it and goes on for the rest of its 1024 rounds, clearing marks
of counters still inside the window. Run against gosh's own class: after 2^64-6, 2^64-4 and 2^64-5
are taken, taking 2^64-1 lets 2^64-5 be taken a second time, and 2^64-1024, which is before the
first, as well. gosh never reaches this: `meetup_open` gives counters below 2^62
(`src/meetup/messages.h`, `MEETUP_COUNTER_MASK`). So it is not a flaw in gosh today. It is "called
correctly", an assumption (REQ1/SHAPE-4), that only another file knows. A proposal for gosh's
owner (REQ1/SHAPE-5): the class says what it needs, or refuses a counter of 2^64-1.

The loop's bound of 1024 rounds is what makes `take` end at all: without it the proof that it ends
fails, and rightly, since at 2^64-1 it would not.

**What it changed:** the generator reads a shift by a variable amount, owed to be defined; the check
proves two domains and sees nine broken versions fail; queue items 9 and 10.

## 2026-11-18: no model by hand: CounterWindow proved from gosh's own file

**Asked:** "the goal is the generator can generate the model --- ow the model must be audited each
time as well." (the owner, 2026-11-18), of the entry above, where the class was written again.

**Seen** (the check, run): `domains/gosh/from/CounterWindow` is one line, `src/meetup/registrations.h`.
The generator finds the class in gosh's file as it stands, takes its text unchanged, and derives
the model and what is owed from it. Proved: the same three statements. Four broken copies of gosh's
file each fail. The comparison runs gosh's own text: 8,001 lines agree. The rewrite is deleted.

**Cost** (REQ1/LRN-1): no lines of model; 76 lines of claims; 4 seconds; about four hours of an
agent's work on the generator (oopc `docs/FINDINGS.md`). The claims for the rewrite did not carry
over: the generated functions differ (three helpers, where the rewrite had them written out), so
the proofs were written again, in half an hour.

**What is still trusted, new with this** (requirements, *Assumptions*): that the class means alone
what it means in its file; and that a class with no `invariant()` claims nothing of its state.

**About gosh's shape:** the generator met ordinary C++ and needed nothing changed in gosh. What it
cannot read is the other shape: a free function over a pointer and a length, which is what
`stun_parse` and most of the map's readers are (queue item 11). The STUN reader is therefore still
a rewrite, and the map now says so.

**What it changed:** the requirements' draft (a model is generated; a rewrite is a debt); the
design (gosh is read by a path, at every check); the map's words; queue items 2, 3 and 11.

## 2026-11-18: the STUN reader reshaped in gosh and proved from its own file; a function read as it stands

**Asked:** "do queue item 11. make changes to gosh in strong/* branch." (the owner, 2026-11-18)

**Seen** (run): three domains proved from gosh's own text, read as committed on `strong/stun-answer`,
and ten broken copies each fail (`tools/check.sh`: PASS). gosh's own check passes on that branch
(PASS, 2026-11-18: unit tests, the fuzzers' replay, the same under AddressSanitizer, and the tests
that drive the programs from outside).

- **`is_stun_request`** (`src/meetup/answer.h`): proved with gosh unchanged, once the generator read
  a function over a pointer and a length. 35 lines of claims.
- **`StunAnswer`** (`src/pathfinding/stunanswer.h`, new on the branch): `stun_parse` as it stood could
  not be read, and should not be: it works on a socket address union with byte-order macros and
  signed arithmetic. On the branch the reading is a class with private state, and `stun_parse` is
  20 lines that make a socket address of what the class kept. What `stun_parse` gives is unchanged,
  by gosh's own tests and fuzz corpus.

**Cost** (REQ1/LRN-1): of the 388 lines of claims written for the hand-made copy, 40 changed, all
by search and replace but three, when the class became gosh's own (a parameter gone, three names,
a result that is now `bool`). So a change of shape that keeps the statements cost the proof almost
nothing; the earlier change, of helpers written out to helpers called, cost it all (76 lines).

**About gosh's shape:** the line a proof wants is the one the fifth point of gosh's own fundamental shape already draws: logic
apart from the system. `stun_parse` had the two mixed; split, the logic is provable and the edge is
small enough to read. The edge is not proved, and is where a wrong byte order would now hide.

**Not shown:** that what is proved is what gosh releases: the class is on a branch, local, not
pushed, not merged (queue item 12). That the caller's pointer has `len` bytes: trusted.

**What it changed:** the check reads gosh at a branch, as committed; no rewrite is left in this
repository; the requirements' draft carries the owner's word on `strong/` branches (REQ1/SHAPE-5).

## 2026-11-18: what a caller owes can be said in gosh's code: g++ 16 compiles contracts, and gosh passes its check with it

**Asked:** "the meetup had a constraint n < 2^62, can't that be part of the type? it doesn't have to
be checked; it just has to be proven." and "go for it: gcc 16 on a strong/ branch" (the owner,
2026-11-18).

**Seen** (run, on this machine, Debian 12, x86_64):
- g++ 16.2 (conda-forge, fetched with pixi, no root) compiles `pre( condition )` on a method with
  `-std=c++26 -fcontracts`. Violated, the program ends and names the condition; with
  `-fcontract-evaluation-semantic=ignore` it compiles to nothing.
- gosh, built that way with no line of it changed, passes its whole check (PASS: unit tests, the
  fuzzers' replay, the same under AddressSanitizer, the tests from outside). gosh's branch
  `strong/gcc16`, local, not pushed: `tools/gcc16.sh`.
- Clang has no contracts (its status page, read 2026-11-18: "No"), and the generator reads with
  Clang's library. Given `pre` defined away on its command line, that library parses a method with
  a precondition; but its Python interface does not hand over the condition inside.

**Not shown:** a contract in gosh itself: none is written yet. That the generator can read one:
it needs a step of its own for the condition. macOS (Apple's Clang) and Windows: a release there
would have to define contracts away, which is what "ignore" does; not tried.

**What it suggests about gosh's shape:** what a method expects of its caller belongs in the method's
own declaration, as a type whose invariant says it (a counter below 2^62, made by masking; a view
of bytes, made where the kernel hands them over) or as a precondition. Then "called correctly" is
owed and proved at each call, and is assumed only where bytes enter the program.

**What it changed:** queue items 14 to 16. Nothing in the check yet.

## 2026-11-18: the counter is a type in gosh, and what the window expects of its caller is proved

**Asked:** "go for it: item 1, then the counter type" (the owner, 2026-11-18).

**Seen** (run): gosh's branch `strong/meetup-counter` (`a509d9d`, local, on top of
`strong/stun-answer`) adds `MeetupCounter` (`src/meetup/counter.h`): one number, kept by its
constructor to its low 62 bits. `CounterWindow::take` takes one. gosh's check passes on the branch
(PASS). Here, from that branch: four domains proved, twelve broken copies fail (`tools/check.sh`:
PASS).

- `MeetupCounter`: at most 2^62 - 1, whatever it is made from. 4 statements, 33 lines of claims.
- `CounterWindow` now has an invariant, in gosh's own text: the highest counter taken is at most
  2^62 - 1. It is provable only because of what `take` is given; so `top + 1` cannot pass the end
  of 64 bits, and the case found on this date (a counter of 2^64 - 1 making it forget) can no
  longer be written down. With a constructor that keeps every bit, `MeetupCounter`'s proof fails.

**Cost** (REQ1/LRN-1): gosh: 57 lines added and 6 changed, in 5 files; no check added at run time (the mask was
already applied where a counter is opened, and is applied once more where the window is called).
Claims: the window's 76 lines became 91; about three hours of an agent's work, most of it the
generator.

**Not proved:** that the two callers in `Registrations::datagram` pass the counter that was opened:
they construct the type from it, and `Registrations` is not a proved domain. That no counter is
taken twice.

**About gosh's shape:** a bound that lived in one file as a mask and was relied on in another now
has a name both files use. Where a number has a meaning (a counter, a port, a length), a type that
can only hold that meaning costs a few lines and moves "the caller keeps to it" from trust to proof.

**What it changed:** the check reads `strong/meetup-counter`; queue items 9, 14, 15 and 17 are at
review; the requirements' draft says "called correctly" is proved inside the program (REQ1/SHAPE-4).

## 2026-11-18: gosh's changes gathered on `strong/main`; the generator reads `pre()`

**Asked:** "start merging into strong/main." And of what a method expects: "the burden of proof
moves to the caller."

**Seen** (run): gosh's `strong/main` (`c736673`, local) is main with `StunAnswer`,
`MeetupCounter` and the g++ 16 toolchain merged. gosh's own check passes on it twice: with g++
16.2 as C++26 with contracts on, and with the usual compiler. The four domains are proved from it
and the twelve broken copies fail, with the generator at oopc `8e778e0`, which reads `pre(...)`
(oopc's findings say how, and what that trusts).

**Not shown:** anything of a `pre` in gosh: none is written. A precondition of a method that a
class other than its own calls is not read yet, but for a constructor's.

**What it suggests about gosh's shape:** the owner's `bounded<a,b,type>` (both ends included) and
`subarray<type,size>` would make `MeetupCounter` and each pointer-and-length pair a type with no
proof of its own; making one from a number or from received bytes is then where a proof, or a
named assumption, is owed (queue items 18, 19).

**Cost:** none here: no model or claims line changed.

**What it changed:** the check reads `strong/main`; queue item 16 is at review, and 18 and 19 are
new; the requirements draft carries the owner's two assumptions about references.
