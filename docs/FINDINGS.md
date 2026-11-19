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

## 2026-11-18: `bounded` in gosh: the counter's own class and proof are gone, and an assumption moved

**Asked:** "go for it: bounded, proved once for every a and b." "the burden of proof moves to the
caller."

**Seen** (run): gosh's `src/meetup/bounded.h` (on `strong/main`) is proved from its own text, once,
for every type and bounds: 4 statements, 30 lines of claims that never ask what `<=` is, the model
and the C++ agreeing at `uint64_t`, `int64_t`, `double` and `float`. `MeetupCounter` is now a
`typedef` of it. `CounterWindow` is proved as before; two lines of its claims changed (the type
gives both bounds, and the proof wants the upper). 13 broken copies fail.

**Cost:** gosh: one new file, 60 lines; `counter.h` lost its class. Here: `MeetupCounterClaims.lean`
(33 lines) deleted, `bounded_ofClaims.lean` (37) added and never to be written again for another
bound; `from/CounterWindow` names three things it is written with (`needs`).

**What moved, and is not shown:** `MeetupCounter`'s constructor used to mask, so a counter was in
range however it was made. Now it expects that of its caller, and the caller is
`Registrations::datagram`, which is not a proved domain: that the number is within the bounds
rests on `meetup_open`'s mask, read by a person. With g++ 16 the program tests it and ends if it
is not so; with any other compiler nothing does. So one thing proved before is now assumed, on
the map (B6), until `datagram` or `meetup_open` is a domain.

**What it suggests about gosh's shape:** the mask belongs in a small proved function that returns
the type, between the opened message and the window; the generator cannot yet read a function
that returns a class's value.

**What it changed:** the check proves `bounded_of` in place of `MeetupCounter`; queue item 18 is at
review, item 20 is new (signed and floating numbers in an ordinary class: the Bottle).

## 2026-11-18: the way in for code that is not proved; what was assumed an hour ago is tested and proved

**Asked:** "add bounded_checked ... an unchecked domain can only used _checked versions, a
compile-time checked domain does not." "the compiler with the prover can. that is the new
'compile' step."

**Seen** (run): on gosh's `strong/main`, `bounded.h` has `bounded_checked` (made from any number;
tests; says `ok`), and `CounterWindow::take_checked` takes a `MeetupCounterChecked`, asks `ok`, and
only then makes the `MeetupCounter` and calls `take`. `Registrations::datagram`, which is not
proved, calls that, at both places. Five domains proved; 16 broken copies fail, among them
`take_checked` without its test, and `Registrations` making a counter itself, which the rule
refuses with both lines. Run on the gosh of an hour ago, the rule refuses those same two lines.

**What it changed in what is shown:** the assumption the last finding recorded (that
`meetup_open`'s mask keeps a counter within its bounds, read by a person) is gone. A counter from
code that is not proved is tested when the program runs, and the test is proved to be before the use.

**Cost:** gosh: 52 lines added, 6 changed, in 4 files; one comparison and one branch for each
REGISTER and PASS. Here: 22 lines of claims for `take_checked`, 46 for the checked type (once).

**Not shown:** the rule reads words (oopc's `ingress.py` says how): a counter made through a name
it was not told, or by a function that is not proved and returns one, it would not see. Tests and
fuzzers are read as code that is not proved, and pass because none makes a counter.

**What it suggests about gosh's shape:** every proved class that the rest of gosh calls needs one
`_checked` entry for each thing it expects; a class that expects nothing (`StunAnswer::parse`,
`is_stun_request`) is already its own way in.

## 2026-11-18: gosh's proved classes stand in `src/strong/`, and the check holds the line

**Asked:** "strong domains are in the Strong namespace and the src/strong/... strong domains may
not call any _checked abi. the goal is only strong domains (mosh and [ssh] must be weak in the gosh
model as a k4)." "Strong namespace, strong directory. go for it"

**Seen** (run): on gosh's `strong/main`, `src/strong/` holds `bounded.h`, `meetupcounter.h`,
`counterwindow.h` (out of `meetup/registrations.h`), `stunanswer.h` (from `pathfinding/`) and
`stunrequest.h` (out of `meetup/answer.h`), all in `Strong`. gosh's layer test lets any part
include it and refuses it including another part (seen red). Here: five domains proved from
those files; the rule accepts gosh; and it was seen to refuse, in oopc's samples and in a broken
copy of gosh: unproved code that makes a bounded number; unproved code standing under `strong/`;
a proved class elsewhere; a proved method that calls or takes a `_checked`.

**Cost:** gosh: 5 files moved or made, 9 changed; `Gosh::is_stun_request` is kept as a name for
the strong one, for its seven users. No claim changed.

**Not shown:** how much of gosh can be moved there. Today it is 5 files of about 140 in `src/`;
the map's other 24 places each need a reshape first, and the two largest (the session's
datagram, the ssh words) are the K4 by the owner's word.

**What it changed:** `tools/check.sh` gives the rule `STRONG=src/strong`; the map's paths; queue
items 22 (review) and 23 (the three parts of a domain: generated `_checked` entries).

## 2026-11-18: a failed test ends the process; so a datagram must not be able to fail one

**Asked:** "a failed run-time check is a process kill with a single caller stack trace (who called
this) --- not a catchable exception."

**Seen** (run): gosh's `src/strong/caller.h` (on `strong/main`). A `MeetupCounterChecked` made of
2^62 ends the process with `gosh: FILE:LINE: called with what is not expected: A <= raw && raw <=
B` and SIGABRT, with gosh's usual compiler and with g++ 16; made of 7, the window takes it. The
checked type has no `ok` now: one that exists is within its bounds, and `take_checked` is three
lines with nothing to ask. Five domains proved; 16 broken copies fail, among them the checked
type testing nothing.

**What it moved:** with an answer, a wrong counter was dropped. With an end, whoever can make
the test fail can stop the meetup, a process "that runs for months" (map A4). So the test must be
out of reach of what comes in: here it is, because `meetup_open` masks the nonce to 62 bits before
`datagram` hands it over, and the test is reached only after it opened. That is read by a person,
not proved: `Registrations` and `meetup_open` are not strong. It is on the map (B6) as assumed.

**What it suggests about gosh's shape:** a `_checked` way in is for what gosh's own code has
computed; bytes from anyone go first to what is proved to read anything and answer (`StunAnswer`,
`is_stun_request`). Each new way in needs its "can a datagram reach this test, failing?" said on
the map, until its caller is strong.

**What it changed:** `domains/gosh/claims` (the checked type's proof is the bounded one's; the
window's way in lost 8 lines); two red cases; the design's decision, which had said "an answer".

## 2026-11-18: every crossing from weak to strong is a `_checked` name: 18 lines

**Asked:** "the point is to make it strong, and weak code is evident. any call to _checked better
not need it." "weak domains can only call _checked versions, even if those versions cannot fail."

**Seen** (run): on gosh's `strong/main`, `StunAnswer`'s four methods and `is_stun_request` are
named `_checked` (each expects nothing, and its only callers are not proved; no second method was
written). The check refuses a call from weak code by any other name (seen, on a broken copy of
`stun.h`), and lists every one by a `_checked` name: 18 lines in 9 files. Six are `stun_parse`
(`pathfinding/stun.h`), two `Registrations` (`meetup/registrations.h`), one the meetup's loop
(`meetup/serve.cc`), one a name kept for the others (`meetup/answer.h`), and eight are tests and
fuzzers.

**What the list says about gosh's shape:** of the ten lines that ship, only the two in
`Registrations` have a test that could fail. Six of the rest are `stun_parse`, 20 lines that turn
what `StunAnswer` kept into a socket address: an edge that cannot be strong while it names a
socket struct.

**Not shown:** the rule finds a call by the name of what it is called on, declared in the same
file with a proved class's type; an object reached another way it does not see.

**Cost:** gosh: 9 files, a rename in each. Here: the claims' names followed (no proof changed).

## 2026-11-19: a lint between the compiler and the prover; gosh's weak code hands itself to itself

**Asked:** "do the reference rules hold up without changing code? (references are as-if single
threaded for the duration of the reference, distinct parameters are never aliases)"; then "the lint
step is part of a full compile: c++ compile, lint, prove."

**Seen** (run, on `strong/main` at 3c66614): gosh's `src` starts no thread, has no `volatile`, and
installs one signal handler that is a function (the fuzz replay's, in tests). Of 10,451 calls, 26
are of what is under `src/strong/`, and at none are two arguments one thing. Nothing outside takes
a proved value's address, casts it, or holds it in a union. The check now runs compile, lint,
prove, in 179 s (it was 131), and refuses a `stun_parse` that hands `StunAnswer` its own bytes.

**Wrong, and corrected:** the agent first told the client that gosh's shipping code has no call
where two arguments are one thing but `execl( shell, shell, ... )`. That lint skipped a method
called on its own object. With it counted there are 26 such lines outside tests: a method handing
its own field by reference to another of its own methods (`pathfinding/finding.h`, 10;
`copy/filecopy.cc`, 6), or `*this` as the place to send to (`forwarding/tcp/tcpadapter.cc`, 6;
`forwarding/udp/udpforward.cc`, 3). None is a call of what is proved. Each is a line to change
when its part is made strong.

**Not shown:** one thing reached by two names; mosh's core, which has signal handlers of its own
and is not linted; that the core's headers the lint read are those of `strong/main` (they are of
gosh's last build).

**Changed:** `tools/check.sh` (three steps, and it needs a built gosh), `tools/red-test.py` (18
cases), the design's decision and state table, queue item 26.

## 2026-11-19: no call in gosh hands a method itself; two cheaper agents made the change

**Asked:** "go ahead and migrate away --- see if you can guide a lower usage tier to help you."

**Seen** (run): on gosh's `strong/main` at 82c9ecf the lint refuses nothing, and now refuses such a
call anywhere in gosh's own code. 27 lines went by taking a parameter by value (`Addr`, a path, a
`Want`) or by a second local in a test. Nine went by structure: `AdapterPort` and `UDPForwarder`
each handed `*this` to the logic they hold; each now has an `Edge` (the sockets and the functions
the logic calls back) beside the logic, and hands that. gosh's own check passes with the usual
compiler and with g++ 16, its speed comparison among it.

**How:** two agents on Claude Haiku, one after the other, each with the exact lines, the shape of
the fix, three commands to verify by (build, the part's unit tests, the lint), and what not to
touch. 56 thousand and 100 thousand tokens. Both diffs were read whole before they were kept; one
comment was quieted. What made it work was that the lint is a check the agent could run itself.

**Not shown:** a measurement of the copies' cost alone (a 128-byte address per datagram sent; a
path per progress line); gosh's speed test is the only witness.

**Changed:** gosh's `strong/main`; oopc's `lint.py` refuses at every call of the program's own.

## 2026-11-19: the prover lives here

**Asked:** "move the proof project to the strong-domain-driven-design project where you can commit
and push as you see fit (private repo)."

**Done:** `prover/` is oopc's `cpp-proof-gen/` as it stood on the branch `explore/proof-compiler` at
7cb1eee, with `oopcc.py` (four helpers it imports) beside it and that branch's findings as
`prover/FINDINGS.md`. The submodule is gone. Its history stays in oopc's local branch, which is
not pushed and is no longer changed. The check passes from the new place (run).

**Not done:** a Python with libclang is still taken from a checkout of oopc (`CONTRIBUTING.md`).

**Changed:** the design's decision and state table; queue item 8 is no longer blocked.

## 2026-11-19: `subarray<type, size>`: the two readers take a window on an array, and their proofs did not change

**Asked:** "go for it: subarray". Of it, on 2026-11-18: "subarray<type,size> does a windowed
pointer on array<type,type> up to (hard part) memory safety."

**Seen** (run, on gosh's `strong/main` at 4d40094): `Strong::subarray<type, size>` is the first
`count` elements of an array of `size`, made from the array itself; `subarray_checked` tests the
count and ends the process if it is more than the array. A `Datagram` is one of 65,536 bytes.
`StunAnswer::parse_checked` and `is_stun_request_checked` take a `DatagramChecked`. The generator
reads it as the byte view it read a pointer and a length as, and the models came out the same but
for a line number: all 12 statements are proved by the claims as they were. gosh's check passes
with both compilers; this check passes, with a read outside a window still failing its proof.

**What it buys:** a reader was told "these `len` bytes may be read" and had to be believed. Now
`serve.cc` hands over the array `recvmsg` filled, whose size is its type, and a count that is
tested. Where bytes are a string's (`stun_parse`, and a helper the tests use), weak code copies
them into an array first: that its source has that many bytes is weak code's own to get right.

**The hard part, and what holds it:** a window keeps a pointer, so it is not proved; it is the
second trusted file under `src/strong/`. The lint refuses one that is a field, a global, a
static or a function's result, and refuses weak code that makes the unchecked kind or calls
`at()` or `size()` (each seen refused).

**Not shown:** a window that is not a prefix (none is needed yet); an element type other than
`unsigned char`; a window made from an array that is then freed in the same scope (a local array
cannot be; a heap array could); the cost of the copy in `stun_parse` alone, which is on the path
of datagrams that are not the session's (gosh's speed test passed). The prover's own samples have
no reader that takes one.

**The agent's reading:** "size" is the array's size, not the window's; the count is known only when
the program runs. The client has not confirmed it.

**How:** the callers and tests were changed by an agent on Claude Haiku (64 thousand tokens), from
the exact lines and three commands to verify by; its diff was read whole.

**Changed:** gosh's `strong/main`; `prover/prooc.py`, `ingress.py`, `lint.py` (five new cases);
the map's rows A1 and A4; the design; queue item 19.

## 2026-11-19: subarray reshaped on the client's word; two more rules, and what gosh has of each

**Asked:** "maybe the template is subarray<iter a,size_t n> with the understanding that the
s[i]=*(a+i) ..."; to the agent's objection that this loses the test of the count, "that the problem
with run-time tests and why we are trying to remove them. 'does not move' is not provably testable,
almost nothing interesting is ... at run time"; "do the reshape"; "no domain structure leaves it
(no imp reference leaves through abi). no ghosts in the machine to haunt later"; "an instance of
a class can be used by as many concurrent threads as useful (single owner). this means no
writable global state or thread-safe access of global state."

**Seen** (run, gosh's `strong/main` at 8363bf4; gosh's check passes with both compilers, this
check passes, the lint's 36 cases pass):
- `subarray<iterator>( a, n )` replaces the window on an array. Nothing is tested and nothing is
  copied; the two readers' proofs did not change a second time. The lint lists the 3 places weak
  code makes one, and refuses a change to what a named window was made from while it is in scope.
- No state leaves a class: gosh has one public method that gives back a pointer into its own
  object, `Bytes::data` (`forwarding/tcp/bytes.h:35`), in weak code, listed.
- One owner: gosh has 89 things that can be written and are shared by every thread, 4 of them
  in what ships; it starts no thread, so nothing is refused.

**Wrong, and corrected:** the agent's first subarray rested on a test when the program runs, and
argued for it on that ground. And the leaving rule's first run found nothing in gosh, which was
wrong: it did not follow a pointer with a number added, or a local; it finds one now.

**Not shown:** that a thread is handed only what is its alone; state that leaves by a parameter
written through, or by a lambda; a window made from a pointer whose target is then changed; the
prover's own samples have no reader that takes a window.

**Changed:** gosh's `strong/main`; `prover/prooc.py`, `prover/lint.py`; the design (three
decisions); queue items 19, 27, 28.

## 2026-11-19: nothing in what gosh ships is the whole process's; the session is a context

**Asked:** "go ahead and migrate the 4 globals away"; "look at github.com/wmacevoy/retain_recall ..
not sure how to mix this with domain reasoning -> required context with single owner"; "go for it:
vendor retain.hpp and use it for the_session"; "go for it: the retain/recall lint rules".

**Seen** (run): the relay's log name is a parameter of `say`, and the words the core's main is
handed are kept by its caller (an agent on Claude Haiku, 58 thousand tokens; its diff read
whole). gosh's two mains make a `Session` and retain it; `Gosh::session()` recalls it; no call of
it changed, and the seam's patches did not change. The lint follows what is recalled up gosh's
calls: both mains retain before they call, and 11 functions that need a session are called by
nothing of gosh (the hooks, entered from mosh's core): listed, assumed. The lint's 50 cases pass.

**Found on the way:** the lint skipped a call that begins where another call does
(`a.b().c()`, `x::begin()->n`): it took the second for one already read. So some calls of gosh
were never looked at by any rule. Fixed; gosh's count of calls went from 10,537 to 11,226, and
nothing new was refused.

**Not shown:** a call through a function pointer, a `std::function` or a virtual method; that
the core calls its hooks only from the thread and the frame that retained (it is the K4 the
session always rested on, now said by a list); a core that uses a session after gosh's main
has returned (the static outlived main; the local does not).

**Changed:** gosh's `strong/main` (`vendor/retain/`, `src/seam/session.cc`, the two mains,
`relay/process.h`, `seam/core-main.h`, design v2 4.2); `prover/lint.py`; the design; queue 28, 29.

## 2026-11-19: what is claimed of Bottle, as a test that cannot be run

**Asked:** "write a compile-time test for bottle: for (float maxvalue in [0,max_float]) { for
(value in [0,max_float]) { ... } it shoud look like C++ code but would be impossible to actually
run. } this is how invariants should be shown as auditable by humans."

**Seen** (run): `prover/sample/bottle/bottle.proof.cpp` compiles with both compilers against a
`Bottle` of floats; `all<float>( 0, FLT_MAX )` is every float from 0 to the largest (it was run
over 8 of them, and over 3, 256 and no whole numbers), so two of them nested are 2^62 rounds. Two
million sampled pairs agreed with every `PROVE`. `gauge.proof.cpp` says the same of `Gauge`.

**Not shown:** anything proved. The prover reads neither file; `Bottle` has floats, which it
reads in no ordinary class (queue item 20). What a loop means when its body changes an object
the next round sees (it is proved of every state the rounds could leave) is the agent's reading,
written in `forall.h`.

**Changed:** `prover/sample/bottle/` (four files), the prover's README, queue item 30.

## 2026-11-19: the integer bottle's proof is a C++ file a programmer can read

**Asked:** "use the integer bottle - the goal is an auditable proof by a regular programmer."

**Seen** (run): `prover/proofs/Gauge.proof.cpp` is two tests that cannot be run (2^64 and 2^96
rounds), with 7 `PROVE`s. `prove.sh` compiles it, `proofs.py` makes 4 statements of it in Lean,
and one tactic of five lines proves them; the audit accepts them and the kernel, asked again,
does. Broken five ways it fails each time: a `PROVE` that claims more than is so; the carried
`PROVE` taken away; a method the class has not (the compiler); a statement the reader does not
know (refused).

**Learned:** a loop that changes an object the next round sees needs what it carries to be said.
The reader takes it from the `PROVE`s that end the loop and do not name its variable: so the
programmer writes one more `PROVE`, in C++, and no invariant in any other language. Without it
the loop's statement is false, and the proof fails, as it should.

**Not shown:** that `proofs.py` reads a test rightly: nothing compares its reading with a run,
because nothing can run one. A class of gosh's; floats; more than one object.

**Changed:** `prover/proofs.py`, `prover/model/forall.h` (`PROVE` is a function, `all<T>()` is
every value), `prover/prove.sh`, the prover's README, queue item 30.

## 2026-11-19: for the STUN reader, the fuzzing does not matter; for what is around it, it still does

**Asked:** "look at one of the fuzzing tests for stun, and rewrite as a proof the fuzzing does not
matter."

**Read:** gosh's `src/pathfinding/stun-fuzzer.cc` hands `stun_parse` any bytes and watches for two
things: under AddressSanitizer, a read past an exact copy of them; and an answer that is taken and
cannot be written down and read back (it found one on 2026-11-16: an IPv6 address of one link
alone). Then it does the same for `parse_ip_port` on any text.

**Seen** (run): `domains/gosh/proofs/StunAnswer.proof.cpp` says the first two of the reader, in C++:
for every sequence of bytes of every length, after any datagrams before it, `parse_checked` ends
and reads nothing outside them, the invariant holds (nothing, IPv4, or IPv6 not of one link
alone), and the family kept is 0, 4 or 6. The check compiles it against gosh's own header, reads
it, and proves it. The proof is ten lines: it works nothing out, and rests on what was already
proved of `parse_checked`. Made to claim that nothing kept is IPv6, it is not proved.

**What still needs the fuzzer:** `stun_parse`'s own 20 lines, which make a socket address of what
was kept; `format_ip_port` and `parse_ip_port`, which write it down and read it back (the
fuzzer's second check runs through them); and its third check, of any text. None is proved, and
the proof file says so at its head.

**Changed:** `prover/proofs.py` (a loop over every sequence of bytes; a window as an argument; a
method that loops), `prover/model/forall.h` (`every_bytes`), `tools/red-test.py` (19 cases), the
map's row A1, queue item 30.

## 2026-11-19: the meetup's front door, first step: a head is numbers, and it is proved

**Asked:** "whenever you feel nervous 'i should test this' think 'i should prove this' and what
makes reasoning about proving this cleaner"; "go for it: the meetup's front door".

**Seen** (run): `meetup_read_header`, the first thing a datagram from anyone reaches at a meetup
and at an end, is now ten lines over `Strong::MeetupHeader`. The class keeps a kind, an end, the
datagram's length and where what is sealed begins: numbers, and no pointer into the datagram. It
is proved from gosh's own text (12 statements), and `proofs/MeetupHeader.proof.cpp` says in C++,
of every datagram: it ends and reads nothing outside; a head with a ticket is of 52 bytes or
more; what is sealed begins inside; and a head is of the datagram it was handed. gosh's unit
tests of the meetup and of path-finding pass over it unchanged, and its full check.

**What made the proving cleaner, twice:**
- The first shape set the kind by five `if`s one after another. The proof's first step ran out of
  steps on the 32 ways through them. Two small methods (`kind_of`, `right_length`), each proved
  alone in three lines, and the rest went through in four seconds.
- The head keeps where things are, not pointers to them. So "the ticket is inside the datagram"
  is a comparison of two numbers, and the edge that copies it out is three lines to read.

**The numbers are said twice, and the compiler holds them the same:** the class writes the
lengths and marks out; `messages.h` asserts at compile time that they are its own (a mark with
one letter changed does not compile: seen).

**Not shown:** the edge's ten lines; `meetup_open` and the cipher; `meetup_read_register`,
`meetup_addr_of`; `Registrations::datagram`. The fuzzers still cover those.

**Changed:** gosh's `strong/main`; `domains/gosh/` (a sixth domain); `prover/proofs.py` (a
sequence's size in a condition); `tools/red-test.py` (22 cases); the map's row A4; queue 31, 32.

## 2026-11-19: the prover taken apart into parts, with nothing it writes or refuses changed

**Asked:** "think about domain based design for the prover ... it will get too big to reason about
too"; then, of the proposal, "yes to both, steps 1 to 5".

**Seen** (run, on the branch `prover-domains`, then merged): the generator was one file of 1,966
lines and is now a reader (1,090), a tree (479), a model writer (426), and writers for what is owed
(63) and the comparison (319), with a command of 121. The lint is a command and six rule files.
The proof reader is a reader and a writer. The spike's tree is written from the generator's tree,
so what the kernel checks is what the model was written from. `prover/judge.sh` (new) proves the
prover's 16 classes and fails on one changed byte of what is generated: it, the suite (160
cases), the project's check (six domains of gosh, 22 red cases) and the spike's 18 breaks all
pass, and nothing generated differs.

**How:** five agents, each given the exact shape, what must not change, and a judge it could run:
Haiku for step 1 (64 thousand tokens), Sonnet for steps 2 and 3 (101 and 91), Opus for steps 4
and 5 (277 and 210). Two of them built harnesses of their own (81 and 29 inputs) and compared
every message and every file with the old code. Each diff was checked by the judge again, here.

**What the judge was worth:** the first run of `judge.sh` showed that the prover's committed
sample output was stale (it had not been regenerated since the generator changed). Nothing had
been comparing it.

**Not clean, and said** (queue item 33):
- `reader.py` is 1,090 lines: where the subset's rules are is where the size went.
- Which branch becomes its own definition is worked out twice, in the reader and in the model,
  because two refusals depend on it and would otherwise come in another order.
- The proof reader keeps five helpers of its own that differ from the generator's: it sees
  through casts; it refuses `bool` and `int`; it reads a literal as all its tokens; it takes any
  `Strong::subarray<...>` for a window; its refusals say a line and no column.
- The lint's rules each stand alone, but still look at cursors; `ingress.py` still reads words.
- Two faults found and left: a method that takes a value of its own class makes the generator
  recurse until it crashes; a local of a class's type is refused in a branch of several
  statements and allowed in a branch of one.
- The spike now refuses a literal written in brackets (`x = (5);`), which it used to copy; and
  refuses plainly a literal not in decimal, on which it used to crash.

**Changed:** all of `prover/`; the design; queue items 32 and 33.


## 2026-11-19: the approach written down, in the form of the guide's exemplar

**Asked:** "look at the domain based design fundamental shape in software engineering exemplars,
and write ... the shape of strong domains as a design / test / prove approach, and how an
iterative approach develops the prover. write guidelines as to how to develop this way."

**Read:** the guide's exemplar for domain-driven design and SE1/D14 (both on its branch
`shape-choice`, drafts), and this project's design and findings.

**Written:** `docs/STRONG_DOMAINS.md`: the forces, seven lettered shape items with what each
refuses, where a claim is held (design, proof, test) and the loop between them, how each step of
the prover was pulled by one class, 33 guidelines, five likely changes, and tells.

**What the exemplar's form showed:** domain-driven design's items are judged by a person at a
review; every item here is made impossible to break, refused by a program, or on a list of what
is assumed. And the form asks two things this project has not done: a rival shape written by
someone who has not seen this one, and predictions written before the changes.

**Not shown:** anything new; nothing was run for it but the doctor. It is one reading, by the
agent that did the work.

**Changed:** the document; README and CONTRIBUTING point to it; queue item 34. Apart from it,
three lines that still spoke of the prover as a submodule (CONTRIBUTING, the design) are corrected.

## 2026-11-19: ten other ways to hold a design by proof; one is a second reader we could run

**Asked:** "can you look for/think about alternative proof-style approach to design? can you make
a write-up ... about them?"

**Read:** seven web searches, and what the agent recalls. Nothing was run; none was tried on gosh.

**Written:** `docs/ALTERNATIVES.md`: ten approaches asked the same four questions (which text is
first, how many inputs, who proves and what is trusted, what a person reads).

**Learned** *(the agent's reading)*:
- This project's shape is an old one (seL4's: translate the code that ships, prove after), and
  its nearest living relative is Rust read into Lean with agents writing the proofs.
- What it lacks beside the others: a reading of C++ anyone else has checked; anything to say of
  weak code; anything over time or between parties.
- A bounded model checker needs no proofs, reads C++ by Clang, and gosh's datagrams have a
  largest size. It is the strongest rival at the front door, and run beside the proofs it would be
  a second, unrelated reading of the same classes.
- The meetup's messages differ only in data. A format said once as a table would make a new kind
  a row, not a proof.
- Reports (2026-11-13) say contracts may be taken out of C++26. The strong headers say `pre(...)`.
  The outcome was not found.

**Not shown:** any of it. Every "for" and "against" is argument, not measurement.

**Changed:** the document; README and `STRONG_DOMAINS.md` point to it; queue item 35.

## 2026-11-19: seL4 is this shape's ancestor; and the map says nothing of how gosh uses its cipher

**Asked:** "note the seL4 similarity. is there internal information about their approach?
reasoning about cryptography seems important."

**Read:** six more web searches, and gosh's `src/meetup/messages.h` and `ticket.h` on
`strong/main`. seL4's repository of proofs is public; it was not read.

**Learned** *(the agent's reading)*:
- seL4 has three texts (what, how, the C) and proves security of the shortest, carried down by
  refinement. This project has no text above the code but a proof file.
- Their measured cost (about twenty lines of proof to one of C; proof growing with the square of
  the statement; upkeep the main work) argues for small domains, and no cost is measured here.
- They took their C parser off the list of what is trusted by checking what it made against the
  binary. Queue item 25 is the same idea.
- A claim about cryptography is one of five kinds. Four are someone else's or a model's. The
  fifth, that the code uses the cipher as it must (a nonce once, nothing before the tag, keys
  apart), is gosh's own, is where the map is silent, and fits design, lint and proof.
- `ticket.h` makes a key by a seal at nonce zero and argues for it in a comment. No instrument
  holds that. Not a fault found: a place for a cryptographer.

**Not shown:** any of it; nothing was run.

**Changed:** `docs/ALTERNATIVES.md` (two sections), `docs/STRONG_DOMAINS.md` (seL4 named as the
nearest ancestor), queue item 36.

## 2026-11-19: how gosh uses its cipher, read: three claims, and what each rests on

**Asked:** "write it as a finding." *(The agent's reading: of what was said of gosh's use of its
cipher. So gosh's code was read for it, on `strong/main` at `4f894d4`: `src/meetup/ticket.h`,
`messages.h`, `registrations.h`, `serve.cc`, and `src/pathfinding/finding.h`. Read, not run. The
agent is not a cryptographer.)*

**1. A ticket's key is the master key's seal of its id, at nonce zero.** `ticket.h` says why this
is sound (for one full block the cipher is a keyed permutation) and what it rests on: "The fixed
nonce is safe only because the master key seals nothing else, ever."
- *Holds today, by reading:* the master key reaches a cipher in one place, `ticket_key`, called
  from `make_ticket` and from `serve.cc`'s `KeyOf`. Only the 16 bytes of the block are used,
  never the tag.
- *Held by:* a comment, and whoever reads the next change. No type, lint or test would refuse a
  second use of the master key.
- *Could be held by design:* the master key as a type that only `ticket_key` takes.

**2. A nonce is used once under a key.** A ticket's key has four senders (each end, and the
meetup to each end), told apart by the nonce's top two bits; below them is a counter.
- *The four never meet:* a fact about numbers. Not proved until today's step (below).
- *A sender's counter never repeats:* each side starts its counter from the time of day, in
  milliseconds, times 1024, and adds one for each message sealed (`registrations.h`: `sealed`;
  `finding.h`: `meetup_counter = wall_ms << 10`). So a ticket used again by a new process does not
  begin again at zero.
- *What that rests on, and nothing says:* **that the clock is not set back between two uses of
  one ticket by more than the counter has since advanced**, and that no sender seals more than
  1,024 messages for each millisecond it has run. A ticket is good for 30 days; a laptop's clock
  is set back by a correction, a dead battery, or another system on the same machine. gosh's
  documents do not name this as an assumption (searched for; not found).
- *What a repeat would cost* *(the agent's reading, to be judged by someone who knows)*: with this
  cipher a nonce used twice under one key lets what was sealed be compared and, in general, a
  message be forged under that key. What is sealed under a ticket's key is where an end says it
  is, the time, and datagrams the session has already sealed itself. So the session's own text
  stays sealed; what is at risk is the meetup's path: a registration moved, or datagrams passed
  to where they should not go, which the session then refuses.
- *Could be held:* by the end keeping the last counter it used with a ticket, or by a ticket
  being used by one process only; either is gosh's design to decide.

**3. No message is taken twice.** `CounterWindow` is proved for memory and ending, not for this.
`registrations.h` already says what is not closed: a meetup just started remembers nothing, so
for a minute it would take again a REGISTER copied in the minute before.

**Kind:** K4 for the clock (an assumption nobody chose aloud), K1 for the rest.

**Not shown:** that any of this can be reached by an attacker in practice; nothing was run, and
no nonce was seen to repeat.

**Changed:** nothing in gosh. Queue item 36 names the steps; the clock is added to it.

## 2026-11-19: a nonce is a domain: no two senders under a key can make the same one

**Asked:** "continue to move domains in gosh to strong."

**Seen** (run): what a meetup message is sealed with is `Strong::MeetupNonce` on gosh's
`strong/main`: an end, who sealed, and a counter of 62 bits, as numbers. `meetup_seal` and
`meetup_open` are edges over it, with the same bits in the same places; gosh's own check passes
by both compilers. It is proved from gosh's text (14 statements), and
`proofs/MeetupNonce.proof.cpp` says in C++: every 64-bit nonce reads as one sender and one
counter, which write it again; and every sender and counter of 62 bits, written and read, are
themselves. Broken two ways (the counter read with the sender's bits left in; a third end
claimed), each is refused. It is the first thing proved about how gosh uses its cipher.

**What it replaced:** the map said of `meetup_open` that it "gives a nonce's low 62 bits and
nothing else ... read by a person, and if it were wrong, one datagram from a ticket's holder
would end the meetup". That is now the class's invariant.

**What the proving found in the prover** (queue item 38). The proof file was the first with a
bounded loop around another, and the first to hand a method what a method gives:
- the statement of the loop inside left out what the loops around it say of their variables. It
  asked that a third end be read again as itself, which is false, so nothing could be proved.
  Wrong in the safe direction, and wrong: it did not say what the file says.
- `nonce.read_checked( nonce.value_checked() )` was written with a name nothing bound, which
  Lean refuses to read.
Both are fixed in `proofs.py`, with a third proof of `Gauge` that uses them and a break in the
suite. **Nothing compares the proof reader's reading with a run**, and this is what that costs:
the two faults were found only because a true statement would not prove.

**What the boundary rule found in gosh:** a local named `nonce` beside mosh's own field
`m.nonce`: the rule reads words, and refused. The local is named `stamp`. A rule that read
meanings would not have asked for that (queue item 33).

**What it cost:** the class, 81 lines of C++; 114 lines of claims for the class and 87 for the
proof file, most of them one fact (a 64-bit number is its top two bits and its low 62) said in
arithmetic, because proofs by compiled code are refused. gosh's own check was run four times
(twice for the class, twice for the renamed local). The time was not measured.

**Not shown:** that a sender's counter is never used twice; the cipher; the edges' ten lines.

**Changed:** gosh's `strong/main` (2c8bf87); `domains/gosh/` (a seventh domain); `proofs.py`;
`tools/red-test.py` (24 cases); the map's row B6; queue items 36 to 38.

## 2026-11-19: checking while working: one domain, in seconds; the whole check for a merge

**Asked:** "two testing optimizations: run tests/proofs only on the domain being tested, and make
--lite and --heavy tests, check --lite first use --heavy in CI and integrations. --lite should
skip tests that are proven."

**Seen** (run): `tools/check.sh --lite MeetupNonce` here proves and breaks that domain alone in 21
seconds; the whole check takes about three minutes. In gosh (on `strong/main`, 17333d1),
`tools/check.sh --lite meetup` builds, runs the meetup's unit tests and its six outside tests, and
passes in 99 seconds; it leaves out the doctor, the fuzzers under AddressSanitizer, the
reference and the NAT lab, and 20 outside tests of other parts. Each lite run ends
`PASS (lite: ...)` and says what it did not run. Named with a part that is not one, or `--heavy`
with a part, each refuses to start.

**A test of what is proved:** a unit test marks a fact as proved where it stands
(`src/seam/proved.h`, naming the proof), and the lite check does not try it and prints that it
did not. The whole check tries it all the same: a proof rests on the prover's reading of the
C++, which is only tested, so the two agreeing is evidence about the prover.

**How many facts that is today: one** (that a counter's bits above 62 cannot change who sealed a
message). The rule kept: mark a fact only where the proof says the same thing of the same code.
Most of gosh's tests of proved classes also pass through an edge or the cipher, and stay.

**Measured, once each, on this machine:** gosh's whole check, 565 seconds; lite of the meetup, 99.
Here: the whole check about three minutes; lite of one domain, 21 seconds.

**Not shown:** that the parts' tags on gosh's outside tests are the right ones (the agent's
reading of each test's name and comment).

**Changed:** `tools/check.sh`, `tools/red-test.py` here; in gosh, `tools/check.sh`,
`src/seam/proved.h`, one fact of `messages-test.cc`, CONTRIBUTING; guideline 24; queue item 39.
