# Strong domains: a shape held by design, test and proof

*A draft, by Claude Fable 5.2, 2026-11-19, asked for by the owner: "look at the domain based design
fundamental shape in software engineering exemplars, and write ... the shape of strong domains as a
design / test / prove approach, and how an iterative approach develops the prover. write guidelines
as to how to develop this way."*

It follows the form of the guide's exemplar for domain-driven design
(`software-engineering`, branch `shape-choice`, `exemplars/shapes/domain-driven-design/`), which
follows SE1/D14 (a draft, not released). Unlike the exemplar, the problem here is real: gosh. The
shape items are lettered so nobody reads them as requirements: this project's own are
REQ1/SHAPE-1 to 5 in `REQUIREMENTS_v2.md` (unchanged since v1), in the owner's words, and this document changes none of
them. Where a sentence is the owner's it is quoted; the rest is the agent's reading *(inferred)*.

**What this rests on:** one subject, one owner, three days (2026-11-17 to 19), agents of one
family. Six domains of gosh are proved, on a branch of gosh that is not merged or released. See
*How this was checked* at the end.

## The problem

gosh reads bytes from anyone on the Internet, on a machine its user logs in to. Its boundaries were
tested and fuzzed. A test shows the inputs tried; an attacker needs one that was not. And the code
is now written faster than it can be read: "white hat agents can write code at an unauditable
pace"; "nothing is deployed that cannot be proven secure before full contact" *(owner, 2026-11-18)*.

So the scarce thing is a person's reading. The shape exists to make what must be read small: a
statement of what is proved, a few lines of invariant, and a short list of what is assumed.

## Forces

SE1/D14's seven questions, asked of this problem.

| Ask of the problem | Here | Present? |
| ------------------ | ---- | -------- |
| Does anything change state, and who owns it? | A counter window, a parsed answer, a datagram's head: each small, each with a rule that must always hold. | Strong |
| Is the model ours, or someone else's? | The logic is ours. Socket addresses, byte order, mosh's core, ssh and the cipher are someone else's. | Ours; foreign edges all round |
| Do many cases differ only in data? | The meetup's five kinds of message differ in a mark and a length. | Weak |
| Are there rules people argue about? | The other side of the argument is an attacker, and the argument is over every input at once. | Strong |
| Does a word change meaning somewhere? | "Length", "counter", "pointer": outside, a number somebody sent; inside, a number that is true of the bytes. | Strong |
| More than one surface, or source? | Four kinds of sender: anyone, a key's holder, the host, this machine (`MAP.md`). | Strong |
| Is history a requirement, or will outsiders extend it? | No. | Absent |

One force the table has no row for: **who reads it.** A proof is checked by a machine and trusted
for nothing; what a person reads is the statement. The shape is chosen so the statement is short
and in the programmer's own language.

## Why this shape, and what it shares with domain-driven design

Domain-driven design draws two kinds of border. A **bounded context** is where a word changes
meaning. An **aggregate** is a consistency boundary: state and the logic that guards it, reached only
through its root, its invariant holding whenever no change is under way, and another aggregate
referred to only by its identity (Evans, 2003; Vernon, 2013). A strong domain is the aggregate's
border, made something a program refuses to let be broken. And this shape adds a third axis that
domain-driven design has not got: **what may be relied on**, strong or weak. Outside, a length is
a claim; inside, it is a fact.

| Domain-driven design (the exemplar) | Strong domains | In gosh |
| ----------------------------------- | -------------- | ------- |
| An aggregate: it alone guards every change to itself, reached only through its root | A domain: a set of classes, functions and state that alone guards that state, reached only through its ABI; the simplest one class or one function (SHAPE-B) | `CounterWindow`, `StunAnswer`, `MeetupHeader`: each a domain of one class |
| Another aggregate referred to only by its identity | A domain carried only as an opaque handle that only it opens, fresh or already open *(design)* | not yet: no strong domain is handed another to change |
| The invariant holds outside a transaction; one transaction changes one aggregate | The invariant holds outside an open; a second open of one instance is told so *(design)* | each method of a one-class domain, from any state its invariant allows |
| A bounded context: where a word changes meaning | Each domain is its own: inside, a length is a fact about the bytes | the meetup's messages; the STUN reader |
| (no counterpart) | Strong and weak: where what may be relied on changes | `src/strong/`, namespace `Strong`; everything else |
| What crosses between contexts is chosen by a context map, often a domain event | What crosses the ABI is a value whose type says what holds, or a reference lent for the call and kept by no one | `bounded`, `Datagram` (a `subarray`), plain numbers |
| Rules live in one place that touches nothing | The logic touches no socket or clock; other threads only by a method marked `volatile` or by isolated work; state only the domain's own | every file under `src/strong/` |
| An anticorruption layer: a foreign model's spelling stays at one edge | A weak edge beside the logic | `stun_parse` makes the socket address; `meetup_read_header` copies the ticket out |
| Judged from the imports and where a diff lands | Judged by the check, which refuses | `tools/check.sh` |

**Not events.** Isolation by a boundary that only messages cross, each a copy, private state
answering only messages and sending only messages, is the actor model (Hewitt; Erlang) and the
event-driven style of integration, not domain-driven design as such: there the root's methods are
ordinary calls, and events between aggregates came later (Vernon; event sourcing). This shape
gets the isolation of a message without its copy: a reference lent for one call and kept by no one.

The difference is in the last row. The exemplar's items are judged by a person at a review. Here
each item is either made impossible to break (design), refused by a program (lint, proof), or on a
list of what is assumed. Nothing is held by care.

**The neighbours.**

- *seL4.* The nearest ancestor, and far older: the C that ships is the source, in a subset; the
  kernel was reshaped to be proved; what is assumed is a published list. It claims much more (the
  code does what a specification says) at much more cost. `ALTERNATIVES.md` sets the two side by
  side.

- *Actors and event-driven integration.* The same isolation: state nobody else reaches. Bought by a
  copy at every crossing, and often an allocation; here a borrow buys it for nothing, which is
  what code that must be fast, embedded code included, needs.
- *Functional core, imperative shell.* The same split of logic from I/O. It does not say what is
  true of the core, or what may cross. If "for every input" is not the claim you need, it is
  enough, and this shape is accidental complexity (SE1/D8).
- *Design by contract, tested when the program runs.* The same words (`pre`, invariant). But a
  contract that is tested fails in front of the user, and at an Internet boundary a failed test is
  an attack that worked. Here: "contracts are proven at compile time - they can be ignored at run
  time" *(owner, 2026-11-18)*.
- *A verified language or compiler for the whole program.* Refused here on purpose: mosh's core and
  ssh stay as they are, named as assumed. The shape is for a program that is partly someone else's.

**It stops fitting** where there is little logic and much arranging of the system (the map's rows
for "this machine"), where the state is a library's container the prover does not read, and where
the arithmetic is floating point (queue item 20). There the code stays weak and is called weak.

## The shape

**Strong** means three things together: "strong means isolation, simplified reasoning, and proof
of invariants." *(owner, 2026-11-22)*. *Isolation:* what is true of a domain follows from its own
code, the statements of what it calls and the obligations of its callers, relative to a boundary
of stated K4s. *Simplified reasoning:* so that is all a reader, a person, a proof or an agent,
must hold, and it does not grow as the program does. *Proof of invariants:* what is always true
of the domain's state is shown for every input, by a machine, and audited. The items below hold
one or more of the three.

A template; the blanks are a subject's. Each item names its force, what it refuses, and how it is
judged.

- **SHAPE-A** Two kinds of code, told apart by where a line stands. Strong: under ___, proved.
  Weak: everything else, assumed safe (a K4, checked by other means), including what is assumed
  by decision: ___. Force: a memory error anywhere
  goes past `private`, so a reader must know which kind a line is without reading it. Refuses: a
  proved class anywhere else; anything under ___ that is not proved, beyond the trusted files named
  here: ___. Judged by the check.
- **SHAPE-B** A strong domain is a set of classes, functions and state (their fields,
  thread-locals, retained contexts) that alone guards that state; the simplest is one class or one
  function. Its implementation is the inside, reached only through its ABI, the boundary; what is
  always true of its state is written as its `invariant()`, in the program's language. "a strong
  domain is not a class, is a set of classes, functions, state (thread local/retained). abi is the
  boundary, imp is the inside." "the simplest strong domain would be a single function or class."
  *(owner, 2026-11-22)*. Force: the state has a rule (___) that must hold after any input.
  Refuses: a pointer, reference, view or iterator into its state given out ("no ghosts in the
  machine to haunt later"); a pointer kept; writable state that is not the domain's own. Judged by
  the generator and the lint.
- **SHAPE-C** What is owed is derived from the code, and from nothing else; a proof is a hint,
  audited. Force: whoever writes proofs (an agent, at a pace nobody reads) is not trusted. Refuses:
  a model written by hand; a statement the proof's author could change; "proved" because of who
  said so. Judged by the audit, and by the claims made to cheat that it is seen to refuse.
- **SHAPE-D** What a domain expects of its caller is a type first, a contract second, and never a
  test. Strong code calls what says `pre(...)`, and each call is proved. Weak code comes in only
  through names ending `_checked`, and every such place is printed by the check. Force: ___ is sent
  by someone who may lie. Refuses: a bare pointer and length; a run-time test as the guarantee
  (it is a tripwire that should never fire); a failed test returned as an answer. Judged by the
  check's list, which should only shrink.
- **SHAPE-E** What a proof takes as given of the program around the class is held of the whole
  program, before anything is proved: one name for what a call may write, one owner for anything
  writable, a window that does not move, a context that is retained. Force: "in the end proofs
  should only need to work out the correctness of a domain." Refuses: a proof that reasons about
  its callers; a rule that holds only of the strong part. Judged by the lint, in the full compile:
  compile, lint, prove.
- **SHAPE-F** Someone else's model stays in a weak edge beside the logic, and the subject is
  reshaped to put it there. Force: ___ (socket structs, byte-order macros, a library's types) is
  not ours and cannot be claimed to be read rightly. Refuses: teaching the prover a foreign thing
  so the subject need not change; a strong class that names ___. Judged from the generator's
  refusals and the diff.
- **SHAPE-G** Everything is proved, assumed, or not yet, and a map says which. Force: "proved" is a
  strong word, and what is left out is where the flaw will be. Refuses: "proved" without its text,
  its statement and its assumptions; an assumption found only by reading code; a hidden input
  (open/close, retain/recall, a system or library call) not stated at the boundary. The program's
  claim names that boundary: "strong, assuming ___ is strong". Judged by a person, reading the map
  against the check's lists.

## Design, test, prove: where each claim is held

Every claim about the program is held one of three ways. The work is moving claims leftward.

| Held by | What it is | What it can hold | In gosh |
| ------- | ---------- | ---------------- | ------- |
| **Design** | A type, a place, or a lint rule that makes the claim impossible to break, or unnecessary to say | Things true of the whole program, by its form | `private`; a `bounded` number; a `Datagram` in place of a pointer and a length; a head that keeps positions, not pointers |
| **Proof** | A statement derived from the code, shown for every input, audited | What one class does: no memory error, every loop ends, the invariant holds, and what a proof file says | the six domains; `StunAnswer.proof.cpp`, `MeetupHeader.proof.cpp` |
| **Test** | A run, on the inputs tried | Only what nothing else can reach yet, and whether the other two instruments work | weak code and its fuzzers; speed; the generator's reading, compared with the running C++; the red cases |

Prefer them in that order. A claim held by design costs every later proof nothing. A proof costs
once per class. A test is paid for on every change and still says nothing of the input not tried:
"'does not move' is not provably testable, almost nothing interesting is ... at run time"
*(owner, 2026-11-19)*.

**The working rule:** "whenever you feel nervous 'i should test this' think 'i should prove this'
and what makes reasoning about proving this cleaner" *(owner, 2026-11-19)*. In practice it is a
loop, and the proof is the part that pushes back:

1. Say the worry as a statement over every input. A proof file is the form: C++ that compiles and
   could never be run (`for ( auto& b : every_bytes() )`), with `PROVE( ... )` where a test would
   assert.
2. Try to prove it.
3. What blocks the proof is a finding about the design, not about the prover. Reshape the code
   until the statement is easy: move the foreign thing to an edge, make a number a type, split a
   method, keep positions instead of pointers.
4. Prove it, then break the code on purpose and watch the proof fail.
5. Whatever is still only tested, say so, at the head of the proof file and on the map.

Four times this happened here, each in `FINDINGS.md`:

- **The STUN reader.** Its result was a socket address written through a reference. Reshaped as a
  class keeping its own numbers, with an edge that makes the address. The prover was not taught
  socket structs.
- **The counter.** A replay counter had a class and a proof of its own. Made a `bounded` number, the
  class and the proof were deleted, and an assumption about the caller became a type.
- **The window.** A pointer and a length became `subarray`. Its first shape tested its count at run
  time; the owner removed the test, and what it expects is held by the lint.
- **The meetup's head.** Five `if`s in a row gave the proof 32 paths and it ran out of steps. Two
  small methods, each proved in three lines, and the rest took four seconds. The code a proof finds
  easy is code a person finds easy, for the same reason.

**What a test is still for:** weak code, until it is made strong; the system; speed; and the
instruments themselves. The generator's reading of C++ is not proved, so it is compared with the
compiled class on the same inputs. Every proof is broken and seen to fail; every lint rule is seen
to refuse; the audit is fed claims made to cheat. A check that has never been seen to say no has
not been seen to work (SE1/U3).

## What a proof rests on: its K4s, and who may change or view

A proof is a statement about a text, and it holds only under falsehoods chosen knowingly: K4s
([SE1/U4](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/02-unknowing.md#u4)),
each a place the proof is load-bearing, and each named with what breaks when it comes due. "These
are the K4's. 'change or view' --- that is a security principle. This belongs in the idea of
proof." *(owner, 2026-11-21)*

**The environment** is everything a proof rests on and does not prove:

- the hardware and its firmware (and its faults: a bit that flips);
- the kernel and its drivers;
- the loader and the runtime, which run before `main` and touch everything;
- every library the program links against;
- the program's own unproved code, other threads among it: it shares the process, and it is
  assumed safe (no memory error, it ends, it touches nothing of what calls it beyond what it is
  lent), checked by other means: tests, fuzzers, sanitizers, review;
- the tools that built it: the compiler, the assembler, the linker;
- **anyone with the rights to change or view the program or its memory, before it runs or while it
  does**: a person or process that can write the binary, set its environment (`LD_PRELOAD`), attach
  a debugger, read or write `/proc/<pid>/mem`, or is root;
- and the method's own: the prover's reading of the C++ (compared with the running class, not
  proved), `proofs.py`'s reading of a proof file (run at small bounds, not proved), the hand-read
  primitives (`subarray.h`, `fixed`, `caller.h`, the byte view), Lean's kernel and three axioms.

Input is not on the list. Bytes that come in through the program's interfaces are what the proofs
are about: every input, from anyone. What is assumed is that nothing reaches the state *around*
those interfaces.

**Hidden inputs are on the boundary, not holes in it.** What a method depends on beyond its
parameters and its own state crosses at a place this list already names, and is a K4 stated
there, plainly: open and close (between them a window's bytes are there and stay: whoever makes
one keeps it), retain and recall (a context is retained by a caller: `retain.hpp`), and each
system or library call (that it does what it says). None is a gap in reasoning about a domain
alone; each is a line in the claim. So a program's whole claim names its boundary: gosh is
*strong, assuming ssh and mosh's core are strong*. "hidden inputs as plainly stated k4's. This
handles open/close, retain/recall, and system/library calls as part of the assumption boundary.
for gosh: strong assuming ssh and core are strong." *(owner, 2026-11-21)*

**Change or view.** That is the access-control question, and it is the same line as the proof's:

- **Change** is integrity. A proof is about the state as the class's own methods leave it. Anyone
  who can change that state from outside makes every statement about it void. So who may change
  the process is the proof's boundary.
- **View** is confidentiality, and a proof says nothing about it at all. A key held by a proved
  class is proved used rightly, and is no secret from a debugger, a core dump, or root. Proving
  code does not hide its state.

So the two kinds of work meet: **shrinking who may change or view the process is shrinking the
proof's K4s.** Running a part as its own user, refusing to be traced or dumped, and holding a key
in a process apart are security measures and they are proof measures, for the same reason.

## Calls, handles and threads: the design, not yet held

Today a strong method calls only its own class's methods and the public const methods of another
proved class's value it is handed, and the prover refuses a pointer or reference anywhere (byte
windows, which are hand-read primitives, aside); so nothing a strong domain calls can reach back
into it. This section is the design for what comes next, agreed with the owner
on 2026-11-22. Nothing in it is checked yet; where the lint holds part of it, that is said.

**A domain is not a class** (SHAPE-B): it is a set of classes, functions and state, the simplest
one class or one function. Its invariant is over all of that state, and its parts are read
together, as one text. Today the prover proves one class at a time; a domain of several, with one
invariant across them, is design. A domain has two sides, and each has one rule.

- **The ABI is a borrow.** "the abi callers can pass in references to their state, but that must
  be ephemeral, none is kept" *(owner, 2026-11-22)*. A caller may lend references to its own state
  for the length of one call; the domain uses them only through the lent names and keeps none.
  Actors and event-driven designs get isolation from a boundary only messages cross, each a copy;
  a borrow gives the same isolation for reasoning with no copy: nothing kept after the call (for a message:
  nothing shared once sent), and nothing lent for writing has a second name during it (nobody
  changes a message while it is read). The second is the lint's one-name rule, held today.
- **The implementation is opaque: a handle only the domain opens.** "domain imp is opaque outside
  domain; so the domain must unhide itself --- this leaves room for globals, thread-locals and
  retained values, but only the domain can unwrap it, and at that point know if it is an alias
  (which is required to be allowed)." *(owner, 2026-11-22)*. Every open has two outcomes, and the
  domain's code handles both: **fresh** (its state, the invariant holding) or **already open**
  (the instance is open further up the stack, is another argument of this call, or is open on
  another thread; the fact, and no access). It is domain-driven design's rule that another
aggregate is referred to only by its identity, made a type and given the alias check. A call that comes back into a domain lands in
  *already open* and cannot see its state half-made, so the invariant need hold only where the
  domain is entered and left; and `x.merge( x )` is a case the domain gives a meaning, proved like
  any other input. It is not a trap: a flag that aborts is a run-time test standing in for a
  proof, and *already open* is part of the meaning. It costs a bit per instance and a branch per
  open.

**No cycles through the ABI** is the property: no domain is used again while one of its calls
runs, or a reference lent as "fill in here" could come back to its owner as another "fill in
here", an alias across frames that no single call site shows. The handle holds it locally, so
nothing is proved about the call graph. Recursion inside an implementation is not such a cycle:
"recursion is ok, it is the same restriction as a method call: there is no gaurantee it will
complete or be an out of memory error: this must be a k4, the machine has enough resources to
execute." *(owner, 2026-11-22)*. Enough memory and stack joins the environment's K4s.

**Two kinds: strong, and assumed safe.** "the only way to reason about it is assume code is
either safe or strong. i think we are down to two categories again, the not-strong code is assumed
safe: clear k4, checked by other means." *(owner, 2026-11-22)*. A middle tier, safe code proved
at a cheaper rank, was considered and dropped: for code with state, memory safety rests on the
invariant, so proving safe is most of proving strong, and the expensive part, isolation, both need.
So code that is not strong (weak code, libraries, system calls) is **assumed safe**: it commits no
memory error, ends, and touches nothing of its caller's beyond what it is lent. That is a K4, and
it is checked by other means: tests, fuzzers, sanitizers, review, a language that holds it, a
run-time check that ends the process. A strong domain calls it and stays strong when the call
lends and keeps nothing, and the result is taken as input (strong code already holds for every
input). And **safe code can only carry opaque structure:** "never move, clone,
read, or write" *(owner, 2026-11-22)*. A handle, or anything else it is lent without being shown,
it passes on by reference. The type holds this: copy and move deleted, nothing public, the domain
its only friend. A handle that never moves has its address as its identity, so two opens of one
instance are always seen as one. Where a handle is kept (a global, a thread-local, a retained
context, a callback), how long it lives is open and close, a K4.

**Threads: as if single-threaded.** "the rules allow multiple threads generally, but the reasoning
for non volatile references must be as-if single threaded." and "strong code can run/have
threads, but must call thread safe methods (marked with explicitly volatile args), or call
isolated work." *(owner, 2026-11-22)*. A lender guarantees that no other thread touches what it
lent while the call runs, as it guarantees no second name; that is the C++ memory model's own
bargain (a program without data races behaves as if its threads took turns), made an obligation
on callers, so every proof stays single-threaded. Strong code reaches another thread only by:

- **a thread-safe method,** marked by explicitly `volatile` arguments, so the declaration says
  what other threads may touch. Inside it each read of a volatile argument is an input, any value
  of its type, as a callee's result is;
- **isolated work:** a thread handed only what is its alone, which shares nothing.

A handle two threads can reach opens by an atomic test-and-set, acquire on open and release on
close, so the open is also where the state passes between threads; *already open* on another
thread takes the same branch and does not wait (whether a wait ends is liveness, a K4). A handle
that never crosses threads keeps a plain bit. A volatile reference to something outside the
program, a device register, is a hidden input at the boundary. Today the lint's one owner refuses
a thread started beside state every thread shares, and says each other start, so that a person
reads that what each thread is handed is its alone.

**What is not built:** calls that may change another domain or come back, reference parameters
under the borrow, the handle and its open, and the `volatile` mark.

## How the prover grows

The prover was not designed and then used. Each step was pulled by one class that could not be
proved without it.

| What was tried | What it pulled into the prover | What it pulled out of the subject |
| -------------- | ------------------------------ | --------------------------------- |
| Two toy classes | a class read by Clang, one statement owed, an audit | |
| gosh's STUN reader, written again by hand | loops with a bound as a hint, a byte view, the invariant in the C++ | the reader wants bytes as one value and its result as its own state |
| The owner: no model by hand | a class read from the subject's own file, where it stands | |
| The STUN reader itself | functions as well as classes | the reader reshaped, with an edge |
| What a caller owes | `pre(...)` read; calls between proved classes | the counter as a type (`bounded`) |
| Weak code must get in somehow | `_checked` ways in, proved to test before they take | `src/strong/`; every crossing listed |
| A proof assumed things of its callers | a lint, between the compiler and the proofs | 36 calls changed; 4 globals gone; the session a context |
| Bytes as a pointer and a length | a window read as the byte view | `subarray`, `Datagram` |
| "auditable ... by a regular programmer" | proof files: C++ read as statements | a fuzzer's two claims proved |
| The prover too big to reason about | itself, taken apart: a reader, a tree, writers | |

What stayed the same through every step, and is the method:

- **Refuse by default.** The prover reads a small subset of C++ and refuses the rest, with the
  line. A construct it has not been taught is never guessed at.
- **At each refusal, decide who moves.** If the construct is someone else's model or hard to read
  rightly, the subject is reshaped (SHAPE-F). If it is ordinary C++ a programmer would write anyway
  and reshaping would make the code worse, the subset grows by that one construct.
- **Each thing the prover learns comes with a class of the prover's own that uses it,** a refusal
  for what is just outside it, and a way of breaking it that is seen to fail. The subject's
  classes are not the prover's tests.
- **What it writes is committed and compared.** `prover/judge.sh` proves the prover's own classes
  and fails on one changed byte of output. That is what let five agents take it apart without
  changing what it writes; on its first run it found the committed output was already stale.
- **What is trusted shrinks.** One part asks Clang and refuses; what it read is plain data; the
  writers hold no cursor. The question "did it read rightly?" has one place to be asked.
- **The prover is weak code, and says so.** Its reading is tested, not proved, and that is on the
  list of assumptions. It is held to the shape it enforces where it can be: parts that each answer
  for one thing, with data between them.
- **A lint rule grows the same way:** it first only lists, over the whole subject, so the size of
  the change is known; the subject is migrated; then it refuses.

## Guidelines

For a person or an agent making part of a program strong. Each has its reason; where a reason
does not hold, say so.

**Choosing what to make strong**

1. Start from the map of where bytes and calls come in, nearest the stranger first. That is where
   a flaw costs most.
2. Take one small thing with a rule: a parser, a counter, a table. Not a subsystem.
3. Leave what is someone else's weak, by decision, and write it on the list.

**Shaping a domain**

4. Write the invariant first, as code in the domain (in its class, where it is one). If you cannot
   say what is always true, there is nothing to prove yet. A comment or a requirement is not an invariant.
5. Keep numbers and positions, not pointers. "Inside the datagram" is then a comparison.
6. Take arguments by value, and bytes as a window; once the prover admits it, a reference borrowed
   for the call and kept by no one. Give nothing out that points in.
7. Put the socket, the clock, the environment and the library's types in an edge beside the class,
   a few lines long, so it can be read.
8. Use unsigned arithmetic where a value can overflow; signed overflow has no meaning to prove.
9. Prefer small methods with one decision each. A proof walks every path, and so does a reader.

**Crossing**

10. Say what a method expects as a type. Use `pre(...)` only for what relates two arguments, or an
    argument to the object.
11. Weak code calls `_checked` names only, even where nothing can fail, so that the list of
    crossings is complete.
12. A `_checked` test must not be reachable by bad input from outside: a failed one ends the
    process. Weak code hands in only what it has itself made right.

**Proving**

13. Write the proof file before the proof. It is what a person will read.
14. In a loop that changes an object the next round sees, end the loop with a `PROVE` of what is
    carried from round to round.
15. Never write the model or the statement by hand, and never edit what is generated.
16. No proof by compiled code. It is shorter, and it can be swapped.
17. A claims file is a program. Do not check a stranger's outside a sandbox.

**When the proof is hard**

18. Change the C++ first. Ask what would make the statement obvious to a programmer.
19. Change the prover second, by one construct, with its sample, its refusal and its break.
20. If neither is right today, leave the code weak and say so. Do not write a test and call the
    matter closed.

**Testing what remains**

21. Call a test a test. Say at the head of a proof file what is still only tested.
22. Watch every instrument refuse once: each proof, each lint rule, the audit, the check's start.
23. Keep a fuzzer until every claim it makes is proved, then say which claims are left to it.

24. While working, check only the domain in hand (`tools/check.sh --lite DOMAIN` here; `--lite PART`
    in gosh), and leave out a test of what is proved, marked as such where it stands. A merge and
    CI are held to the whole check, which runs those tests too: a proof rests on the prover's
    reading, and that is only tested.

**Growing the prover**

25. Run the judge before and after any change to the prover. A changed byte is a decision to make.
26. Do not edit the prover while its suite runs.
27. When a part cannot be held in one reading, take it apart, judged by bytes, changing nothing it
    writes or refuses.
28. A fault found and not fixed is written in the queue the same day.

**Working with agents**

29. Give an agent the exact shape, what must not change, and a judge it can run. The cheaper the
    agent, the more exact the brief.
30. Trust nothing an agent returns: run the judge again yourself.
31. Change the subject on a branch of its own, which passes the subject's own check before
    anything is proved of it.

**Saying what is shown**

32. "Proved" names the text, the statement and the assumptions, every time.
33. Every domain tried ends in a finding: what it suggests about the subject's shape, what it
    cost, and what is not shown.
34. The lists the check prints (crossings, shared state, things assumed) are the work left. They
    should shrink; if one grows, say why.

**Learned from gosh's meetup messages** (2026-11-21: REGISTER, TIME, REGISTERED and PASS, each
read where the cipher left it, in gosh `strong/main` 5091dc7 and 7330cf7)

35. When a text has one length, make the length its type (`fixed<N, Of>`), read only at indices
    written out below N. The reader then has no case on the length and no read to prove; the
    proofs of TIME and REGISTER lost their length cases, and REGISTERED's proved on the first try.
36. Find the length once, where the window is made, for every kind (gosh: `Unsealed<T>::read`
    takes N from the reader's own signature). That one line is now trusted, not proved: list it,
    as the edge it is, rather than leave a check in every reader.
37. Tag a window with the class that reads it (`Opened<Register>`), so that the compiler keeps
    one kind's text from another's. The proofs read every window alike, so the tag costs nothing
    to prove.
38. Read bytes where they lie; let one owner keep what an edge gave back, and copy only into
    what is sent on. The owner: "for performance it is crucial that data is not copied just
    because." A copy made to fit a type or a rule is a sign the boundary is in the wrong place.
39. Keep only what the caller needs (a family, a length), not the bytes. A reader that keeps
    numbers proves in a few lines; what the caller compares, it compares in place.
40. Break a construct in a red case, not one spelling of its argument: a case that looked for
    `CounterChecked( counter )` failed when a correct change passed `opened->counter()`.

**Where things stand**

41. The approach and the prover live here; a program's proofs live in the program, beside the
    classes they prove, and run in its own check (gosh, since 2026-11-21: `tools/proofs.sh`).
    This project's check runs that program's proofs by this prover, so that a change here is seen
    on a real program before the program takes it.
42. Name a proof's K4s by who may change or view the program's state, and treat shrinking that set
    as security work: it is the same set. A proof holds against what can change the state only
    through the class; it says nothing of who can view it.

## Five likely changes, and where each lands

Written after three days of changes, not before any (see below).

1. **A wire format gains a field or a kind.** The strong class, its invariant, and its proof file.
   The weak edge changes only where it copies bytes out; the compile-time comparison of the
   numbers said twice fails until both agree. As hoped.
2. **A new source of bytes** (another socket). A weak edge makes a `Datagram`, and the check's list
   of crossings grows by a line. No proof changes. As hoped.
3. **gosh starts a thread.** The lint refuses while anything writable is shared, and 85 such
   things are listed today, all in tests, fuzzers and the test library. They go first. This is the shape's
   price: a rule held of the whole program is paid for by the whole program. Strong code itself may
   run threads by the design (*Calls, handles and threads*): reaching another thread only through a
   method whose `volatile` arguments say so, or by isolated work.
4. **A domain needs floating point,** or a library's container (`Registrations` keeps a map).
   Awkward. The prover reads neither. The class is reshaped to arrays and whole numbers, or the
   prover grows, or the class stays weak. The shape has no answer but those three.
5. **A strong domain must call another, or be handed its own kind.** Calls that say `pre` are
   read. A method taking a value of its own class crashes the generator today (queue item 33). The
   subset is the limit, and the limit is found by trying. A call that may change another domain,
   or come back, waits for the handle (*Calls, handles and threads*).

## Tells

Signs the name is being used without its purpose.

- A class under `src/strong/` whose `invariant()` says nothing its callers rely on.
- A `_checked` test that a datagram from outside can make fail.
- A proof file whose `PROVE` restates the method's body.
- A model written by hand "for now".
- The prover taught a socket struct so the subject need not change.
- "Proved" with no statement beside it.
- The list of trusted files under `src/strong/` growing (two today: `caller.h`, `subarray.h`).
- A lint rule that lists and never refuses, and a list that does not shrink.
- A test kept because the proof was hard, and not called a test.
- A strong class nobody weak calls: proved, and guarding nothing.

## How this was checked, and what would show it wrong

- **Run:** the check (`tools/check.sh`: six domains of gosh proved, 22 ways of breaking them each
  seen to fail), the prover's suite (160 cases), its judge (16 classes, output unchanged). gosh's
  own check passes on the branch the proofs read.
- **Not done, and SE1/D14 asks for it:** no rival shape was written by someone who had not seen
  this one. The five changes were written afterward, so they predict nothing yet; the next real
  change is the first that can be tagged against them. `ALTERNATIVES.md` sets this shape beside ten
  other ways to hold a design by proof; it is by the same agent, so it is not that rival.
- **Not shown:** that any of this is what gosh releases (the branch is not merged); that the
  generator reads C++ rightly beyond where the comparison reaches; that a proof file is read
  rightly (nothing can run one to compare); that the cost of a domain falls as the prover grows
  (it was not measured); that the shape holds for a second subject, a second owner, or a second
  family of agents.
- **Wrong if:** a flaw is found in a strong class inside what its statement covers; reshaping for
  proof makes gosh slower or harder for its owner to read; the lists stop shrinking; or the prover
  grows faster than what it proves, so that what must be trusted got larger, not smaller.
