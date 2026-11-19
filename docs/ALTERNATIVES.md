# Other ways to hold a design by proof

*A draft, by Claude Fable 5.2, 2026-11-19, asked for by the owner: "can you look for/think about
alternative proof-style approach to design? can you make a write-up ... about them?"*

`STRONG_DOMAINS.md` says what this project does. SE1/D14 asks for a rival before building; none
was written. This is the nearest thing so far: the other known ways to make "it is proved" part of
how a program is designed, each asked the same questions, and what each would mean for gosh.

**What this rests on.** Recalled by the agent, and thirteen web searches on 2026-11-19 (sources at
the end; a claim that was searched is marked *(searched)*, the rest is *(recalled)* and not
checked). **Nothing here was run, and none of these was tried on gosh.** It is also not the blind
rival D14 asks for: it is written by the agent that wrote the shape it is compared with.

## Four questions that tell them apart

1. **Which text comes first?** The code that ships, a specification the code is made from, or a
   description of the data.
2. **What is shown, of how many inputs?** Every input; every input up to a size; or the inputs
   that happen, when they happen.
3. **Who does the proving, and what must be trusted?** A person or agent writing proofs that are
   checked; a solver that searches; a compiler's rules; nothing but a run.
4. **What does a person read to know what was shown?**

This project's answers: the code that ships, read where it stands; every input; an agent writes
proofs, trusted for nothing, audited against a statement derived from the code, and the reading of
the C++ is trusted; a person reads a few lines of invariant and a proof file in C++.

## The alternatives, in short

| Approach | Text first | Inputs | Who proves | Read by a person | For gosh |
| -------- | ---------- | ------ | ---------- | ---------------- | -------- |
| **This project** | the C++ that ships | all | agent; kernel checks | invariant, proof file in C++ | six domains |
| 1. Translate C to a prover (seL4, VST) | the C that ships | all | experts, by hand | a specification in the prover's language | the same idea, much older, C only |
| 2. Annotate the source (VeriFast, Frama-C, SPARK) | the code, with contracts written in it | all | a solver, guided by annotations | the annotations | C++ in part |
| 3. Search to a bound (CBMC, ESBMC, Kani) | the code | all up to a size | a solver, unaided | the harness and the bound | a datagram has a largest size |
| 4. Sound static analysis (Astrée, Frama-C Eva, IKOS) | the code | all | the tool, unaided | the alarms left over | memory errors only |
| 5. Describe the data, generate the reader (EverParse) | a format description | all | the generator, once | the format | the meetup's messages, STUN |
| 6. A language that cannot say the error (Wuffs, Rust, SPARK) | code in that language | all | the compiler | the code | a second language |
| 7. Write the proof first, extract the program (F\*, Coq, Dafny, B) | the specification | all | experts | the specification | refused already |
| 8. Types alone (parse, don't validate; typestate) | the code | all, for what a type can say | the compiler | the types | already done in part |
| 9. Model the design, not the code (TLA+, Alloy, Tamarin) | a model of the protocol | all, of the model | a model checker | the model | what our proofs do not reach |
| 10. Contain it when it runs (hardening, sandbox, CHERI) | the code | the ones that happen | nobody | nothing | the weak part |

## Each one

For each: what it is, what speaks for it here, what speaks against, and what to take from it.

### 1. Translate the C that ships into a prover

seL4's kernel is the example: a parser turns C into the prover's own terms, a tool (AutoCorres)
lifts that to something a person can reason about, and proofs are written by hand in Isabelle
*(searched)*. VST does the same in Coq, resting on a compiler that is itself proved (CompCert)
*(recalled)*. Aeneas does it for Rust into Lean 4, the prover used here, and in 2026 it is being
used on Microsoft's SymCrypt and Signal's library, with proofs written by AI provers *(searched)*.

- **This is our shape.** Code first, where it stands; a translation that is trusted; proofs
  checked by a kernel. Aeneas with agents writing proofs is the closest relative found.
- **For:** twenty years of finding what goes wrong. seL4 later removed the compiler and the C
  parser from what is trusted by checking the binary against the proof *(recalled)*; that is the
  known answer to "the generator's reading is not proved".
- **Against:** C or Rust, not C++. The proofs are specialists' work and long: seL4's are many
  times the size of its code *(recalled)*.
- **Take:** how they treat the translator. AutoCorres proves, each time it runs, that what it
  hands the person agrees with what the parser read *(searched)*. Our reader is tested against the
  running class; the same idea is the spike's tree, checked by the kernel (queue item 25).

### 2. Write the contract in the source, and let a solver discharge it

Frama-C (C only *(searched)*), VeriFast (C, Java, Rust, and C++ in part: no templates as of its
2022 report *(searched)*), SPARK for Ada, Dafny and Verus for their own languages. The programmer
writes preconditions, invariants and loop invariants beside the code; a solver proves each
function against them.

- **For:** no second text and no proof file: the claim is at the line it is about. Loop
  invariants are written by the programmer in the program's language, which is what our proof
  files reach for.
- **Against:** the annotations are in a logic of their own (separation logic for VeriFast), which
  is not what "a regular programmer" audits. When a solver fails, it says "could not prove" and
  little else. The solver is trusted; here only Lean's kernel is.
- **Take:** SPARK's levels *(recalled)*. It names a ladder: the subset holds; data flows are right;
  no run-time error; stated properties; full correctness. Each domain here could say which rung it
  is on. Today that is said in sentences on the map.

### 3. Search every input up to a bound

CBMC and ESBMC for C and C++, Kani for Rust. No proof is written: the tool turns the program and
"no bad read, no overflow, this assertion holds" into one question for a solver, for all inputs up
to a stated size. ESBMC reads C++ through Clang, as our generator does, and checks bounds, use
after free and overflow *(searched; how much of C++17 it reads was not confirmed)*.

- **For:** it is the cheapest of all of these, and gosh's inputs have a largest size: a meetup
  datagram is at most 1,551 bytes, a STUN answer is short. Where the bound covers every input,
  "up to a bound" is "all". And it needs no subset: it could read weak code as it stands.
- **Against:** it gives a yes or a counterexample, and no statement a person reads but the
  harness. A loop over 1,551 bytes may be more than the solver finishes. It trusts a solver and
  its own model of C++.
- **Take:** this is the strongest rival for memory safety at gosh's front door, and it is also a
  **second reader of the C++** that shares nothing with ours. Run on the six strong classes, a
  disagreement would be a fault in one of the two readings, which is the thing this project trusts
  most and has shown least. See *What I would do*.

### 4. Sound static analysis

Astrée, Frama-C's Eva, NASA's IKOS *(recalled)*. The tool computes, for every variable at every
line, a range that covers every run, and reports each place it cannot show safe. No proofs and no
bound; it is used on flight software.

- **For:** whole programs, unaided. It answers "no memory error anywhere", which a proof of one
  class cannot.
- **Against:** it raises alarms that are not errors, and somebody reads each one. It proves the
  absence of crashes, not an invariant. The strong ones are commercial; C++ is covered in part.
- **Take:** the question it answers is the one our map leaves open: the weak code. A proof never
  will reach mosh's core.

### 5. Describe the data, and generate the reader

EverParse: a format is written much like a C struct with conditions, and the tool writes a C
validator that is proved safe, correct against the description, and to read each byte once. Every
packet through Hyper-V's virtual network is checked by code made this way: about 100 message
kinds, 5,000 lines of description making 25,000 of C *(searched)*.

- **For:** it fits a force this project marked weak and may have under-weighed: the meetup's five
  messages, and STUN's attributes, **differ only in data**. Nobody proves anything per format; the
  description is the statement, and a person reads that.
- **Against:** the owner has refused generating the code that ships ("The gen would not generate
  C"). It is a toolchain in F\*, which is a large thing to carry. It makes validators, not the
  logic that follows.
- **Take:** without generating anything: say a format once, as data in the C++ (a `constexpr`
  table of kinds, marks and lengths), and prove the one reader of the table. `MeetupHeader`
  already keeps numbers and is checked against `messages.h` by `static_assert`; that is half of
  this. A new kind of message would then be a row, not a proof.

### 6. A language that cannot say the error

Wuffs is a small language for reading untrusted files: an addition does not compile unless the
compiler can show it cannot overflow, an index unless it is in range; it writes C, with no test
left at run time *(searched)*. Rust rules out one thing under two names and use after free by
ownership. SPARK rules out aliasing by its rules for parameters *(recalled)*.

- **For:** the rule is held of every line by the compiler, with nothing to audit. Our lint (one
  name, one owner, nothing leaves, a window) is these languages' rules, written again for C++ and
  checked by a program of ours.
- **Against:** a second language beside C++, and mosh's core stays C++ whatever is done. Wuffs
  generates the C that ships. It shows safety, not an invariant.
- **Take:** honesty about what the lint is: a small, unproved borrow checker. Where its rules
  differ from Rust's or SPARK's, that difference should be on purpose. Nobody has compared them.

### 7. Write the proof first, and extract the program

HACL\* (cryptography in Firefox and Linux, written in F\* and extracted to C), the B method
(a specification refined step by step into code; a Paris metro line runs on it), Coq extraction,
Dafny *(recalled)*.

- **For:** the strongest results there are come from here. Nothing is ever unproved, because the
  code does not exist before the proof.
- **Against:** refused in this project's shape: C++ is the source. The program is no longer
  written by programmers in their language. What ships is a generator's output.
- **Take:** refinement as an idea. Our invariant says what is always true; it does not say what a
  method is *for*. A proof file states that in C++; the B method's lesson is to write the short
  statement before the code. Guideline 13 says so.

### 8. Types alone

"Parse, don't validate" (a function that checks returns a type that carries the fact),
typestate (an object's type changes with what may be done next), refinement types (Liquid
Haskell), and language-theoretic security: recognise the whole input against a grammar before
acting on any of it *(recalled)*.

- **For:** it costs nothing after it is written and needs no tool. `bounded` and `Datagram` are
  this. So is the rule that weak code gets in only by `_checked`.
- **Against:** a C++ type can say little, and nothing checks that the function making the type
  told the truth. That gap is exactly what the proofs here fill.
- **Take:** language-theoretic security's rule fits `MeetupHeader`: it reads the whole head and
  keeps numbers before anything acts. It could be said as a guideline: a strong reader finishes
  recognising before any weak code touches the bytes.

### 9. Model the design, not the code

TLA+ and Alloy for state machines; Tamarin and ProVerif for protocols with an attacker (used on
TLS 1.3 and Signal) *(recalled)*. A small model of the protocol is checked for every interleaving
or every attacker, before or beside the code.

- **For:** it holds what no proof of a class holds. This project says of `CounterWindow`: memory
  and ending are proved, and "not that no counter is taken twice". Replay, the meetup's exchange,
  what a ticket's holder can do: those are properties of several parties over time.
- **Against:** a model is a second text, and nothing ties it to the C++. The owner refused that
  for models of classes.
- **Take:** a different rung, not a rival. Where the property is of one class (no counter twice),
  it is an invariant we have not yet written, and Lean is already here. Where it is of the
  protocol, a model is the only instrument, and the map should say "modelled" as its own word,
  apart from "proved".

### 10. Contain it when it runs

Hardened standard libraries, bounds checks added by the compiler, sanitizers, capability hardware
(CHERI), and a sandbox that takes away what the process may do *(recalled)*.

- **For:** it covers all the code, today, including mosh's core.
- **Against:** it is a test at run time: "that the problem with run-time tests and why we are
  trying to remove them" *(owner)*. A caught error is still a dead session.
- **Take:** two of these are different in kind. A sandbox does not test anything; it bounds what a
  flaw in weak code can reach, which a proof of strong code never will. And a kill on a memory
  error in weak code is the same decision already made for `STRONG_CHECK`. Whether gosh wants
  either is gosh's requirement, not this project's.

## seL4, more closely

The owner, 2026-11-19: "note the seL4 similarity. is there internal information about their
approach?" There is, and it is public: the specifications and every proof are in one repository
(`seL4/l4v`), with papers on the method, on what is assumed, and on what the proofs cost to keep.
What follows is from six searches and recall; the repository itself was not read.

**How it is built.**

- **Three texts, two proofs.** An abstract specification says what the kernel does. An executable
  specification says how; it began as a prototype in Haskell, which the designers could run, and
  is translated into the prover. Then the C. One proof shows the executable specification refines
  the abstract one; a second shows the C refines the executable one *(searched)*.
- **Security is proved of the short text and carried down.** Integrity and confidentiality are
  shown of the abstract specification, and hold of the C because refinement keeps them
  *(searched)*.
- **The C is written by hand, in a subset its parser reads,** and the kernel was designed to be
  proved: almost no concurrency inside it, little global state, a design settled in the prototype
  between the people who build kernels and the people who prove them *(recalled)*.
- **What is assumed is published as a list:** at first the compiler, the assembly, the hardware
  and the boot code *(searched)*.
- **Then the compiler and the C parser were taken off the list.** A tool proves that the binary
  the ordinary compiler made refines the same formal text the proofs are about: "the method by
  which we arrive at this artefact is irrelevant" *(searched: Sewell, Myreen and Klein, 2013)*.
- **The proofs are kept with the code.** A change to the kernel is not accepted until the proofs
  pass again *(recalled)*.

**What it cost.** About 200,000 lines of proof for about 10,000 of C, some twenty to one; 25
person-years in all, 12 on the kernel itself. Their own later measurements: effort grows with the
size of the proof, and the size of a proof grows about with the square of the size of the
statement it proves. Keeping the proofs alive as the code changes became the main work, over a
decade *(searched; the figures are from secondary sources and do not all agree)*.

**The same, here.** The code that ships is the source, in a subset. The subject is reshaped so it
can be proved. One owner and no threads. A named list of what is assumed. A kernel checks proofs
nobody trusts.

**Different, and which way it cuts.**

| | seL4 | Here | |
|---|---|---|---|
| What is claimed | the code does what a specification says | no memory error, every loop ends, the invariant holds, and what a proof file says | theirs is far the stronger claim |
| Where the statement comes from | written by hand, and read by people | derived from the code; the invariant is a few lines of the C++ | less to audit here, because less is said |
| Who writes proofs | specialists | agents, trusted for nothing | theirs took person-years; ours has no measured cost |
| The reading of the code | a parser of long standing, later checked against the binary | ours, three days old, compared with runs | theirs is checked; ours is not |
| How much is proved | the whole kernel | six small classes of one program | |

**What to take.**

1. **A short text above the code.** seL4 proves security of the abstract specification, not of
   the C. Here there is no such text: a proof file is the nearest thing. For anything about
   several calls or several parties (replay, a nonce used once), a short specification that the
   class is shown to refine is their answer, and it is a known one.
2. **Their measurement is an argument for small domains.** If proof grows with the square of the
   statement, six statements of one class each cost far less than one statement of six. It is
   also a warning: REQ1/LRN-1 asks what each domain cost, and no cost has been measured here.
3. **The reader comes off the list by checking what it made, not by trusting how.** That is the
   spike (queue item 25): the kernel checks each generated model against one statement of what
   the C++ means. seL4 shows the idea carries to a whole kernel.
4. **Proofs pass before a change is accepted.** Here gosh's `main` is not what is proved, and the
   design says so. Their rule is the end state, and it is the owner's to decide for gosh.

## Reasoning about cryptography

The owner, the same day: "reasoning about cryptography seems important." It is where this
project says least. The map says the cipher is assumed. It does not say what is assumed *of
gosh* in using it, and that part is gosh's own.

**A claim about cryptography is one of five kinds, held by different instruments.**

| | The claim | Who holds it, elsewhere | In gosh today |
| - | --------- | ----------------------- | ------------- |
| 1 | The primitive is secure: AES is a good block cipher; OCB with it seals and proves | mathematics, on paper; some checked by machine (EasyCrypt, CryptoVerif) *(recalled)* | assumed |
| 2 | The code computes the primitive | HACL\* and EverCrypt: memory safety, the same answers as the standard's own definition, and nothing secret decides a branch or an address; in Firefox, Linux, WireGuard *(searched)*. Microsoft's SymCrypt in Rust, proved in Lean through Aeneas *(searched)* | mosh's own AES-OCB, assumed with mosh's core |
| 3 | Time and memory say nothing of a secret | a type for secrets that has no branch and no index: the compiler refuses the rest *(searched: HACL\*)* | not looked at |
| 4 | The protocol is secure, the primitive taken as perfect | a model with an attacker: Tamarin, ProVerif, CryptoVerif. In 2023 Tamarin models of sealing found attacks that rest on a nonce used twice, and on small differences between ciphers *(searched)* | the meetup's exchange: tested, not modelled |
| 5 | The code uses the primitive as the protocol says: a nonce once under a key; nothing acted on before it is proved genuine; keys kept apart | the newest work: the Signal project in Lean reads the real Rust, with the primitives and the protocol written as definitions that cryptographers review before any proof is begun *(searched)* | comments, and unit tests |

Kinds 1 and 2 are someone else's, and stay assumed: mosh's core is not touched (gosh's own REQ10/SHAPE-1).
Kind 5 is all gosh's, and is where a wrong line is an attack however good the cipher is. It is
also the kind a strong domain can hold.

**How kind 5 fits this shape.** The cipher is a weak domain by decision. Treat it the way the
field treats it at kind 4: as perfect, *given what it expects of its caller*. Write that contract
down, and the caller's side of it is ordinary work for design, lint and proof:

- **A nonce once under a key.** gosh makes a nonce from a direction (two bits: who sealed, and
  for whom) and a counter under 2^62 (`messages.h`). Two claims hide there. *The four directions
  never meet* is a fact about numbers: provable now, as a proof file of a few lines, once the
  function stands under `src/strong/`. *A counter is not used twice by one sender* is a claim
  about a history of calls: a class that seals and counts, with the invariant "every nonce handed
  out is below the next", which needs what is owed to speak of earlier calls (queue item 10).
- **No counter taken twice, on the way in.** `CounterWindow` is proved for memory and not for
  this. It is the invariant not yet written, and it is the whole purpose of the class.
- **Nothing before the proof of who sent it.** A type: text that has been opened is a value only
  the cipher's edge can make, and a strong reader of sealed text takes that type and not a
  `Datagram`. Held by design, with one lint rule (who may construct it). No proof.
- **Secrets.** A key or an opened text as a type with no comparison that returns early and no
  use as an index, as HACL\* does it. Held by design. Whether gosh has such a place has not been
  looked at.

**One place to read with a cryptographer.** `src/meetup/ticket.h` derives a ticket's key by
sealing its 16-byte id under the master key with the nonce fixed at zero, and argues in a
comment that for one full block this is a keyed permutation. That is a claim of kind 1 and 4,
made in a comment, held by no instrument. It may well be right. What it rests on (that the
master key seals nothing else at nonce zero; that only the block and never the tag is used) is
exactly what a model checks and a memory proof cannot. *(Read by the agent, who is not a
cryptographer; not a finding of a fault.)*

**What I would do,** in order. None is started.

1. **Write the cipher's contract on the map:** what gosh assumes of mosh's cipher, and what the
   cipher expects of gosh, in five or six lines. Today "assumed" names the cipher and says
   neither. It costs a reading, and everything below hangs on it.
2. **Prove the directions apart,** as the first proof file about cryptographic use. Small, and it
   uses what the prover already reads.
3. **Write "no counter twice" as `CounterWindow`'s invariant,** and the sealing side's "a nonce
   once". This is the first step that grows the prover (a history of calls).
4. **The opened-text type,** when the next reader of sealed text is made strong
   (`meetup_read_register`).
5. **A model of the meetup's exchange with an attacker** (kind 4), which is the map's "modelled".
   A new tool, and a model wants a cryptographer's review of its definitions before anything is
   concluded from it, as the Signal project asks. The owner's decision.

Not proposed: proving mosh's AES-OCB, or changing gosh to a proved cipher. The first is mosh's
core; the second moves gosh's shape. I know of no proved implementation of OCB *(not searched)*.

## What this project has that the others do not, and the reverse

**Has.** The source is the C++ that ships, in a subset small enough to refuse loudly. Whoever
writes the proof is trusted for nothing, which is what lets an agent write it. The subject is
reshaped until the proof is easy, so the proof improves the design. What a person reads is C++.

**Lacks.**

- **A reading of C++ that anyone else has checked.** Ours is three days old. Approaches 1, 3 and
  6 rest on readers used for years.
- **A model of memory that is not ours.** `Prooc.lean` was written by hand, once.
- **Anything to say about the weak code** but that it is listed. Approaches 3, 4 and 10 reach it.
- **Properties over time or between parties.** Approach 9.
- **A solver's speed.** The proofs by compiled code that were refused cost 40 lines in place of 2.

## What I would do

One recommendation, and three smaller ones. None is started.

1. **Run a bounded model checker over the six strong classes, as a second reader** (approach 3).
   It would be an instrument of this project, not a dependency of gosh, and in this project's
   terms a test: of the generator's reading, which is the largest thing trusted. A time box of one
   day on `StunAnswer` would say whether ESBMC reads gosh's C++ at all and finishes. It adds a
   tool to this repository, so it is the owner's decision.
2. **Say a format as data** (from approach 5), at the next step of the meetup's door
   (`meetup_read_register`): a table in the strong class, one reader proved. No generator.
3. **Give the map a third word** (from approach 9): *modelled*, for what is shown of a model of
   the protocol and not of the code. And write "no counter is taken twice" as an invariant first.
4. **Name each domain's rung** (from approach 2): memory and ending; the invariant; a proof file.

**One thing to watch.** What a strong method expects is written as C++26's `pre(...)`, compiled
by g++ 16. A search on 2026-11-19 found reports of a dispute in the standards committee over
whether contracts ship in C++26 at all (The Register, 2026-11-13) *(searched; the outcome was not
found, and the sources disagree)*. If they are taken out, g++'s flag may stay, change spelling, or
go. The generator already writes each `pre` again as the first lines of the body before reading
it, so the proofs do not depend on the spelling; the strong headers do.

## What would show this project's choice wrong

- A bounded checker, unaided, shows of the six classes what took three days here, and finds
  something the proofs missed.
- A format description would have made `StunAnswer` and `MeetupHeader` unnecessary to write.
- The proofs find nothing a type and a fuzzer had not, as more domains are done.

## Sources

Searched 2026-11-19. Everything not listed is recalled.

- EverParse: [project documentation](https://project-everest.github.io/everparse),
  [3D](https://project-everest.github.io/everparse/3d.html),
  [PLDI 2022 paper page](https://www.microsoft.com/en-us/research/?p=845653),
  [Microsoft Research blog](https://www.microsoft.com/en-us/research/blog/everparse-hardening-critical-attack-surfaces-with-formally-proven-message-parsers/)
- ESBMC: [project site](https://esbmc.github.io/),
  [C++ support](https://esbmc.github.io/docs/c-cpp/esbmc-cpp-support/),
  [v7.6 paper](https://arxiv.org/pdf/2406.17862)
- AutoCorres: [project page](https://www.trustworthy.systems/projects/OLD/autocorres),
  [AutoCorres2 in the AFP](https://devel.isa-afp.org/browser_info/current/AFP/AutoCorres2/outline.pdf)
- Aeneas and Verus: [Aeneas at lean-lang.org](https://lean-lang.org/use-cases/aeneas),
  [A Rust-to-Lean verification pipeline with AI provers](https://arxiv.org/abs/2605.30106),
  [Verus](https://github.com/verus-lang/verus)
- Contracts in C++26: [The Register, 2026-11-13](https://theregister.com/devops/2026/11/13/c26-stumbles-at-finish-line-over-contracts-dispute/5309526),
  [P4043R0](https://isocpp.org/files/papers/P4043R0.html)
- seL4: [the 2009 paper](https://www.trustworthy.systems/publications/nicta_full_text/1842.pdf),
  [in CACM](https://cacm.acm.org/?p=30656),
  [binary verification, PLDI 2013](https://www.cl.cam.ac.uk/~mom22/pldi13.pdf),
  [proof engineering considered essential](https://trustworthy.systems/publications/nictaabstracts/Klein_14.abstract),
  [a decade of maintaining the proofs, ITP 2019](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.1),
  [on cost](https://microkerneldude.org/2016/06/16/verified-software-can-and-will-be-cheaper-than-buggy-stuff/)
- Cryptography: [HACL\*](https://github.com/hacl-star/hacl-star),
  [Signal Shot](https://leodemoura.github.io/static/paris2026/),
  [a Rust-to-Lean pipeline with AI provers](https://arxiv.org/abs/2605.30106),
  [Tamarin models of sealing, USENIX Security 2023](https://www.usenix.net/system/files/usenixsecurity23-cremers-protocols.pdf),
  [CryptoVerif](https://arxiv.org/pdf/2310.14658)
- Wuffs: [README](https://skia.googlesource.com/external/github.com/google/wuffs/+show/HEAD/README.md)
- VeriFast: [Verification of C++ Programs with VeriFast](https://arxiv.org/pdf/2212.13754);
  Frama-C: [documentation](https://frama-c.com/html/documentation.html)
