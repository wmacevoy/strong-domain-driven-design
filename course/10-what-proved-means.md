# Lesson 10. What "proved" means here

When `course/prove.sh` prints `PROVED`, it is a precise claim, and it rests on things. Say both,
every time you say "proved" (`docs/STRONG_DOMAINS.md`, guideline 32).

## The claim

*This text* (`Bottle.hpp`, by its hash in `build/course/Bottle/build/Bottle.bundle`), read as *this
model*, meets *these statements* (the generated `Owed` files): no method commits a memory error,
every loop ends, the invariant always holds, and every `PROVE` of the proof file holds in every
round of every loop.

## What it rests on: the K4s

Every proof rests on things it does not prove. Software engineering has a name for an assumption
made on purpose, knowing it is not always true: a **K4**, a falsehood chosen knowingly. "The clock
is right" is one. Nothing gets built without them. The rule is to name each one, say where it is
load-bearing, and say what breaks when it fails. A proof's K4s are of two kinds.

**The environment:** everything the proof rests on but does not prove.

- the hardware and its firmware (and its faults: a memory bit that flips);
- the kernel and its drivers;
- the loader and the runtime, which run before `main`;
- every library the program links against;
- the program's own unproved code, other threads among it: it shares the process;
- the tools that built it: compiler, assembler, linker;
- **anyone with the rights to change or view the program or its memory, before or while it runs**:
  whoever can rewrite the binary, set its environment, attach a debugger, or is root.

Input is not on that list. Bytes that come in through the program's interfaces, from anyone, are
exactly what the proofs cover. What is assumed is that nothing reaches the state *around* the
interfaces.

**The method's own:**

| Assumed | Why it is reasonable | What would show it wrong |
|---|---|---|
| **The prover reads the C++ rightly.** | Each method's model is compared with the compiled C++ on 2,001 seeded calls; the prover has its own suite of over 150 cases, each seen failing | A call on which model and C++ disagree: then `prove.sh` fails, saying so |
| **`proofs.py` reads the proof file rightly.** | It reads a small subset and refuses the rest; and the proof file is also **run at small bounds** before anything is proved (each loop over numbers at its first and last 8 values, over bytes a fixed sample), so a claim that is false when run fails at once (`RAN Bottle ... 8976 PROVEs held`) | A run and a proof that disagree. A run that passes shows only the values it ran. |
| **The hand-read primitives** (`Bytes.hpp`, and in gosh `subarray.h`) | A few lines each, read by a person; each keeps a pointer | A pointer and a length that do not match |
| **Lean's kernel and its three standard axioms.** | A small kernel, checked again by `leanchecker` | A bug in Lean's kernel |

Not assumed: anything you wrote in Lean. The audit and the kernel check your proofs as if a
stranger wrote them.

## Change or view: where proof meets security

"Who may **change** or **view** this?" is the oldest question in computer security, and it is the
same line as the proof's.

- **Change** is *integrity*. A proof is about the state as the class's own methods leave it. If
  anything outside can change that state (a stray write from unproved code, a debugger, root), every
  statement about it is void. So who may change the process is the boundary of the proof.
- **View** is *confidentiality*, and a proof says nothing about it. If `Bottle` held a password, the
  proof would show it is never read outside its array, and anyone who can read the process's memory
  could still see it.

So the two jobs are one: making fewer people and processes able to change or view the program
(its own user, no tracing, a secret in a process apart) is security work, and it is also shrinking
the proof's K4s.

## So, are tests finished?

No. Look at what is still only tested:

- the prover's own reading of your code (the comparison of model and C++: a test);
- `proofs.py`'s reading of your proof file (run at small bounds, which is a test);
- everything around the proved class: the code that calls it, reads files, talks to the network.
  gosh proves its parsers of what strangers send, and tests the rest with facts and fuzzers;
- and the specification itself. A proof shows the code meets `outOfOrder() == 0` and
  `notAsGiven() == 0`. Whether those two methods say what *you* mean by "sorted correctly" is for
  you to read, and to test (lesson 6, exercise 1).

The facts of lessons 1 and 6 are still worth running. They are cheap, they run on the real
compiled code, and they caught the reversed comparison in `merge` in a fraction of a second. A
proof covers every case of what it states; a test checks what really runs. Keep both, and say which
is which.

## Where to go next

- `docs/STRONG_DOMAINS.md`: the approach this course comes from, and 41 guidelines.
- `prover/README.md`: exactly what the prover reads, refuses, and states.
- gosh (`../gosh/src/strong`): a real program whose parsers of untrusted bytes are proved this way,
  each proof beside its class.

## Exercises

1. Write the paragraph you would put in a code review that says what is proved of `Bottle`, what
   it rests on, and what is only tested. No more than six sentences.
2. Find a bug a proof of `MergeSort` would *not* catch. (Hint: what if `notAsGiven()` itself were
   wrong?)
3. Which of the assumptions above would you most like to see removed, and how would you remove it?
4. For a program you use, list who can change or view its memory while it runs. Which of them would
   void a proof of it, and which only learn its secrets?
