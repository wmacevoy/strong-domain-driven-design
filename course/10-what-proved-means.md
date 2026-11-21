# Lesson 10. What "proved" means here

When `course/prove.sh` prints `PROVED`, it is a precise claim, and it rests on things. Say both,
every time you say "proved" (`docs/STRONG_DOMAINS.md`, guideline 32).

## The claim

*This text* (`Bottle.hpp`, by its hash in `build/course/Bottle/build/Bottle.bundle`), read as *this
model*, meets *these statements* (the generated `Owed` files): no method commits a memory error,
every loop ends, the invariant always holds, and every `PROVE` of the proof file holds in every
round of every loop.

## What it rests on

| Assumed | Why it is reasonable | What would show it wrong |
|---|---|---|
| **The prover reads the C++ rightly.** | Each method's model is compared with the compiled C++ on 2,001 seeded calls; the prover has its own suite of over 150 cases, each seen failing | A call on which model and C++ disagree: then `prove.sh` fails, saying so |
| **`proofs.py` reads the proof file rightly.** | It reads a small subset, refuses the rest, and has its own cases | Nothing can compare its reading with a run, since nothing can run it. This is trusted most, and checked least. |
| **The compiler and the machine are correct.** | The proof is of the C++'s meaning, not of the machine code | A miscompilation |
| **The code is called as the class allows.** | Its state is private; `pre` conditions are proved at every call *from proved code* | A caller outside, breaking a `pre` (gosh calls such places `_checked`, and tests them when the program runs) |
| **Lean's kernel and its three standard axioms.** | A small kernel, checked again by `leanchecker` | A bug in Lean's kernel |

Not assumed: anything you wrote in Lean. The audit and the kernel check your proofs as if a
stranger wrote them.

## So, are tests finished?

No. Look at what is still only tested:

- the prover's own reading of your code (the comparison of model and C++: a test);
- `proofs.py`'s reading of your proof file;
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
