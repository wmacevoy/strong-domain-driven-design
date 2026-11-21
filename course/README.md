# From facts to proofs: proving your merge sort is correct

A course for a junior CS student who can write a C++ class, has written tests, and has heard the
word "invariant". It starts from a bottle, tested the ordinary way, and ends at the statement
"for every input, my merge sort's output is sorted and is the input in another order", checked by
a machine.

The tools are assumed to be set up: Lean (`tools/lean.sh`) and a Python with libclang (`pixi
install`), from the root of this repository. Every command below is run from there.

## What you need to know, in the order you will need it

1. **What a test shows, and what it does not.** A test is a fact about one case. Passing tests say
   the cases you thought of work. *(lesson 1)*
2. **Invariants.** What is true of an object after every call, whatever the calls were. Checking
   one after every call in a test is still checking only the calls you made. *(lesson 2)*
3. **"For every".** A test that loops over every value there is, which nobody can run, but which
   says exactly what you mean. And how a loop over every value is reasoned about: from any state
   the rounds before could leave. That is induction, written as a loop. *(lesson 3)*
4. **Code shaped to be reasoned about.** Private state, unsigned numbers, no pointers kept, arrays
   of a fixed size, small methods. Why each makes reasoning possible, and what the prover refuses.
   *(lesson 4)*
5. **What a proof of code is.** A model of each method, "commits no memory error" and "ends" as
   statements, the invariant kept as a statement, and a proof of each that a checker accepts
   without trusting whoever wrote it. Reading a Lean goal, and five tactics. *(lesson 5)*
6. **What "sorted correctly" means.** Two things, sorted *and* a permutation of the input; why
   each alone is not enough; and testing a sort against another one. *(lesson 6)*
7. **Loop invariants and termination.** The invariant of `merge`'s loop and of `sort`'s two loops,
   argued by hand; a measure that shrinks, so each loop ends; and the overflow that broke the
   merge sorts of the world in 2006. *(lesson 7)*
8. **Your claim, as code.** Merge sort's proof file: one loop over every sequence of bytes, and
   two lines saying "sorted" and "nothing lost". What the prover makes of it. *(lesson 8)*
9. **Proving it.** The plan for the Lean proof: a lemma for each loop, from the invariants of
   lesson 7. *(lesson 9: the capstone)*
10. **What "proved" means here.** What the proof rests on, and what is still only tested.
    *(lesson 10)*

## The lessons

| | Lesson | Code |
|---|---|---|
| 1 | [Facts: the bottle, tested](01-facts.md) | `bottle/bottle-facts.cpp` |
| 2 | [What is always true](02-invariants.md) | `bottle/Bottle.hpp`, `bottle/bottle-facts.cpp` |
| 3 | [A test that cannot be run](03-for-every.md) | `bottle/Bottle.proof.cpp` |
| 4 | [Code shaped to be reasoned about](04-shape.md) | `bottle/Bottle.hpp`, `mergesort/MergeSort.hpp` |
| 5 | [The proof, and who checks it](05-proving.md) | `bottle/Bottle.claims.lean`, `bottle/Bottle.proof-claims.lean` |
| 6 | [What "sorted correctly" means](06-sorted.md) | `mergesort/mergesort-facts.cpp` |
| 7 | [Reasoning about loops](07-loops.md) | `mergesort/MergeSort.hpp` |
| 8 | [Your claim, as code](08-claim.md) | `mergesort/MergeSort.proof.cpp` |
| 9 | [Proving merge sort](09-proving-merge-sort.md) | the capstone |
| 10 | [What "proved" means here](10-what-proved-means.md) | |

## Where things stand (2026-11-21)

- **The bottle is proved**, all of it: `course/prove.sh Bottle` prints `PROVED`. Broken (a spill
  taken out, or off by one), it fails.
- **Merge sort is tested**, and its claim is written: the facts pass, including every input up to
  three bytes; the prover reads the class and the proof file, and Lean accepts the statements.
  **They are not yet proved.** Proving them is the capstone, lesson 9, and nobody has done it yet.
  That is a fair place for a course to stand: the last step is yours.

## How to run what is here

```sh
# the facts (lessons 1, 2 and 6): the facts library is vendor/facts
c++ -std=c++17 -Ivendor/facts course/bottle/bottle-facts.cpp vendor/facts/facts.cpp -o build/bottle-facts && build/bottle-facts
c++ -std=c++17 -O2 -Ivendor/facts course/mergesort/mergesort-facts.cpp vendor/facts/facts.cpp -o build/mergesort-facts && build/mergesort-facts --facts_timeout=300

# a proof file compiles as the C++ it is (lessons 3 and 8)
c++ -std=c++17 -fsyntax-only -Iprover/model -Icourse/bottle course/bottle/Bottle.proof.cpp

# the proofs (lessons 5 and 9)
course/prove.sh Bottle
course/prove.sh MergeSort      # fails today, at the first proof not yet written
```
