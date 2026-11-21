# Lesson 6. What "sorted correctly" means

Before proving a sort correct, say what correct is. Most people say "the output is in order". That
is half of it.

## Two halves, each useless alone

- **Sorted:** every element is no greater than the next. A "sort" that sets every element to 0 is
  sorted. So is one that returns nothing.
- **A permutation of the input:** the same elements, each as many times. A "sort" that does
  nothing at all keeps every element.

A correct sort is **both**. Each half catches what the other lets through, so a test or a proof of
only one is a test or proof of a different, broken program.

For bytes, "the same elements, each as many times" can be said by counting: for each of the 256
values, the output holds it as many times as the input did. `MergeSort` says both halves of
itself, as numbers that must be 0:

```cpp
  uint64_t outOfOrder() const;   /* how many bytes held are greater than the next */
  uint64_t notAsGiven() const;   /* how many of the 256 values are held a different number of times than given */
```

Writing the specification as code in the class, next to what it specifies, is the same move as
writing the invariant as `invariant()` (lesson 2). It is checked by the compiler, readable by
anyone, and (lesson 8) the prover can read it too.

## Testing it three ways

`mergesort/mergesort-facts.cpp` tests merge sort three ways, each more than the last.

**1. Examples.** The empty input, one byte, two backwards, all equal, eight backwards (the most it
takes), extremes. The cases someone thought of.

**2. Every input up to three bytes.** 1 + 256 + 65,536 + 16,777,216 inputs, every one, each checked
against both halves of the specification. For those lengths this is not a sample: it is all of
them, and so a proof, by running. About fifteen seconds here. Four bytes would be four billion more;
eight bytes, 2^64.

**3. Seeded random inputs up to eight bytes.** 100,000 of them, from few values (so there are many
repeats, where sorts go wrong). A sample of the lengths that matter most.

```sh
c++ -std=c++17 -O2 -Ivendor/facts course/mergesort/mergesort-facts.cpp vendor/facts/facts.cpp -o build/mergesort-facts
build/mergesort-facts --facts_timeout=300
```

```
100011 (100.0%) truths and 0 (0.0%) fictions checked.
```

(`--facts_timeout`: facts gives up on a run after 10 seconds by default, and this one is longer.)

## The oracle problem

How does a test know the right answer? Here, two ways:

- the specification methods, which say *whether* an output is right without knowing *what* it
  should be;
- and, for a sort, another sort: `std::sort` of the same input. Comparing two programs is a strong
  test, but only as strong as the other program, and only on the inputs you try.

Neither covers inputs of eight bytes completely. That gap, between "every input up to three" and
"every input", is what the rest of the course closes.

## Exercises

1. Write a "sort" that passes the `outOfOrder() == 0` check and fails `notAsGiven() == 0`, and one
   the other way round. Run the facts on each.
2. A sort is **stable** if equal elements keep their order. Why can no test of `MergeSort` see
   whether it is stable? (What are its elements?)
3. Is "every input up to three bytes" really a proof for those lengths? What does it rest on that
   the proofs of lesson 5 do not? (Think about the compiler, and about what `std::sort` is.)
