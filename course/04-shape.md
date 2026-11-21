# Lesson 4. Code shaped to be reasoned about

The prover (`prover/`) reads a class and writes a precise model of it, then states what must be
proved. It reads only code it can give an exact meaning to, and **refuses** the rest, saying why.
Each rule below is one you would want anyway when reasoning by hand.

| Rule | Why it makes reasoning possible |
|---|---|
| **All state is `private`.** No friends, no bases, no `virtual`. | Only the class's own methods change its fields, so "kept by every method" (lesson 2) covers every way it can change. One public field, and anyone can break the invariant. |
| **Unsigned whole numbers** (8 to 64 bits), and arrays of them of a fixed size. | Every operation has one meaning. Unsigned arithmetic wraps, which is defined; signed overflow is undefined behaviour in C++, and a float can be "not a number", false in every comparison. |
| **No pointer or reference kept, given out, or taken.** Bytes from outside come as a read-only view (`Bytes`), held only for the call. | Nothing outside can reach in and change the state behind the class's back, and "inside the array" becomes a comparison of numbers. |
| **No recursion yet; a method calls only methods written before it.** | Each method's model is built from models already built. (Merge sort, therefore, is bottom-up: lesson 7.) |
| **No local arrays yet.** | Merge sort's scratch space is a field instead. |
| **Small methods, one decision each.** | A proof walks every path, and so does a reader. |
| **`bool invariant() const` says what is always true.** | Lesson 2. If you cannot write it, there is nothing to prove yet. |

Some of these are limits of today's prover, not of reasoning: recursion and local arrays are
marked *yet*. The rest are the shape that makes a class easy to reason about by anyone.

## What a refusal looks like

Make `volume` public and ask the prover to read the bottle:

```sh
READ_ONLY=1 course/prove.sh Bottle
```

It refuses, at the line, with the reason ("not private"). That is the first loop of feedback: the
cheapest check that could have caught the problem, before any proof is tried.

## The merge sort, in this shape

`mergesort/MergeSort.hpp` sorts up to 8 bytes. Look at how it keeps the rules:

- the bytes, a copy of what was given, and the scratch space are fixed arrays of 8, all private;
- the input comes as a `Bytes` view in `load`, copied in, and the view is not kept;
- `sort` is two loops, runs of width 1, 2, 4, ... merged pairwise: no recursion;
- `merge( lo, mid, hi )` says what it expects of its caller, `pre( lo <= mid && mid <= hi && hi <= N )`
  (C++26's contracts), and the prover makes every caller prove it;
- and, the part that matters for lesson 8, it can say of itself whether it is correct, with two
  methods that take nothing: `outOfOrder()` counts the bytes greater than the next, and
  `notAsGiven()` counts the values held a different number of times than given. Correct is
  both 0.

When the prover reads it:

```sh
READ_ONLY=1 course/prove.sh MergeSort
```

it says `READ MergeSort`: in the subset, every line given a meaning.

## Exercises

1. For each rule in the table, write a three-line class that breaks it, and run the prover on it.
   (Copy `bottle/` to a folder of your own first.)
2. Why must the specification methods `outOfOrder()` and `notAsGiven()` take no arguments, and
   return a number rather than a `bool`? (Hint: lesson 8; the prover's README, "Not yet".)
3. `merge`'s precondition is on its arguments. Why could it not be part of the class's invariant?
