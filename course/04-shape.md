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

## Why this shape: one class at a time

A proof is only worth having if it stays true when the rest of the program changes. The rules
above are what make that so. Each closes one way other code could reach the class, until what you
know about the class depends on the class alone.

**The problem they solve.** How would you know the bottle's `volume <= maxVolume` is always true,
in ordinary C++? You would need every line that could write those two numbers. With a public
field, that is any line that can name a bottle. With a pointer to a field handed out, it is any
line that ends up holding it, wherever that is. With undefined behaviour anywhere in the program,
it is every line. The honest answer is "read the whole program", and any change anywhere, later,
can break it without a word.

**What each rule lets you stop thinking about:**

| Rule | What you no longer have to think about |
|---|---|
| All state private, and an `invariant()` | Who else changes the fields: nobody. So "true when made, kept by every method" (lesson 2) is true forever. You check a constructor and a few methods, not the program. |
| No pointer or reference kept, given out, or taken | Aliasing: another name for the same memory, changing it behind your back. The commonest reason local reasoning fails in C and C++. A field changes only where the class's code says so. |
| Outside bytes as a read-only view, held for the call only | Whether the input changes while you read it, or outlives the call. |
| What a method expects said at its boundary: `pre(...)`, or a type | Who called it. Its proof assumes only what it expects; each proved caller must show it. |
| Unsigned numbers, nothing undefined | What the compiler may do with a line elsewhere. Each line has one meaning, and its effect is local. |
| No globals, statics or threads | Hidden shared state. A method's result depends on its object and its arguments, nothing else. |
| The clock, sockets and files kept outside | The state of the world. The same inputs always give the same result. |
| Each class proved on its own | Other classes' code. A class that takes another as a parameter relies on that class's invariant, a statement, and not on how its values were made. |

**What it buys.**

- *Short proofs that stay put.* The bottle's proof of `setMaxVolume` is five lines and names no
  other file. It does not care whether the program around it is a hundred lines or a hundred
  thousand, or what is added next year.
- *A bug elsewhere cannot break what is proved.* gosh proves `CounterWindow`, which remembers which
  message counters it has seen, and leaves `Registrations`, the code that calls it, unproved.
  Whatever bug `Registrations` has, it cannot make `CounterWindow` write outside its sixteen words,
  nor even hand it a number that is not a counter: it may not make a `Counter` itself (gosh's check
  refuses the program if it does), and what it hands over is tested on the way in. The proof of
  `CounterWindow` never read `Registrations` (`../gosh/src/strong/meetup/`).
- *Changes stay local.* Change `merge`, and you prove `merge` again, and what rests on what `merge`
  says. Change the code around a class, and its proofs do not move. The work grows with what
  changed, not with the program.
- *Reviews read boundaries.* An invariant, the preconditions, a proof file, and the list of places
  unproved code comes in, instead of the whole program.

**The price.** Locality rests on a few things assumed of everything else: that the rest of the
program commits no memory error (a stray write through a dangling pointer can still corrupt a
proved object's bytes, and C++ has no wall against it when the program runs), and that the
compiler and the machine are right. They are named, not hidden, and lesson 10 lists them. That is
the trade: a few named assumptions about everything else, for reasoning about each piece by itself.

## Exercises

1. For each rule in the table, write a three-line class that breaks it, and run the prover on it.
   (Copy `bottle/` to a folder of your own first.)
2. Why must the specification methods `outOfOrder()` and `notAsGiven()` take no arguments, and
   return a number rather than a `bool`? (Hint: lesson 8; the prover's README, "Not yet".)
3. `merge`'s precondition is on its arguments. Why could it not be part of the class's invariant?
4. Make `getVolume()` return a `uint32_t&` instead of a copy, and write three lines of code outside
   the class that break the invariant. Which rule did that break, and what would you now have to
   read to know the invariant holds?
