# Lesson 8. Your claim, as code

Here is "my merge sort is correct", as a test that cannot be run (`mergesort/MergeSort.proof.cpp`):

```cpp
PROOF( merge_sort_sorts_and_loses_nothing )
{
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    MergeSort s;
    s.load( Bytes( bytes.data(), bytes.size() ) );
    s.sort();
    PROVE( s.invariant() );
    PROVE( s.outOfOrder() == 0 );
    PROVE( s.notAsGiven() == 0 );
  }
}
```

`every_bytes()` is every sequence of bytes there is, of every length: none, then the 256 of one
byte, then the 65,536 of two, and so on, with no end. Lesson 6's facts ran the first 16.8 million;
this says it of all of them. (Sequences of more than 8 bytes are refused by `load`, which leaves
the object empty, and an empty one is sorted and holds what it was given: nothing.)

It compiles, against the class, as the C++ it is:

```sh
c++ -std=c++17 -fsyntax-only -Iprover/model -Icourse/mergesort course/mergesort/MergeSort.proof.cpp
```

## What the prover makes of it

The prover reads that loop as one statement in Lean (`build/course/MergeSort/gen/MergeSortProofOwed.lean`):

```lean
merge_sort_sorts_and_loses_nothing_loop1 : ∀ (bytes : Prooc.Bytes),
  (∃ s1, MergeSort.new = some s1 ∧
  (∃ fuel s2 r3, MergeSort.load fuel s1 (bytes) = some (s2, r3) ∧
  (∃ fuel s4, MergeSort.sort fuel s2 = some (s4, ()) ∧
  (MergeSort.Inv s4 ∧
  ((∃ fuel6 r5, MergeSort.outOfOrder fuel6 s4 = some (s4, r5) ∧ (r5 = 0#64)) ∧
  ((∃ fuel8 r7, MergeSort.notAsGiven fuel8 s4 = some (s4, r7) ∧ (r7 = 0#64)) ∧ True))))))
```

Read it line by line, and it is the C++ again:

- for every sequence of bytes,
- a new `MergeSort` is made (and the constructor commits no memory error),
- `load` ends, with some number of rounds (`fuel`), and commits no memory error,
- `sort` ends and commits no memory error,
- the invariant holds,
- `outOfOrder` ends and gives 0, and `notAsGiven` ends and gives 0.

Notice what you get for free. **"Commits no memory error" and "ends" are part of the statement**,
for every method on the way. You did not write them; they come with every call.

## What else is owed

Besides the proof file, the class owes twelve statements of its own (`gen/MergeSortOwed.lean`),
as the bottle did, whatever any proof file says:

```
new_safe, new_inv                      the constructor: no memory error, and the invariant
load_ends                              load ends, with no memory error, keeping the invariant
sort_ends                              sort ends, with no memory error, keeping the invariant
outOfOrder_ends, notAsGiven_ends       each ends, with no memory error
size_safe, at_safe                     each commits no memory error (at, given its pre: i < count)
size_same, at_same,
outOfOrder_same, notAsGiven_same       the const methods change nothing
```

(Run `course/prove.sh MergeSort` and read `build/course/MergeSort/gen/MergeSortOwed.lean` for
the exact list.) `merge` owes nothing alone. It is private and not on the boundary, but every call
to it must satisfy its `pre`, and `sort_ends` cannot be proved without showing that.

> Found writing this lesson (2026-11-21): the prover gave a const method that loops no `fuel` when
> a `PROVE` named it, and Lean refused the statement above. The prover was fixed, with a test of
> its own (`prover/test_prooc.py`, "a const method that loops, in a PROVE"). A course is a good
> test of its tools.

## Exercises

1. Lesson 7 argued that `sort` keeps "a permutation of what was loaded". Which line of the
   statement above needs that?
2. Change the proof file to claim something false, say `PROVE( s.outOfOrder() == 1 )`. Does the
   prover refuse to read it, or read it and then fail to prove it? Why is the second the right
   behaviour?
3. Why does the statement say `MergeSort.outOfOrder fuel6 s4 = some (s4, r5)`, with `s4` on both
   sides?
