# Lesson 7. Reasoning about loops

Merge sort is loops. To prove a loop, you need two things for it, and you should be able to say
both in English before you write any Lean:

- a **loop invariant**: what is true before every round, kept by every round, and, with the loop's
  condition false, enough to give what you want after it;
- a **measure**: a number that every round makes smaller and that cannot go below zero, so the
  loop ends.

Here is `MergeSort`'s `merge` and `sort` (`mergesort/MergeSort.hpp`), argued by hand.

## `merge( lo, mid, hi )`

It expects `lo ≤ mid ≤ hi ≤ N`, and that `data[lo, mid)` and `data[mid, hi)` are each sorted. It
takes the smaller front element of the two runs into `scratch`, one at a time, then copies
`scratch[lo, hi)` back.

```cpp
    uint64_t i = lo, j = mid, k = lo;          // (three declarations in the file)
    while ( k < hi ) {
      if ( i < mid && ( j >= hi || data[i] <= data[j] ) ) {
        scratch[k] = data[i];  i = i + 1;
      } else {
        scratch[k] = data[j];  j = j + 1;
      }
      k = k + 1;
    }
```

**Invariant**, before every round:

1. `lo ≤ i ≤ mid`, `mid ≤ j ≤ hi`, and `k = lo + (i − lo) + (j − mid)`: what was taken is what was
   written.
2. `scratch[lo, k)` is sorted.
3. `scratch[lo, k)` holds exactly `data[lo, i)` and `data[mid, j)`: a permutation of what was taken.
4. Every element of `scratch[lo, k)` is ≤ `data[i]` (if `i < mid`) and ≤ `data[j]` (if `j < hi`):
   nothing still to take is smaller than what is already taken.

**It holds at the start:** `i = lo`, `j = mid`, `k = lo`, and `scratch[lo, lo)` is empty, so 2, 3
and 4 say nothing.

**Every round keeps it.** Take the first branch (the second is the same with the runs swapped).
`data[i]` is ≤ every element still to take: ≤ `data[i+1], …` because its run is sorted, and ≤
`data[j]` by the condition (or the other run is empty). By 4, it is ≥ everything in
`scratch[lo, k)`. So appending it keeps 2; it keeps 3 by construction; and 4 holds of the new
fronts because the runs are sorted.

**No read is outside an array.** This is the part the prover asks first, and the part people get
wrong. In the first branch, `i < mid ≤ N`. In the second, is `j < hi`? Either `j < hi` was tested
and true, or `i ≥ mid`. In that case, by 1, `i = mid`, so `k = lo + (mid − lo) + (j − mid) = j`, and
`k < hi` is the loop's condition. So `j < hi` either way. **That fact is why invariant 1 is there:**
without the equation for `k`, the second branch cannot be shown safe.

**It ends:** the measure `hi − k` falls by one every round, and the loop stops at 0.

**After it,** `k = hi`, so by 1 `i = mid` and `j = hi`; by 2 and 3, `scratch[lo, hi)` is sorted and
holds exactly `data[lo, hi)`. The copy-back loop then makes `data[lo, hi)` so (its invariant:
`data[lo, k) = scratch[lo, k)`).

## `sort()`

```cpp
    for ( uint64_t width = 1; width < count; width = width * 2 ) {
      for ( uint64_t lo = 0; lo < count; lo = lo + 2 * width ) {
        uint64_t mid = lo + width;      if ( mid > count ) { mid = count; }
        uint64_t hi  = lo + 2 * width;  if ( hi > count )  { hi = count; }
        merge( lo, mid, hi );
      }
    }
```

**Outer invariant:** `data[0, count)` is a permutation of what was loaded, and every run
`data[m·width, (m+1)·width)` (cut off at `count`) is sorted. At the start, `width = 1`, and a run of
one element is sorted.

**Inner invariant:** `lo` is a multiple of `2·width`; the runs of `2·width` before `lo` are sorted;
the runs of `width` from `lo` on are sorted; and it is still a permutation. One round merges the
two runs at `lo` into one of `2·width`.

**`merge`'s precondition holds at the call:** `lo < count`, `mid` and `hi` are cut off at
`count ≤ N`, and `lo ≤ mid ≤ hi` because `width ≥ 1`. The prover will make you show exactly this,
because `merge` says `pre( lo <= mid && mid <= hi && hi <= N )`.

**They end:** in the inner loop, `count − lo` falls by `2·width ≥ 2`; in the outer one, `width`
doubles, so it passes `count` after at most log₂ `count` + 1 rounds.

**After the outer loop,** `width ≥ count`, so the first run, `data[0, width)` cut off at `count`,
is all of it: sorted, and a permutation.

## The bug in nearly every merge sort

In 2006 Joshua Bloch wrote "Nearly All Binary Searches and Mergesorts are Broken". The bug was
`mid = (lo + hi) / 2`: with arrays of more than about a billion elements, `lo + hi` overflows a
32-bit int, and `mid` goes negative. It had been in the Java library for nine years, and in the
textbook it came from for longer. Tests never found it, because nobody tested arrays that big.

Look at `sort` again: `lo + 2 * width` and `lo + width`. With `N = 8` and 64-bit numbers they
cannot wrap. But the prover does not take that on trust. Its numbers are `BitVec 64`, which wrap,
so your proof must **show** they do not: `lo < count ≤ 8` and `width < count`, so the sums are at
most 24. Change `N` to 2^63, and that step of the proof fails. That is the bug, found before anyone
has an array that big.

## Exercises

1. In `merge`, the condition is `i < mid && ( j >= hi || data[i] <= data[j] )`. Why must
   `j >= hi` be tested before `data[j]` is read? What does C++'s `||` guarantee?
2. Write the copy-back loop's invariant and measure.
3. Why does `sort`'s outer loop end even when `count` is 0 or 1? (Look at the condition.)
4. Find the step of the argument above that uses `width ≥ 1`. What goes wrong if `width` starts
   at 0?
