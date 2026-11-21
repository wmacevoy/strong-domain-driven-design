# Lesson 9. Proving merge sort (the capstone)

**Where this stands (2026-11-21):** the statements of lesson 8 are generated, and Lean accepts
them as statements. Nobody has proved them yet. `course/prove.sh MergeSort` stops at the first
missing proof, `claims/MergeSortClaims.lean`. This lesson is the plan. The proof is yours.

Do it in two parts, in this order. The first is a few hundred lines of Lean, most of them like the
bottle's. The second is the real work: lesson 7's arguments, written so a machine can check them.

## How a loop is modelled

A loop becomes two functions (`build/course/MergeSort/gen/MergeSortModel.lean`): one **round**,
and the **loop**, which runs rounds while it has some left:

```lean
def merge.loop1 (fuel : Nat) (left : Nat) (me : MergeSort) (lo mid hi i j k : BitVec 64) : Option (Prooc.Step …) :=
  match left with
  | 0 => none                                   -- out of rounds: no result
  | left + 1 => do
    match (← merge.round1 fuel me lo mid hi i j k) with
    | .next (me, i, j, k) => merge.loop1 fuel left me lo mid hi i j k   -- go round again
    | .done s => pure (.done s)                                         -- the condition is false
    | .ret r => pure (.ret r)                                           -- a `return` inside
```

`left` counts the rounds still allowed. Run out, and the answer is `none`. So "the loop ends" is
"for enough rounds the answer is not `none`", and "enough" is the measure of lesson 7.

## The pattern: one lemma per loop

Every loop proof here has the same shape. It is the one that proves gosh's `CounterWindow`
(`../gosh/src/strong/meetup/CounterWindow.claims.lean`, `loop1_done`):

```lean
theorem merge_loop1_done (left : Nat) (me : MergeSort) (lo mid hi i j k : BitVec 64)
    (hinv : LoopInv me lo mid hi i j k)          -- lesson 7's invariant, as a Lean definition
    (hl : (hi - k).toNat < left) :               -- the measure fits in the rounds allowed
    Prooc.DoneWith (merge.loop1 fuel left me lo mid hi i j k)
      (fun s => After s lo mid hi) := by         -- what holds when it is done
  induction left generalizing me i j k with
  | zero => omega                                -- no rounds left contradicts hl
  | succ left ih =>
    unfold merge.loop1
    by_cases h : k < hi
    · -- one round: show it keeps LoopInv, and the measure falls by one; then use ih
      …
    · -- the condition is false: LoopInv and ¬(k < hi) give After
      …
```

Induction on `left` is induction on rounds: lesson 3's "from any state the rounds before could
leave", made formal.

## Part 1: no memory error, and it ends

These are the twelve statements of `MergeSortOwed.lean`. They need only the **first** line of
lesson 7's `merge` invariant, the one about the indices:

```lean
def Idx (lo mid hi i j k : BitVec 64) : Prop :=
  lo ≤ i ∧ i ≤ mid ∧ mid ≤ j ∧ j ≤ hi ∧ k = lo + (i - lo) + (j - mid) ∧ hi ≤ 8
```

Steps, each a lemma:

1. `merge_loop1_done` with `Idx`: every read `data[i]`, `data[j]` and every write `scratch[k]` is
   below 8 (lesson 7, "no read is outside an array"); `hi − k` falls.
2. `merge_loop2_done`: the copy back, `k` from `lo` to `hi`.
3. `merge_ok`: given `pre( lo <= mid && mid <= hi && hi <= N )`, `merge` gives `some`.
4. `sort_loop2_done` (the inner loop): `merge`'s `pre` holds at each call (lesson 7), and `count − lo` falls.
   **Here is the overflow step:** show `lo + 2 * width` does not wrap, from `lo < count ≤ 8` and `width < count`.
5. `sort_loop1_done` (the outer loop): `width` doubles, so 4 rounds are enough for `count ≤ 8`.
6. `load_ends`, `outOfOrder_ends`, `notAsGiven_ends`: simple loops, as in step 2.
7. The const methods, the constructor and the invariant: as the bottle's.

When Part 1 is done, `course/prove.sh MergeSort` prints its first `PROVED` line: merge sort ends
and commits no memory error, for every input. That is worth having by itself.

## Part 2: sorted, and nothing lost

This is `MergeSortProof.Owed`, the proof file's statement. It needs all four lines of lesson 7's
invariants, written as Lean definitions over the arrays:

```lean
def SortedRange (a : Fin 8 → BitVec 8) (lo hi : Nat) : Prop :=
  ∀ x y, lo ≤ x → x < y → y < hi → a x ≤ a y           -- (indices as numbers below 8)
def CountIn (a : Fin 8 → BitVec 8) (lo hi : Nat) (v : BitVec 8) : Nat := …   -- how many times v is in a[lo, hi)
```

(How the model holds an array, and how `Prooc.get` reads it, is in `prover/Prooc.lean`. Write
these definitions in its terms.)

Then, in order:

1. **`merge` is correct:** if `data[lo, mid)` and `data[mid, hi)` are sorted, afterwards
   `data[lo, hi)` is sorted, holds the same count of every value, and nothing outside `[lo, hi)`
   changed. The loop lemma carries all four lines of the invariant.
2. **The inner loop of `sort`:** runs of `2·width` before `lo` sorted, of `width` after; counts
   unchanged.
3. **The outer loop:** runs of `width` sorted; counts unchanged. At the end, `width ≥ count`.
4. **`outOfOrder` gives 0 of a sorted range, and `notAsGiven` gives 0 when every count matches.**
   Two more loop lemmas, about the specification methods themselves.
5. **`load`:** `data` and `original` hold the same bytes, so every count matches from the start.

## Advice

- **Write the invariant as a Lean `def` first, and test it.** Before proving a loop keeps it, check
  it is true by running: the C++ build of the comparison (`build/course/MergeSort/gen/MergeSort_diff.cpp`)
  can be given an `assert` of the same condition, or write it as a fact.
- **One lemma per loop, and one per round.** gosh's proofs found that Lean simplifies five small
  functions in seconds where one large one ran out of time.
- **When a goal will not close, read it as a state.** Lean shows you a state of your program that
  it thinks is possible. Either it is not, and you have not yet said why (a missing line of the
  invariant), or it is, and you have found a bug.
- **If the proof is hard, change the code first** (`docs/STRONG_DOMAINS.md`, guideline 18): ask
  what would make the statement obvious to a programmer.

## Exercises

1. Do Part 1, step 1. Keep a list of every goal you could not close at first, and what was missing.
2. Before Part 2, state `merge`'s correctness lemma in Lean with `sorry` as its proof, and use it
   to prove the inner loop of `sort`. Then go back and replace the `sorry`. (The audit refuses a
   `sorry`, so this is for working, never for handing in.)
3. Count the lines of your finished proof. Compare with the 150 lines of C++. Where did they go?
