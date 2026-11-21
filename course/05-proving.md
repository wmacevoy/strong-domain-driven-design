# Lesson 5. The proof, and who checks it

```sh
course/prove.sh Bottle
```

```
PROVED Bottle: 10 statements; model and C++ agree on 2001 lines, the invariant among them
PROVED Bottle, as proofs/Bottle.proof.cpp says it: 6 PROVEs in 2 proofs, every round of every loop
```

This lesson says what happened in those two lines, in five steps. You write only the last one.

## 1. The model: each method as a function

The prover reads `Bottle.hpp` and writes each method as a function in [Lean](https://lean-lang.org),
a language for statements and their proofs. Here is `setMaxVolume`, as generated
(`build/course/Bottle/gen/BottleModel.lean`):

```lean
def setMaxVolume (me : Bottle) (value : BitVec 32) : Option (Bottle × Unit) := do
  let mut me := me
  let mut value := value
  me := { me with maxVolume := value }
  if (me.volume > me.maxVolume) then
    me := { me with volume := me.maxVolume }
  return (me, ())
```

Three things to read in it:

- **`BitVec 32`** is a 32-bit machine number: `+` wraps, as `uint32_t`'s does. Not the integers of
  maths, which never overflow.
- **`Option`**: a method gives `some` result, or `none` where the C++ would commit a memory error
  (a read outside an array) or do something undefined. "No memory error" becomes "never `none`".
- The object is a value, `me`, passed in and handed back changed. No pointers.

## 2. What is owed: the statements

From the model, and from nothing else, the prover writes what must be proved
(`gen/BottleOwed.lean`). For each method that changes the object, two statements: it commits no
memory error, and it keeps the invariant. Here is the second, for `setMaxVolume`:

```lean
setMaxVolume_inv : ∀ (me : Bottle) (value : BitVec 32) (me' : Bottle) (r : Unit),
  Bottle.Inv me → Bottle.setMaxVolume me value = some (me', r) → Bottle.Inv me'
```

Read it aloud: *for every bottle `me` and every value, if the invariant holds of `me`, and
`setMaxVolume` gives `me'`, then the invariant holds of `me'`.* That is lesson 2's "kept by every
method", for this method, for every input. A loop method gets "ends" as well: there is some number
of rounds (`fuel`) after which it has finished.

Your proof file (lesson 3) becomes statements the same way (`gen/BottleProofOwed.lean`), one for
each loop, saying what lesson 3 said a loop means.

## 3. The proof: what you write

`bottle/Bottle.claims.lean` proves each statement. This one is five lines:

```lean
theorem setMaxVolume_inv : ∀ (me : Bottle) (value : BitVec 32) (me' : Bottle) (r : Unit),
    Inv me → Bottle.setMaxVolume me value = some (me', r) → Inv me' := by
  intro me value me' r _ h
  simp [Bottle.setMaxVolume] at h
  split at h <;> simp at h <;> subst h <;> simp_all [Inv] <;> bv_omega
```

After `:= by` come **tactics**: steps that turn the goal into simpler goals until none is left.
Five are enough for the bottle:

| Tactic | Does |
|---|---|
| `intro x h` | "Let `x` be any value, and suppose `h`": moves a `∀` or an `→` into what you know |
| `simp [f] at h` | Opens the definition of `f` in `h` and simplifies: runs the method, symbolically |
| `split` | Takes each branch of an `if` as its own goal: the bottle that spills, and the one that does not |
| `subst h` | Replaces a name by what `h` says it equals |
| `bv_omega` | Decides comparisons and sums of machine numbers: `volume ≤ value` follows from `¬(volume > value)` |

`<;>` means "then, to every goal that is left". When a proof fails, Lean shows the goal it could not
close: what you knew, a line, and what you had to show. Reading that goal is most of the skill.
Read it as a question about your code: here is a state the prover thinks is possible; why is it
not?

## 4. Who checks it: nobody trusts you

A proof file is a program, and you might have made a mistake, or cheated. So the prover:

- checks the claims prove **exactly** the generated statements, not some easier ones of your own;
- **audits** them: no new axioms, no `sorry` (a proof left out), nothing the kernel was told to
  skip. The bottle's proof rests on 1,092 definitions and theorems and three standard axioms
  (`build/course/Bottle/build/Bottle.audit`);
- asks Lean's **kernel** to check everything again, from scratch (`leanchecker`);
- and **compares** the model with the C++: 2,001 lines of the same calls, run through both,
  must agree. That is a test, of the prover's reading of your class. Lesson 10 comes back to it.

## 5. See it fail

A proof you have never seen fail has not been seen to work. Put lesson 1's off-by-one back into
`setMaxVolume` (`volume > maxVolume + 1`) and run `course/prove.sh Bottle` again:

```
FAIL: Bottle: a proof does not hold (claims/BottleClaims.lean)
```

Lean shows the goal: a bottle holding exactly `maxVolume + 1`, which the invariant forbids. The
facts passed this bug; the proof found the one case that matters. Put the line back.

Then take out the carried `PROVE` of lesson 3. The class still proves, and the proof file does not:

```
FAIL: Bottle: a PROVE of proofs/Bottle.proof.cpp is not proved (claims/BottleProofClaims.lean)
```

> Both seen 2026-11-21.

## Exercises

1. Add a method `pour( uint32_t more )` that adds to the volume, spilling what does not fit. Watch
   out: `volume + more` can wrap. Write it, run the prover, and read the statement it owes. Prove
   it, starting from `setVolume_inv`.
2. Write a `PROOF` that pouring `more` and then `setVolume( getVolume() )` changes nothing, and prove it.
3. Delete `bv_omega` from one proof. What goal is left? Say it in English.
