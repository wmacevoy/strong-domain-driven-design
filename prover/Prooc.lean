/-! The primitives: the only ways a generated model touches memory, and how a loop says what
happened. Written by hand, once. A read or a write outside an array or a view is `none`: a memory
error, which a class's safety theorems say never happens. -/
namespace Prooc

def get (v : Vector α n) (i : Nat) : Option α := v[i]?

def set (v : Vector α n) (i : Nat) (x : α) : Option (Vector α n) :=
  if h : i < n then some (v.set i x h) else none

/-- Inside the array, a read is the element. -/
theorem get_of_lt (v : Vector α n) (h : i < n) : get v i = some v[i] := by
  simp [get, h]

/-- Inside the array, a write is the array with that element changed. -/
theorem set_of_lt (v : Vector α n) (x : α) (h : i < n) : set v i x = some (v.set i x h) := by
  simp [set, h]

/-- A shift by an amount known only when it runs. In C++ a shift by the width or more is undefined,
so here it is `none`, as a read outside an array is. -/
def shl (x : BitVec w) (n : Nat) : Option (BitVec w) := if n < w then some (x <<< n) else none

def shr (x : BitVec w) (n : Nat) : Option (BitVec w) := if n < w then some (x >>> n) else none

/-- Below the width, a shift is the shift. -/
theorem shl_of_lt (x : BitVec w) (h : n < w) : shl x n = some (x <<< n) := by simp [shl, h]

theorem shr_of_lt (x : BitVec w) (h : n < w) : shr x n = some (x >>> n) := by simp [shr, h]

/-- A division by a number known only when it runs. In C++ a division by zero is undefined, so
here it is `none`. -/
def div (x y : BitVec w) : Option (BitVec w) := if y = 0 then none else some (x / y)

def mod (x y : BitVec w) : Option (BitVec w) := if y = 0 then none else some (x % y)

/-- `+` and `-` of two signed numbers. In C++ an overflow is undefined, so here it is `none`, as a
read outside an array is. -/
def sadd (x y : BitVec w) : Option (BitVec w) := if x.saddOverflow y then none else some (x + y)

def ssub (x y : BitVec w) : Option (BitVec w) := if x.ssubOverflow y then none else some (x - y)

/-- Where it does not overflow, it is the sum, or the difference. -/
theorem sadd_of_not (h : x.saddOverflow y = false) : sadd x y = some (x + y) := by simp [sadd, h]

theorem ssub_of_not (h : x.ssubOverflow y = false) : ssub x y = some (x - y) := by simp [ssub, h]

/-- The byte view (model/Bytes.hpp): bytes that are someone else's, read only. No object in C++ is
2^63 bytes or more, so its size fits the 64 bits `size()` gives. -/
structure Bytes where
  bytes : Array (BitVec 8)
  small : bytes.size < 2 ^ 63

namespace Bytes

def size (b : Bytes) : BitVec 64 := BitVec.ofNat 64 b.bytes.size

def read (b : Bytes) (i : Nat) : Option (BitVec 8) := b.bytes[i]?

/-- `size()` is the number of bytes: nothing is lost in 64 bits. -/
theorem size_toNat (b : Bytes) : b.size.toNat = b.bytes.size := by
  have := b.small
  simp [size]
  omega

/-- For claims: byte `i` of the view, and 0 outside it. (`read` is what the model uses: it fails outside.) -/
def byte (b : Bytes) (i : Nat) : BitVec 8 := b.bytes.getD i 0

/-- Inside the view, a read is the byte. -/
theorem read_of_lt (b : Bytes) (h : i < b.bytes.size) : b.read i = some (b.byte i) := by
  simp [Bytes.read, Bytes.byte, h]

/-- For the comparison with the C++ only: a view of the bytes a line of hex names. -/
def ofHex (s : String) : Bytes :=
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 0
  let rec pairs : List Char → List (BitVec 8)
    | a :: b :: rest => BitVec.ofNat 8 (digit a * 16 + digit b) :: pairs rest
    | _ => []
  let a := (pairs s.toList).toArray
  if h : a.size < 2 ^ 63 then ⟨a, h⟩ else ⟨#[], by decide⟩

end Bytes

/-- `memcpy` of n bytes from a view, at j, into an array, at k: `none` if either is passed, as a
read or a write outside an array is. -/
def copyIn (v : Vector (BitVec 8) m) (k : Nat) (b : Bytes) (j n : Nat) : Option (Vector (BitVec 8) m) :=
  if k + n ≤ m ∧ j + n ≤ b.bytes.size then
    some (Vector.ofFn fun i => if k ≤ i.val ∧ i.val < k + n then b.byte (j + (i.val - k)) else v[i])
  else none

/-- `memcpy` of n bytes from another array of the object, at j, into one, at k. -/
def copyOwn (v : Vector (BitVec 8) m) (k : Nat) (s : Vector (BitVec 8) p) (j n : Nat) : Option (Vector (BitVec 8) m) :=
  if k + n ≤ m ∧ j + n ≤ p then
    some (Vector.ofFn fun i => if k ≤ i.val ∧ i.val < k + n then s.toArray.getD (j + (i.val - k)) 0 else v[i])
  else none

/-- Within both, a copy has a result. -/
theorem copyIn_isSome (v : Vector (BitVec 8) m) (b : Bytes) (h1 : k + n ≤ m) (h2 : j + n ≤ b.bytes.size) :
    (copyIn v k b j n).isSome := by simp [copyIn, h1, h2]

theorem copyOwn_isSome (v : Vector (BitVec 8) m) (s : Vector (BitVec 8) p) (h1 : k + n ≤ m) (h2 : j + n ≤ p) :
    (copyOwn v k s j n).isSome := by simp [copyOwn, h1, h2]

/-- What a round of a loop says: go round again, the loop is done, or the method returns. -/
inductive Step (σ ρ : Type) where
  | next : σ → Step σ ρ
  | done : σ → Step σ ρ
  | ret : ρ → Step σ ρ

/-- For proofs about a loop: it is done (it did not run out of rounds, commit a memory error, or
return), and what it hands back satisfies `P`. -/
def DoneWith (r : Option (Step σ ρ)) (P : σ → Prop) : Prop := ∃ s, r = some (.done s) ∧ P s

@[simp] theorem doneWith_done (s : σ) (P : σ → Prop) : DoneWith (ρ := ρ) (some (.done s)) P ↔ P s := by
  simp [DoneWith]

theorem DoneWith.some (h : DoneWith r P) : ∃ s, r = some (Step.done s) ∧ P s := h

/-- A call of a function outside the program, by its contract: `none` where what the call is
handed does not keep the contract (a memory error, as a read outside an array is); else its answer. -/
def outside (ok : Prop) [Decidable ok] (r : α) : Option α := if ok then some r else none

/-- What the function gives back: a value the world chooses, within what its contract says (lo to
hi); `world` ranges over everything, so every such value is reached. -/
def pick (width : Nat) (lo hi : Int) (w : BitVec 64) : BitVec width :=
  BitVec.ofInt width (if lo ≤ w.toInt ∧ w.toInt ≤ hi then w.toInt else lo)

/-- The bytes it writes, at k, n of them: what the world says (its words 1, 2, ...). -/
def scribble (v : Vector (BitVec 8) m) (k n : Nat) (world : Nat → BitVec 64) : Vector (BitVec 8) m :=
  Vector.ofFn fun i => if k ≤ i.val ∧ i.val < k + n then (world (1 + (i.val - k))).setWidth 8 else v[i]

/-- For the comparison with the C++ only: a world, the same one the C++'s stand-in for the function
answers by (splitmix64). -/
def seeded (i : Nat) : BitVec 64 :=
  let z := BitVec.ofNat 64 (i + 1) * 0x9E3779B97F4A7C15#64
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9#64
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB#64
  z ^^^ (z >>> 31)

/-- What a counting loop rests on, said once for every loop: if each round, from a state where `P`
holds, either goes round again to a state where `P` holds and `measure` is less, or says the loop
is done in a state where `Q` holds, then within `measure + 1` rounds the loop is done, where `Q`
holds. For a loop `for ( i = a; i < b; i++ )` the measure is b less i. -/
theorem done_within {σ ρ : Type} (round : σ → Option (Step σ ρ)) (loop : Nat → σ → Option (Step σ ρ))
    (hs : ∀ left s, loop (left + 1) s = (round s).bind fun r => match r with
      | .next s' => loop left s' | .done s' => some (.done s') | .ret r => some (.ret r))
    (measure : σ → Nat) (P Q : σ → Prop)
    (hround : ∀ s, P s → (∃ s', round s = some (.next s') ∧ P s' ∧ measure s' < measure s) ∨
                          (∃ s', round s = some (.done s') ∧ Q s')) :
    ∀ left s, P s → measure s < left → DoneWith (loop left s) Q := by
  intro left
  induction left with
  | zero => intro s _ h; omega
  | succ left ih =>
    intro s hp hm
    rw [hs]
    rcases hround s hp with ⟨s', hr, hp', hm'⟩ | ⟨s', hr, hq⟩
    · simp [hr]; exact ih s' hp' (by omega)
    · simp [hr, hq]

/-- For proofs: there is a result (no memory error, and the rounds were enough), and it satisfies `P`. -/
def Ok (r : Option α) (P : α → Prop) : Prop := ∃ s, r = some s ∧ P s

@[simp] theorem ok_some (s : α) (P : α → Prop) : Ok (some s) P ↔ P s := by
  simp [Ok]

theorem Ok.isSome (h : Ok r P) : r.isSome := by
  obtain ⟨s, rfl, _⟩ := h; rfl

/-- What follows a step that is known to have a result. -/
theorem ok_bind {r : Option β} {f : β → Option α} {Q : β → Prop} {P : α → Prop}
    (h : Ok r Q) (hf : ∀ s, Q s → Ok (f s) P) : Ok (r.bind f) P := by
  obtain ⟨s, rfl, hq⟩ := h
  simpa using hf s hq

/-- What follows a loop that is known to be done. -/
theorem ok_bind_done {r : Option (Step σ ρ)} {f : Step σ ρ → Option α} {Q : σ → Prop} {P : α → Prop}
    (h : DoneWith r Q) (hf : ∀ s, Q s → Ok (f (.done s)) P) : Ok (r.bind f) P := by
  obtain ⟨s, rfl, hq⟩ := h
  simpa using hf s hq

/-- What a method that may throw, or end the process, gives back: what it returns; that it threw;
or that the process ended (`assert`, `exit`, `abort`). What is thrown is not read (it is made of
literals alone: the generator checked), so it says nothing of the state; the state a throw leaves
is the state the method had made by then. After an end nothing of the program runs, so nothing is
owed of the state it leaves. -/
inductive Outcome (α : Type) where
  | gave : α → Outcome α
  | thrown : Outcome α
  | ended : Outcome α

end Prooc
