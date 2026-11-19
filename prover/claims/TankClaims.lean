import TankOwed

/-! The proofs about Tank. Nothing here is trusted, and nothing here says what is owed: that is
`Tank.Owed`, generated from the class as it stands in its own file, and `owed`, at the end, is a
proof of it. What Tank is given of a Level is bounded_of's invariant at 0 and 100, and nothing
more; and where Tank makes a Level, that the number is within 0 and 100 is proved here. -/

namespace Tank
namespace Claims

/-- Why `fill` stays inside the 101 places: a Level is at most 100, by the type's invariant. -/
theorem index_lt (to : bounded_of (BitVec 32)) (h : bounded_of.Inv 0#32 100#32 to) : to.value.toNat < 101 := by
  simp only [bounded_of.Inv] at h
  bv_omega

theorem new_safe : Tank.new.isSome := by
  simp [Tank.new]

theorem new_inv : ∀ (me : Tank), Tank.new = some me → Inv me := by
  intro me h
  simp [Tank.new] at h
  subst h
  simp [Inv]

theorem fill_safe : ∀ (me : Tank) (to : bounded_of (BitVec 32)), Inv me → bounded_of.Inv 0#32 100#32 to → (Tank.fill me to).isSome := by
  intro me to _ h
  have hi := index_lt to h
  simp [Tank.fill, bounded_of.number, Prooc.get, Prooc.set, hi]

theorem fill_inv : ∀ (me : Tank) (to : bounded_of (BitVec 32)) (me' : Tank) (r : Unit),
    Inv me → bounded_of.Inv 0#32 100#32 to → Tank.fill me to = some (me', r) → Inv me' := by
  intro me to me' r _ h hf
  have hi := index_lt to h
  simp [Tank.fill, bounded_of.number, Prooc.get, Prooc.set, hi] at hf
  subst hf
  simpa [Inv, bounded_of.Inv] using h.2

/-- A remainder by 101 is what a Level's constructor expects: from 0 to 100. -/
theorem made (n : BitVec 32) : bounded_of.new_pre 0#32 100#32 (n % 101#32) := by
  simp [bounded_of.new_pre, BitVec.le_def]
  omega

theorem fill_number_some (me : Tank) (n : BitVec 32) (hinv : Inv me) :
    ∃ v, Tank.fill me { value := n % 101#32 } = some v ∧ Inv v.1 := by
  have hp := made n
  have hl : bounded_of.Inv 0#32 100#32 ({ value := n % 101#32 } : bounded_of (BitVec 32)) := by
    simpa [bounded_of.Inv, bounded_of.new_pre] using hp
  have hs := fill_safe me { value := n % 101#32 } hinv hl
  cases hg : Tank.fill me { value := n % 101#32 } with
  | none => simp [hg] at hs
  | some v => exact ⟨v, rfl, fill_inv me _ v.1 v.2 hinv hl hg⟩

theorem fill_number_safe : ∀ (me : Tank) (n : BitVec 32), Inv me → (Tank.fill_number me n).isSome := by
  intro me n hinv
  obtain ⟨v, hv, _⟩ := fill_number_some me n hinv
  simp [Tank.fill_number, bounded_of.new, made n, hv]

theorem fill_number_inv : ∀ (me : Tank) (n : BitVec 32) (me' : Tank) (r : Unit),
    Inv me → Tank.fill_number me n = some (me', r) → Inv me' := by
  intro me n me' r hinv h
  obtain ⟨v, hv, hi⟩ := fill_number_some me n hinv
  simp [Tank.fill_number, bounded_of.new, made n, hv] at h
  rw [← h]; exact hi

/-- The way in for code that is not proved: a LevelChecked is within the bounds (its invariant:
making one is what tested), so the Level `fill_checked` makes of its number is made rightly, and
`fill` is given what it expects. -/
theorem fill_checked_some (me : Tank) (n : bounded_checked_of (BitVec 32)) (hinv : Inv me)
    (hn : bounded_checked_of.Inv 0#32 100#32 n) :
    ∃ v, Tank.fill_checked me n = some v ∧ Inv v.1 := by
  have hb : 0#32 ≤ n.value ∧ n.value ≤ 100#32 := by simpa [bounded_checked_of.Inv] using hn
  have hl : bounded_of.Inv 0#32 100#32 ({ value := n.value } : bounded_of (BitVec 32)) := by
    simpa [bounded_of.Inv] using hb
  have hs := fill_safe me { value := n.value } hinv hl
  cases hf : Tank.fill me { value := n.value } with
  | none => simp [hf] at hs
  | some v =>
    refine ⟨(v.1, ()), ?_, fill_inv me _ v.1 v.2 hinv hl hf⟩
    simp [Tank.fill_checked, bounded_checked_of.number, bounded_of.new, bounded_of.new_pre, hb, hf]

theorem fill_checked_safe : ∀ (me : Tank) (n : bounded_checked_of (BitVec 32)), Inv me →
    bounded_checked_of.Inv 0#32 100#32 n → (Tank.fill_checked me n).isSome := by
  intro me n hinv hn
  obtain ⟨v, hv, _⟩ := fill_checked_some me n hinv hn
  simp [hv]

theorem fill_checked_inv : ∀ (me : Tank) (n : bounded_checked_of (BitVec 32)) (me' : Tank) (r : Unit),
    Inv me → bounded_checked_of.Inv 0#32 100#32 n → Tank.fill_checked me n = some (me', r) → Inv me' := by
  intro me n me' r hinv hn h
  obtain ⟨v, hv, hi⟩ := fill_checked_some me n hinv hn
  rw [hv] at h
  cases h; exact hi

theorem at_safe : ∀ (me : Tank), Inv me → (Tank.«at» me).isSome := by
  intro me _; simp [Tank.«at»]

theorem at_same : ∀ (me me' : Tank) (r : BitVec 32), Tank.«at» me = some (me', r) → me' = me := by
  intro me me' r h; simp [Tank.«at»] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Tank.Owed :=
  { new_safe, new_inv, fill_safe, fill_inv, fill_number_safe, fill_number_inv, fill_checked_safe, fill_checked_inv, at_safe, at_same }

end Claims
end Tank
