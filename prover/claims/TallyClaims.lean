import TallyOwed

/-! The proofs about Tally. Nothing here is trusted, and nothing here says what is owed: that is
`Tally.Owed` (TallyOwed.lean, generated from the class), and `owed`, at the end, is a proof of it. -/

namespace Tally
namespace Claims

/-- Why `see` stays inside the array: a byte's low two bits are a number below 4. -/
theorem kind_lt (byte : BitVec 8) : byte.toNat % 4294967296 &&& 3 < 4 := by
  have := @Nat.and_le_right (byte.toNat % 4294967296) 3
  omega

theorem new_safe : Tally.new.isSome := by
  simp [Tally.new, Prooc.set_of_lt]

theorem new_inv : ∀ (me : Tally), Tally.new = some me → Inv me := by
  intro me h
  simp [Tally.new, Prooc.set_of_lt] at h
  subst h
  simp [Inv, Tally.raw]

theorem see_safe : ∀ (me : Tally) (byte : BitVec 8), Inv me → (Tally.see me byte).isSome := by
  intro me byte _
  have hk := kind_lt byte
  simp [Tally.see]
  generalize byte.toNat % 4294967296 &&& 3 = k at hk
  simp [Prooc.get_of_lt, Prooc.set_of_lt, hk]

theorem see_inv : ∀ (me : Tally) (byte : BitVec 8) (me' : Tally) (r : Unit),
    Inv me → Tally.see me byte = some (me', r) → Inv me' := by
  intro me byte me' r hinv h
  have hk := kind_lt byte
  simp [Tally.see] at h
  generalize byte.toNat % 4294967296 &&& 3 = k at h hk
  simp [Prooc.get_of_lt, Prooc.set_of_lt, hk] at h
  subst h
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  simp only [Inv] at hinv ⊢
  rcases hcases with rfl | rfl | rfl | rfl <;> simp <;> rw [hinv] <;> bv_omega

theorem of_safe : ∀ (me : Tally) (kind : BitVec 32), Inv me → (Tally.«of» me kind).isSome := by
  intro me kind _
  simp [Tally.«of»]
  split
  · simp
  · have hk : kind.toNat < 4 := by bv_omega
    simp [Prooc.get_of_lt, hk]

theorem of_same : ∀ (me : Tally) (kind : BitVec 32) (me' : Tally) (r : BitVec 32),
    Tally.«of» me kind = some (me', r) → me' = me := by
  intro me kind me' r h
  simp [Tally.«of»] at h
  split at h
  · simp at h; exact h.1.symm
  · have hk : kind.toNat < 4 := by bv_omega
    simp [Prooc.get_of_lt, hk] at h
    exact h.1.symm

theorem getTotal_safe : ∀ (me : Tally), Inv me → (Tally.getTotal me).isSome := by
  intro me _; simp [Tally.getTotal]

theorem getTotal_same : ∀ (me me' : Tally) (r : BitVec 32), Tally.getTotal me = some (me', r) → me' = me := by
  intro me me' r h; simp [Tally.getTotal] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Tally.Owed :=
  { new_safe, new_inv, see_safe, see_inv, of_safe, of_same, getTotal_safe, getTotal_same }

end Claims
end Tally
