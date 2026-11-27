import RationOwed

/-! The proofs about Ration. Nothing here is trusted, and nothing here says what is owed: that is
`Ration.Owed`, generated from the class. Each method that throws does so before it changes
anything, so the state a throw leaves is the state it was given, which kept the invariant. -/

namespace Ration
namespace Claims

theorem new_safe : Ration.new.isSome := by simp [Ration.new]

theorem new_inv : ∀ (me : Ration), Ration.new = some me → Inv me := by
  intro me h
  simp [Ration.new] at h
  subst h
  simp [Inv]

theorem take_safe : ∀ (me : Ration) (n : BitVec 32), Inv me → (Ration.take me n).isSome := by
  intro me n _
  unfold Ration.take
  by_cases h : n > me.stock <;> simp [h] <;> split <;> simp

theorem take_inv : ∀ (me : Ration) (n : BitVec 32) (me' : Ration) (r : Prooc.Outcome (BitVec 32)),
    Inv me → Ration.take me n = some (me', r) → r ≠ Prooc.Outcome.ended → Inv me' := by
  intro me n me' r hi h hr
  unfold Ration.take at h
  by_cases hn : n > me.stock
  · simp [hn] at h
    obtain ⟨rfl, _⟩ := h
    exact hi
  · simp [hn] at h
    split at h
    · simp at h
      obtain ⟨rfl, _⟩ := h
      simp only [Inv] at *
      bv_omega
    · simp at h
      obtain ⟨_, rfl⟩ := h
      exact absurd rfl hr

theorem refill_safe : ∀ (me : Ration), Inv me → (Ration.refill me).isSome := by
  intro me _
  unfold Ration.refill
  by_cases h : me.taken = 0#32 <;> simp [h]

theorem refill_inv : ∀ (me : Ration) (me' : Ration) (r : Prooc.Outcome Unit),
    Inv me → Ration.refill me = some (me', r) → Inv me' := by
  intro me me' r hi h
  unfold Ration.refill at h
  by_cases ht : me.taken = 0#32
  · simp [ht] at h
    obtain ⟨rfl, _⟩ := h
    exact hi
  · simp [ht] at h
    obtain ⟨rfl, _⟩ := h
    simp [Inv]

theorem remaining_safe : ∀ (me : Ration), Inv me → (Ration.remaining me).isSome := by
  intro me _; simp [Ration.remaining]

theorem remaining_same : ∀ (me me' : Ration) (r : BitVec 32), Ration.remaining me = some (me', r) → me' = me := by
  intro me me' r h; simp [Ration.remaining] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Ration.Owed :=
  { new_safe, new_inv, take_safe, take_inv, refill_safe, refill_inv, remaining_safe, remaining_same }

end Claims
end Ration
