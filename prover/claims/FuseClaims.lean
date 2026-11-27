import FuseOwed

/-! The proofs about Fuse. Nothing here is trusted, and nothing here says what is owed: that is
`Fuse.Owed`, generated from the class. At the fourth blow the process ends, and nothing is owed of
the state then; before it, the count goes up by one from at most 2. -/

namespace Fuse
namespace Claims

theorem new_safe : Fuse.new.isSome := by simp [Fuse.new]

theorem new_inv : ∀ (me : Fuse), Fuse.new = some me → Inv me := by
  intro me h
  simp [Fuse.new] at h
  subst h
  simp [Inv]

theorem blow_safe : ∀ (me : Fuse), Inv me → (Fuse.blow me).isSome := by
  intro me _
  unfold Fuse.blow
  by_cases h : me.blows = 3#32 <;> simp [h]

theorem blow_inv : ∀ (me : Fuse) (me' : Fuse) (r : Prooc.Outcome (BitVec 32)),
    Inv me → Fuse.blow me = some (me', r) → r ≠ Prooc.Outcome.ended → Inv me' := by
  intro me me' r hi h hr
  unfold Fuse.blow at h
  by_cases hb : me.blows = 3#32
  · simp [hb] at h
    obtain ⟨_, rfl⟩ := h
    exact absurd rfl hr
  · simp [hb] at h
    obtain ⟨rfl, _⟩ := h
    simp only [Inv] at *
    bv_omega

theorem count_safe : ∀ (me : Fuse), Inv me → (Fuse.count me).isSome := by
  intro me _; simp [Fuse.count]

theorem count_same : ∀ (me me' : Fuse) (r : BitVec 32), Fuse.count me = some (me', r) → me' = me := by
  intro me me' r h; simp [Fuse.count] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Fuse.Owed :=
  { new_safe, new_inv, blow_safe, blow_inv, count_safe, count_same }

end Claims
end Fuse
