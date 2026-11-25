import WaterOwed

/-! The proofs about Water, a part of the station. Nothing here is trusted, and nothing here says
what is owed: that is `Water.Owed`, generated from the class as it stands in its own file, and
`owed`, at the end, is a proof of it. -/

namespace Water
namespace Claims

theorem new_safe : Water.new.isSome := by simp [Water.new]

theorem new_inv : ∀ (me : Water), Water.new = some me → Inv me := by
  intro me h; simp [Water.new] at h; subst h; simp [Inv]

theorem level_safe : ∀ (me : Water), Inv me → (Water.level me).isSome := by
  intro me _; simp [Water.level]

theorem level_same : ∀ (me me' : Water) (r : BitVec 32), Water.level me = some (me', r) → me' = me := by
  intro me me' r h; simp [Water.level] at h; exact h.1.symm

/-- Safe only where its caller keeps what it expects: that what is taken is there. -/
theorem take_safe : ∀ (me : Water) (n : BitVec 32), Inv me → Water.take_pre me n → (Water.take me n).isSome := by
  intro me n _ hp; simp [Water.take, hp]

theorem take_inv : ∀ (me : Water) (n : BitVec 32) (me' : Water) (r : Unit),
    Inv me → Water.take_pre me n → Water.take me n = some (me', r) → Inv me' := by
  intro me n me' r hi _ h
  simp only [Water.take] at h
  by_cases hp : Water.take_pre me n
  · simp [hp] at h; obtain ⟨rfl, -⟩ := h
    simp only [Inv, take_pre] at *; bv_omega
  · simp [hp] at h

theorem fill_safe : ∀ (me : Water), Inv me → (Water.fill me).isSome := by
  intro me _; simp [Water.fill]

theorem fill_inv : ∀ (me : Water) (me' : Water) (r : Unit), Inv me → Water.fill me = some (me', r) → Inv me' := by
  intro me me' r _ h; simp [Water.fill] at h; obtain ⟨rfl, -⟩ := h; simp [Inv]

/-- Everything owed. -/
theorem owed : Water.Owed :=
  { new_safe, new_inv, level_safe, level_same, take_safe, take_inv, fill_safe, fill_inv }

end Claims
end Water
