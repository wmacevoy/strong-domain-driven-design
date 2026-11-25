import TrayOwed

/-! The proofs about Tray, a part of the station. Nothing here is trusted, and nothing here says
what is owed: that is `Tray.Owed`, generated from the class as it stands in its own file, and
`owed`, at the end, is a proof of it. -/

namespace Tray
namespace Claims

theorem new_safe : Tray.new.isSome := by simp [Tray.new]

theorem new_inv : ∀ (me : Tray), Tray.new = some me → Inv me := by
  intro me h; simp [Tray.new] at h; subst h; simp [Inv]

theorem held_safe : ∀ (me : Tray), Inv me → (Tray.held me).isSome := by
  intro me _; simp [Tray.held]

theorem held_same : ∀ (me me' : Tray) (r : BitVec 32), Tray.held me = some (me', r) → me' = me := by
  intro me me' r h; simp [Tray.held] at h; exact h.1.symm

theorem room_safe : ∀ (me : Tray), Inv me → (Tray.room me).isSome := by
  intro me _; simp [Tray.room]

theorem room_same : ∀ (me me' : Tray) (r : BitVec 32), Tray.room me = some (me', r) → me' = me := by
  intro me me' r h; simp [Tray.room] at h; exact h.1.symm

/-- Safe only where its caller keeps what it expects: that there is room. -/
theorem add_safe : ∀ (me : Tray) (n : BitVec 32), Inv me → Tray.add_pre me n → (Tray.add me n).isSome := by
  intro me n _ hp; simp [Tray.add, hp]

theorem add_inv : ∀ (me : Tray) (n : BitVec 32) (me' : Tray) (r : Unit),
    Inv me → Tray.add_pre me n → Tray.add me n = some (me', r) → Inv me' := by
  intro me n me' r hi _ h
  simp only [Tray.add] at h
  by_cases hp : Tray.add_pre me n
  · simp [hp] at h; obtain ⟨rfl, -⟩ := h
    simp only [Inv, add_pre] at *; bv_omega
  · simp [hp] at h

theorem empty_safe : ∀ (me : Tray), Inv me → (Tray.empty me).isSome := by
  intro me _; simp [Tray.empty]

theorem empty_inv : ∀ (me : Tray) (me' : Tray) (r : Unit), Inv me → Tray.empty me = some (me', r) → Inv me' := by
  intro me me' r _ h; simp [Tray.empty] at h; obtain ⟨rfl, -⟩ := h; simp [Inv]

/-- Everything owed. -/
theorem owed : Tray.Owed :=
  { new_safe, new_inv, held_safe, held_same, room_safe, room_same, add_safe, add_inv, empty_safe, empty_inv }

end Claims
end Tray
