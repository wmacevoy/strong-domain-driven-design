import PercentOwed

/-! The proofs about Percent. Nothing here is trusted, and nothing here says what is owed: that is
`Percent.Owed`, generated from the class as it stands in its own file, and `owed`, at the end, is a
proof of it. -/

namespace Percent
namespace Claims

theorem new_safe : ∀ (raw : BitVec 32), (Percent.new raw).isSome := by
  intro raw; simp [Percent.new]

/-- However it is made, it is at most 100: a remainder by 101 is. -/
theorem new_inv : ∀ (raw : BitVec 32) (me : Percent), Percent.new raw = some me → Inv me := by
  intro raw me h
  simp [Percent.new] at h
  subst h
  simp [Inv, BitVec.le_def]
  omega

theorem number_safe : ∀ (me : Percent), Inv me → (Percent.number me).isSome := by
  intro me _; simp [Percent.number]

theorem number_same : ∀ (me me' : Percent) (r : BitVec 32), Percent.number me = some (me', r) → me' = me := by
  intro me me' r h; simp [Percent.number] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Percent.Owed :=
  { new_safe, new_inv, number_safe, number_same }

end Claims
end Percent
