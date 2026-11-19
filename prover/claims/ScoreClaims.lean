import ScoreOwed

/-! The proofs about Score. Nothing here is trusted, and nothing here says what is owed: that is
`Score.Owed`, generated from the class as it stands in its own file, and `owed`, at the end, is a
proof of it. The constructor tests nothing: that a Score is at most 100 is what it expects of its
caller, and so what its model has a result for. -/

namespace Score
namespace Claims

theorem new_safe : ∀ (raw : BitVec 32), Score.new_pre raw → (Score.new raw).isSome := by
  intro raw h; simp [Score.new, h]

theorem new_inv : ∀ (raw : BitVec 32) (me : Score), Score.new raw = some me → Inv me := by
  intro raw me h
  by_cases hp : Score.new_pre raw
  · simp [Score.new, hp] at h
    subst h
    simpa [Inv, Score.new_pre] using hp
  · simp [Score.new, hp] at h

theorem number_safe : ∀ (me : Score), Inv me → (Score.number me).isSome := by
  intro me _; simp [Score.number]

theorem number_same : ∀ (me me' : Score) (r : BitVec 32), Score.number me = some (me', r) → me' = me := by
  intro me me' r h; simp [Score.number] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Score.Owed :=
  { new_safe, new_inv, number_safe, number_same }

end Claims
end Score
