import BoardOwed

/-! The proofs about Board. Nothing here is trusted, and nothing here says what is owed: that is
`Board.Owed`, generated from the class as it stands in its own file, and `owed`, at the end, is a
proof of it. `mark_number` makes a Score: that it gives Score's constructor what that expects is
proved here, of the caller, and nowhere tested. -/

namespace Board
namespace Claims

theorem index_lt (s : Score) (hs : Score.Inv s) : s.value.toNat < 101 := by
  simp only [Score.Inv] at hs
  bv_omega

theorem new_safe : Board.new.isSome := by
  simp [Board.new]

theorem new_inv : ∀ (me : Board), Board.new = some me → Inv me := by
  intro me _; simp [Inv]

theorem mark_safe : ∀ (me : Board) (s : Score), Inv me → Score.Inv s → (Board.mark me s).isSome := by
  intro me s _ hs
  have hi := index_lt s hs
  simp [Board.mark, Score.number, Prooc.get, Prooc.set, hi]

theorem mark_inv : ∀ (me : Board) (s : Score) (me' : Board) (r : Unit),
    Inv me → Score.Inv s → Board.mark me s = some (me', r) → Inv me' := by
  intro me s me' r _ _ _; simp [Inv]

/-- A remainder by 101 is what Score's constructor expects: at most 100. -/
theorem made (n : BitVec 32) : Score.new_pre (n % 101#32) := by
  simp [Score.new_pre, BitVec.le_def]
  omega

theorem mark_number_safe : ∀ (me : Board) (n : BitVec 32), Inv me → (Board.mark_number me n).isSome := by
  intro me n hinv
  have hp := made n
  have hs : Score.Inv { value := n % 101#32 } := by simpa [Score.Inv, Score.new_pre] using hp
  have hm := mark_safe me { value := n % 101#32 } hinv hs
  cases hg : Board.mark me { value := n % 101#32 } with
  | none => simp [hg] at hm
  | some v => simp [Board.mark_number, Score.new, hp, hg]

theorem mark_number_inv : ∀ (me : Board) (n : BitVec 32) (me' : Board) (r : Unit),
    Inv me → Board.mark_number me n = some (me', r) → Inv me' := by
  intro me n me' r _ _; simp [Inv]

theorem times_safe : ∀ (me : Board) (s : Score), Inv me → Score.Inv s → (Board.times me s).isSome := by
  intro me s _ hs
  have hi := index_lt s hs
  simp [Board.times, Score.number, Prooc.get, hi]

theorem times_same : ∀ (me : Board) (s : Score) (me' : Board) (r : BitVec 32),
    Board.times me s = some (me', r) → me' = me := by
  intro me s me' r h
  simp only [Board.times, Score.number] at h
  cases hg : Prooc.get me.seen s.value.toNat with
  | none => simp [hg] at h
  | some v => simp [hg] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Board.Owed :=
  { new_safe, new_inv, mark_safe, mark_inv, mark_number_safe, mark_number_inv, times_safe, times_same }

end Claims
end Board
