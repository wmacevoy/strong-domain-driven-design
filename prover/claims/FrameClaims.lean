import FrameOwed

/-! The proofs about Frame. Nothing here is trusted, and nothing here says what is owed: that is
`Frame.Owed`, generated from the class. Past its bounds test, n is from 24 to 65536, so n - 8 made
an int is that number itself (below 2^31), and taking 16 from it cannot overflow. -/

namespace Frame
namespace Claims

/-- Past the bounds test: the body's length as an int is n - 8, and below 2^31. -/
theorem body_small (n : BitVec 64) (lo : ¬ n < 24#64) (hi : ¬ n > 65536#64) :
    ((n - 8#64).setWidth 32).toNat = n.toNat - 8 ∧ n.toNat - 8 < 65529 := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat] at lo hi
  have h8 : (n - 8#64).toNat = n.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le] <;> simp [BitVec.le_def] <;> omega
  simp [BitVec.toNat_setWidth, h8]
  omega

theorem no_overflow (n : BitVec 64) (lo : ¬ n < 24#64) (hi : ¬ n > 65536#64) :
    ((n - 8#64).setWidth 32).ssubOverflow 16#32 = false := by
  obtain ⟨h, hs⟩ := body_small n lo hi
  have lo' : 24 ≤ n.toNat := by simp only [BitVec.lt_def, BitVec.toNat_ofNat] at lo; omega
  have := BitVec.ssubOverflow_eq ((n - 8#64).setWidth 32) 16#32
  rw [this]
  have hm : ((n - 8#64).setWidth 32).msb = false := by
    rw [BitVec.msb_eq_decide]; simp [h]; omega
  have hm2 : ((n - 8#64).setWidth 32 - 16#32).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_sub_of_le] <;> simp [BitVec.le_def, h] <;> omega
  simp [hm, hm2]

theorem new_safe : Frame.new.isSome := by simp [Frame.new]

theorem new_inv : ∀ (me : Frame), Frame.new = some me → Inv me := by
  intro me h; simp [Frame.new] at h; subst h; simp [Inv]

theorem carried_safe : ∀ (me : Frame) (n : BitVec 64), Inv me → (Frame.carried me n).isSome := by
  intro me n _
  unfold Frame.carried
  by_cases h : (n < 24#64) ∨ (n > 65536#64)
  · simp [h]
  · simp only [not_or] at h
    simp [h, Prooc.ssub, no_overflow n h.1 h.2]
    split <;> simp

theorem carried_inv : ∀ (me : Frame) (n : BitVec 64) (me' : Frame) (r : BitVec 64),
    Inv me → Frame.carried me n = some (me', r) → Inv me' := by
  intro me n me' r hi h
  unfold Frame.carried at h
  by_cases hb : (n < 24#64) ∨ (n > 65536#64)
  · simp [hb] at h; obtain ⟨rfl, _⟩ := h; exact hi
  · simp only [not_or] at hb
    simp [hb, Prooc.ssub, no_overflow n hb.1 hb.2] at h
    split at h
    · simp at h; obtain ⟨rfl, _⟩ := h; exact hi
    · simp at h
      obtain ⟨rfl, _⟩ := h
      obtain ⟨hn, hs⟩ := body_small n hb.1 hb.2
      have hm : ((n - 8#64).setWidth 32).msb = false := by
        rw [BitVec.msb_eq_decide]; simp [hn]; omega
      simp only [Inv, BitVec.le_def, BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, hn, BitVec.toNat_ofNat]
      omega

theorem last_body_safe : ∀ (me : Frame), Inv me → (Frame.last_body me).isSome := by
  intro me _; simp [Frame.last_body]

theorem last_body_same : ∀ (me me' : Frame) (r : BitVec 64), Frame.last_body me = some (me', r) → me' = me := by
  intro me me' r h; simp [Frame.last_body] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Frame.Owed :=
  { new_safe, new_inv, carried_safe, carried_inv, last_body_safe, last_body_same }

end Claims
end Frame
