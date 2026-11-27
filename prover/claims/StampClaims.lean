import StampOwed

/-! The proofs about Stamp. Nothing here is trusted, and nothing here says what is owed: that is
`Stamp.Owed`, generated from the class. Each copy is past a test that its bytes are all there, or
is of a length within both arrays, so each has a result; the invariant claims nothing. -/

namespace Stamp
namespace Claims

theorem new_safe : Stamp.new.isSome := by simp [Stamp.new]

theorem new_inv : ∀ (me : Stamp), Stamp.new = some me → Inv me := by
  intro me _; simp [Inv]

theorem keep_safe : ∀ (me : Stamp) (p : Prooc.Bytes) («at» : BitVec 64), Inv me → (Stamp.keep me p «at»).isSome := by
  intro me p a _
  unfold Stamp.keep
  by_cases h : (a > p.size) ∨ (p.size - a < 8#64)
  · simp [h]
  · simp only [not_or] at h
    have hs := Prooc.Bytes.size_toNat p
    have h1 : a.toNat + 8 ≤ p.bytes.size := by
      have ⟨ha, hb⟩ := h
      simp only [BitVec.lt_def, BitVec.not_lt, BitVec.le_def] at ha hb
      rw [BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using ha)] at hb
      simp at hb; omega
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Prooc.copyIn_isSome me.head p (k := 0) (n := 8) (by omega) (by simpa using h1))
    simp [h, hv]

theorem keep_inv : ∀ (me : Stamp) (p : Prooc.Bytes) («at» : BitVec 64) (me' : Stamp) (r : BitVec 8),
    Inv me → Stamp.keep me p «at» = some (me', r) → Inv me' := by
  intro _ _ _ _ _ _ _; simp [Inv]

theorem keep_tail_safe : ∀ (me : Stamp) (s : Prooc.Bytes), Inv me → (Stamp.keep_tail me s).isSome := by
  intro me s _
  unfold Stamp.keep_tail
  by_cases h : s.size < 4#64
  · simp [h]
  · have hs := Prooc.Bytes.size_toNat s
    have h1 : 4 ≤ s.bytes.size := by simp only [BitVec.lt_def] at h; simp at h; omega
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Prooc.copyIn_isSome me.tail s (k := 0) (j := 0) (n := 4) (by omega) (by omega))
    simp [h, hv]

theorem keep_tail_inv : ∀ (me : Stamp) (s : Prooc.Bytes) (me' : Stamp) (r : Unit),
    Inv me → Stamp.keep_tail me s = some (me', r) → Inv me' := by
  intro _ _ _ _ _ _; simp [Inv]

theorem fold_safe : ∀ (me : Stamp), Inv me → (Stamp.fold me).isSome := by
  intro me _
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Prooc.copyOwn_isSome me.head me.tail (k := 4) (j := 0) (n := 4) (by omega) (by omega))
  simp [Stamp.fold, hv]

theorem fold_inv : ∀ (me : Stamp) (me' : Stamp) (r : Unit), Inv me → Stamp.fold me = some (me', r) → Inv me' := by
  intro _ _ _ _ _; simp [Inv]

theorem first_safe : ∀ (me : Stamp), Inv me → (Stamp.first me).isSome := by
  intro me _; simp [Stamp.first, Prooc.get]

theorem first_same : ∀ (me me' : Stamp) (r : BitVec 32), Stamp.first me = some (me', r) → me' = me := by
  intro me me' r h; simp [Stamp.first, Prooc.get] at h; exact h.1.symm

theorem count_safe : ∀ (me : Stamp), Inv me → (Stamp.count me).isSome := by
  intro me _; simp [Stamp.count]

theorem count_same : ∀ (me me' : Stamp) (r : BitVec 64), Stamp.count me = some (me', r) → me' = me := by
  intro me me' r h; simp [Stamp.count] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Stamp.Owed :=
  { new_safe, new_inv, keep_safe, keep_inv, keep_tail_safe, keep_tail_inv, fold_safe, fold_inv,
    first_safe, first_same, count_safe, count_same }

end Claims
end Stamp
