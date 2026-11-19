import ZerosOwed

/-! The proofs about Zeros. Nothing here is trusted, and nothing here says what is owed: that is
`Zeros.Owed` (ZerosOwed.lean, generated from the class), and `owed`, at the end, is a proof of it. -/

namespace Zeros
namespace Claims

/-- The loop is done within a round for every byte not yet read, and one more: each round reads
inside the view, because it has just tested that `i` is below its size. -/
theorem loop1_done (fuel left : Nat) (me : Zeros) (data : Prooc.Bytes) (i : BitVec 64)
    (hl : data.bytes.size - i.toNat < left) :
    Prooc.DoneWith (take.loop1 fuel left me data i) (fun _ => True) := by
  have hs := data.small
  have hlen := Prooc.Bytes.size_toNat data
  induction left generalizing me i with
  | zero => omega
  | succ left ih =>
    unfold take.loop1
    by_cases h : i < Prooc.Bytes.size data
    · have hlt : i.toNat < data.bytes.size := by bv_omega
      simp (disch := omega) [take.round1, h, Prooc.Bytes.read_of_lt]
      split <;> exact ih _ _ (by bv_omega)
    · simp [take.round1, h]

theorem new_safe : Zeros.new.isSome := by
  simp [Zeros.new]

theorem new_inv : ∀ (me : Zeros), Zeros.new = some me → Inv me := by
  intro me _; simp [Inv]

theorem take_ends : ∀ (me : Zeros) (data : Prooc.Bytes), Inv me →
    ∃ (fuel : Nat) (me' : Zeros) (r : Unit), Zeros.take fuel me data = some (me', r) ∧ Inv me' := by
  intro me data _
  obtain ⟨s, hs, _⟩ := loop1_done (data.bytes.size + 1) (data.bytes.size + 1) me data 0#64 (by simp)
  exact ⟨data.bytes.size + 1, s.1, (), by simp [Zeros.take, hs], by simp [Inv]⟩

theorem getZeros_safe : ∀ (me : Zeros), Inv me → (Zeros.getZeros me).isSome := by
  intro me _; simp [Zeros.getZeros]

theorem getZeros_same : ∀ (me me' : Zeros) (r : BitVec 64), Zeros.getZeros me = some (me', r) → me' = me := by
  intro me me' r h; simp [Zeros.getZeros] at h; exact h.1.symm

theorem getSeen_safe : ∀ (me : Zeros), Inv me → (Zeros.getSeen me).isSome := by
  intro me _; simp [Zeros.getSeen]

theorem getSeen_same : ∀ (me me' : Zeros) (r : BitVec 64), Zeros.getSeen me = some (me', r) → me' = me := by
  intro me me' r h; simp [Zeros.getSeen] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Zeros.Owed :=
  { new_safe, new_inv, take_ends, getZeros_safe, getZeros_same, getSeen_safe, getSeen_same }

end Claims
end Zeros
