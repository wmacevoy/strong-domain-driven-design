import ChecksumOwed

/-! The proofs about Checksum. Nothing here is trusted, and nothing here says what is owed: that is
`Checksum.Owed`, generated from the class as it stands in its own file, and `owed`, at the end, is a
proof of it. -/

namespace Checksum
namespace Claims

/-- The loop is done within a round for every byte not yet read, and one more: each round reads
below the length, because it has just tested that `i` is below it. -/
theorem loop1_done (fuel left : Nat) (me : Checksum) (data : Prooc.Bytes) (i : BitVec 64)
    (hl : data.bytes.size - i.toNat < left) :
    Prooc.DoneWith (add.loop1 fuel left me data i) (fun _ => True) := by
  have hs := data.small
  have hlen := Prooc.Bytes.size_toNat data
  induction left generalizing me i with
  | zero => omega
  | succ left ih =>
    unfold add.loop1
    by_cases h : i < Prooc.Bytes.size data
    · have hlt : i.toNat < data.bytes.size := by bv_omega
      simp (disch := omega) [add.round1, h, Prooc.Bytes.read_of_lt]
      exact ih _ _ (by bv_omega)
    · simp [add.round1, h]

theorem new_safe : Checksum.new.isSome := by
  simp [Checksum.new]

theorem new_inv : ∀ (me : Checksum), Checksum.new = some me → Inv me := by
  intro me _; simp [Inv]

theorem add_ends : ∀ (me : Checksum) (data : Prooc.Bytes), Inv me →
    ∃ (fuel : Nat) (me' : Checksum) (r : Unit), Checksum.add fuel me data = some (me', r) ∧ Inv me' := by
  intro me data _
  obtain ⟨s, hs, _⟩ := loop1_done (data.bytes.size + 1) (data.bytes.size + 1) me data 0#64 (by simp)
  exact ⟨data.bytes.size + 1, _, (), by simp [Checksum.add, hs]; rfl, by simp [Inv]⟩

theorem get_safe : ∀ (me : Checksum), Inv me → (Checksum.get me).isSome := by
  intro me _; simp [Checksum.get]

theorem get_same : ∀ (me me' : Checksum) (r : BitVec 32), Checksum.get me = some (me', r) → me' = me := by
  intro me me' r h; simp [Checksum.get] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Checksum.Owed :=
  { new_safe, new_inv, add_ends, get_safe, get_same }

end Claims
end Checksum
