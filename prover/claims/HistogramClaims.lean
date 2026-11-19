import HistogramOwed

/-! The proofs about Histogram. Nothing here is trusted, and nothing here says what is owed: that
is `Histogram.Owed` (HistogramOwed.lean, generated from the class as it stands in its own file),
and `owed`, at the end, is a proof of it. -/

namespace Histogram
namespace Claims

/-- Why `full` and `bump` stay inside the array: a remainder by 8 is below 8. -/
theorem bin_lt (bin : BitVec 32) : bin.toNat % 8 < 8 := by omega

theorem full_some (me : Histogram) (bin : BitVec 32) :
    ∃ b, Histogram.full me bin = some (me, b) := by
  simp [Histogram.full, Prooc.get, bin_lt]

/-- `bump` has a result, and keeps the invariant: one more in a bin, and one more in the total. -/
theorem bump_ok (me : Histogram) (bin : BitVec 32) (hinv : Inv me) :
    Prooc.Ok (Histogram.bump me bin) (fun s => Inv s.1 ∧ s.1.wrapped = me.wrapped) := by
  have hk : (bin % 8#32).toNat < 8 := by simp [BitVec.toNat_umod]; omega
  simp only [Histogram.bump]
  generalize (bin % 8#32).toNat = k at hk ⊢
  simp [Prooc.get_of_lt, Prooc.set_of_lt, hk]
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  simp only [Inv] at hinv ⊢
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> rw [hinv] <;> bv_omega

theorem new_safe : Histogram.new.isSome := by
  simp [Histogram.new]

theorem new_inv : ∀ (me : Histogram), Histogram.new = some me → Inv me := by
  intro me h
  simp [Histogram.new] at h
  subst h
  simp [Inv]

theorem add_safe : ∀ (me : Histogram) (value : BitVec 32), Inv me → (Histogram.add me value).isSome := by
  intro me value hinv
  obtain ⟨b, hb⟩ := full_some me value
  obtain ⟨s, hs, _⟩ := bump_ok me value hinv
  simp [Histogram.add, hb, hs]
  split <;> simp

theorem add_inv : ∀ (me : Histogram) (value : BitVec 32) (me' : Histogram) (r : BitVec 8),
    Inv me → Histogram.add me value = some (me', r) → Inv me' := by
  intro me value me' r hinv h
  obtain ⟨b, hb⟩ := full_some me value
  obtain ⟨s, hs, hsinv, _⟩ := bump_ok me value hinv
  simp [Histogram.add, hb, hs] at h
  split at h
  · simp at h; rw [← h.1]; exact hsinv
  · simp at h; rw [← h.1]; simpa [Inv] using hinv

/-- Why `share` divides by nothing that is zero: `total` is tested first. -/
theorem share_safe : ∀ (me : Histogram) (bin : BitVec 32) (parts : BitVec 32), Inv me →
    (Histogram.share me bin parts).isSome := by
  intro me bin parts _
  simp only [Histogram.share]
  by_cases h : me.total = 0#32 ∨ bin ≥ 8#32
  · simp [h]
  · have hb : bin.toNat < 8 := by bv_omega
    have ht : me.total ≠ 0#32 := fun e => h (Or.inl e)
    simp [h, Prooc.div, Prooc.get, hb, ht]
    split <;> simp

theorem share_same : ∀ (me : Histogram) (bin : BitVec 32) (parts : BitVec 32) (me' : Histogram) (r : BitVec 32),
    Histogram.share me bin parts = some (me', r) → me' = me := by
  intro me bin parts me' r h
  simp only [Histogram.share] at h
  by_cases hc : me.total = 0#32 ∨ bin ≥ 8#32
  · simp [hc] at h; exact h.1.symm
  · have hb : bin.toNat < 8 := by bv_omega
    have ht : me.total ≠ 0#32 := fun e => hc (Or.inl e)
    simp [hc, Prooc.div, Prooc.get, hb, ht] at h
    split at h <;> simp at h <;> exact h.1.symm

/-- The loop is done within nine rounds: `i` is one more each round, and at 8 it stops. -/
theorem loop1_done (fuel left : Nat) (me : Histogram) (most i : BitVec 32) (hl : 9 - i.toNat < left) :
    Prooc.DoneWith (largest.loop1 fuel left me most i) (fun _ => True) := by
  induction left generalizing most i with
  | zero => omega
  | succ left ih =>
    unfold largest.loop1
    by_cases h : i < 8#32
    · have hi : i.toNat < 8 := by bv_omega
      simp [largest.round1, h, Prooc.get, hi]
      split <;> exact ih _ _ (by bv_omega)
    · simp [largest.round1, h]

/-- The loop never returns from inside itself: so what `largest` gives back is the object it was given. -/
theorem loop1_noret (fuel left : Nat) (me : Histogram) (most i : BitVec 32) (a : Histogram × BitVec 32) :
    largest.loop1 fuel left me most i ≠ some (.ret a) := by
  induction left generalizing most i with
  | zero => simp [largest.loop1]
  | succ left ih =>
    unfold largest.loop1
    by_cases h : i < 8#32
    · have hi : i.toNat < 8 := by bv_omega
      simp [largest.round1, h, Prooc.get, hi]
      split <;> exact ih _ _
    · simp [largest.round1, h]

theorem largest_ends : ∀ (me : Histogram), Inv me → ∃ (fuel : Nat), (Histogram.largest fuel me).isSome := by
  intro me _
  obtain ⟨s, hs, _⟩ := loop1_done 10 10 me 0#32 0#32 (by simp)
  exact ⟨10, by simp [Histogram.largest, hs]⟩

theorem largest_same : ∀ (fuel : Nat) (me : Histogram) (me' : Histogram) (r : BitVec 32),
    Histogram.largest fuel me = some (me', r) → me' = me := by
  intro fuel me me' r h
  simp only [Histogram.largest] at h
  cases hl : largest.loop1 fuel fuel me 0#32 0#32 with
  | none => simp [hl] at h
  | some s =>
    cases s with
    | ret a => exact absurd hl (loop1_noret fuel fuel me 0#32 0#32 a)
    | next s => simp [hl] at h; exact h.1.symm
    | done s => simp [hl] at h; exact h.1.symm

theorem reset_safe : ∀ (me : Histogram), Inv me → (Histogram.reset me).isSome := by
  intro me _; simp [Histogram.reset]

theorem reset_inv : ∀ (me : Histogram) (me' : Histogram) (r : Unit),
    Inv me → Histogram.reset me = some (me', r) → Inv me' := by
  intro me me' r _ h
  simp [Histogram.reset] at h
  subst h
  simp [Inv]

/-- Everything owed. -/
theorem owed : Histogram.Owed :=
  { new_safe, new_inv, add_safe, add_inv, share_safe, share_same, largest_ends, largest_same,
    reset_safe, reset_inv }

end Claims
end Histogram
