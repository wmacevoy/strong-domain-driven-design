import DialOwed

/-! The proofs about Dial. Nothing here is trusted, and nothing here says what is owed: that is
`Dial.Owed`, generated from the class as it stands in its own file, and `owed`, at the end, is a
proof of it. What Dial is given of a Percent is Percent's invariant, and nothing more. -/

namespace Dial
namespace Claims

/-- Why `mark` and `times` stay inside the 101: a Percent is at most 100, by its own invariant. -/
theorem index_lt (p : Percent) (hp : Percent.Inv p) : p.value.toNat < 101 := by
  simp only [Percent.Inv] at hp
  bv_omega

theorem new_safe : Dial.new.isSome := by
  simp [Dial.new]

theorem new_inv : ∀ (me : Dial), Dial.new = some me → Inv me := by
  intro me h
  simp [Dial.new] at h
  subst h
  simp [Inv]

theorem mark_safe : ∀ (me : Dial) (p : Percent), Inv me → Percent.Inv p → (Dial.mark me p).isSome := by
  intro me p _ hp
  have hi := index_lt p hp
  simp [Dial.mark, Percent.number, Prooc.get, Prooc.set, hi]

theorem mark_inv : ∀ (me : Dial) (p : Percent) (me' : Dial) (r : Unit),
    Inv me → Percent.Inv p → Dial.mark me p = some (me', r) → Inv me' := by
  intro me p me' r _ hp h
  have hi := index_lt p hp
  simp [Dial.mark, Percent.number, Prooc.get, Prooc.set, hi] at h
  subst h
  simpa [Inv, Percent.Inv] using hp

theorem times_safe : ∀ (me : Dial) (p : Percent), Inv me → Percent.Inv p → (Dial.times me p).isSome := by
  intro me p _ hp
  have hi := index_lt p hp
  simp [Dial.times, Percent.number, Prooc.get, hi]

theorem times_same : ∀ (me : Dial) (p : Percent) (me' : Dial) (r : BitVec 32),
    Dial.times me p = some (me', r) → me' = me := by
  intro me p me' r h
  simp only [Dial.times, Percent.number] at h
  cases hg : Prooc.get me.seen p.value.toNat with
  | none => simp [hg] at h
  | some v => simp [hg] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Dial.Owed :=
  { new_safe, new_inv, mark_safe, mark_inv, times_safe, times_same }

end Claims
end Dial
