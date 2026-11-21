import MeetupPassOwed

/-! The proofs about MeetupPass, gosh's class (src/strong/meetup/pass.h): what a meetup takes a PASS's
opened text for. Nothing here is trusted, and nothing here says what is owed: that is
`MeetupPass.Owed`, generated from the class as it stands, and `owed`, at the end, is a proof of it. -/

namespace MeetupPass
namespace Claims

theorem new_safe : MeetupPass.new.isSome := by
  simp [MeetupPass.new]

theorem new_inv : ∀ (me : MeetupPass), MeetupPass.new = some me → Inv me := by
  intro me h; simp [MeetupPass.new] at h; subst h; simp [Inv]

/-- `read_checked` gives a result, and what it leaves keeps the invariant, and is what was there or
of the text it was handed. It reads no byte, only the text's size, so it cannot fail; it keeps a
length only where it has just found it is 1 to 1500. -/
theorem read_ok (me : MeetupPass) (text : Prooc.Bytes) (hinv : Inv me) :
    ∃ me' r, MeetupPass.read_checked me text = some (me', r) ∧ Inv me' ∧ (me' = me ∨ me'.length = Prooc.Bytes.size text) := by
  simp only [MeetupPass.read_checked]
  split
  · exact ⟨me, 0#8, rfl, hinv, Or.inl rfl⟩
  · rename_i h
    refine ⟨_, 1#8, rfl, ?_, Or.inr rfl⟩
    simp only [Inv]
    simp only [not_or] at h
    bv_omega

theorem read_checked_safe : ∀ (me : MeetupPass) (text : Prooc.Bytes), Inv me → (MeetupPass.read_checked me text).isSome := by
  intro me text h
  obtain ⟨me', r, hr, _⟩ := read_ok me text h
  simp [hr]

theorem read_checked_inv : ∀ (me : MeetupPass) (text : Prooc.Bytes) (me' : MeetupPass) (r : BitVec 8),
    Inv me → MeetupPass.read_checked me text = some (me', r) → Inv me' := by
  intro me text me' r h hr
  obtain ⟨me2, r2, hr2, hinv2, _⟩ := read_ok me text h
  rw [hr2] at hr
  cases hr
  exact hinv2

theorem length_checked_safe : ∀ (me : MeetupPass), Inv me → (MeetupPass.length_checked me).isSome := by
  intro me _; simp [MeetupPass.length_checked]
theorem length_checked_same : ∀ (me me' : MeetupPass) (r : BitVec 64), MeetupPass.length_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupPass.length_checked] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : MeetupPass.Owed :=
  { new_safe, new_inv, read_checked_safe, read_checked_inv, length_checked_safe, length_checked_same }

end Claims
end MeetupPass
