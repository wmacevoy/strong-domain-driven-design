import MeetupRegisteredOwed

/-! The proofs about MeetupRegistered, gosh's class (src/strong/meetup/registered.h): what an end takes
a REGISTERED's opened text for. Nothing here is trusted, and nothing here says what is owed: that is
`MeetupRegistered.Owed`, generated from the class as it stands, and `owed`, at the end, is a proof of
it. -/

namespace MeetupRegistered
namespace Claims

theorem new_safe : MeetupRegistered.new.isSome := by
  simp [MeetupRegistered.new]

theorem new_inv : ∀ (me : MeetupRegistered), MeetupRegistered.new = some me → Inv me := by
  intro me h; simp [MeetupRegistered.new] at h; subst h; simp [Inv]

/-- `read_checked` gives a result, and what it leaves keeps the invariant. Its text is a fixed
window of 19 bytes, read below 19 alone, so no read can fail; it keeps a family only where it has
just found it is 4 or 6. -/
theorem read_ok (me : MeetupRegistered) (text : Prooc.Bytes) (hinv : Inv me) :
    ∃ me' r, MeetupRegistered.read_checked me text = some (me', r) ∧ Inv me' := by
  simp only [MeetupRegistered.read_checked]
  by_cases h4 : (text.byte 0).setWidth 32 = 4#32
  · simp [h4, Inv]
  · by_cases h6 : (text.byte 0).setWidth 32 = 6#32
    · simp [h6, Inv]
    · simp [h4, h6, hinv]

theorem read_checked_safe : ∀ (me : MeetupRegistered) (text : Prooc.Bytes), Inv me → (MeetupRegistered.read_checked me text).isSome := by
  intro me text h
  obtain ⟨me', r, hr, _⟩ := read_ok me text h
  simp [hr]

theorem read_checked_inv : ∀ (me : MeetupRegistered) (text : Prooc.Bytes) (me' : MeetupRegistered) (r : BitVec 8),
    Inv me → MeetupRegistered.read_checked me text = some (me', r) → Inv me' := by
  intro me text me' r h hr
  obtain ⟨me2, r2, hr2, hinv2⟩ := read_ok me text h
  rw [hr2] at hr
  cases hr
  exact hinv2

theorem family_checked_safe : ∀ (me : MeetupRegistered), Inv me → (MeetupRegistered.family_checked me).isSome := by
  intro me _; simp [MeetupRegistered.family_checked]
theorem family_checked_same : ∀ (me me' : MeetupRegistered) (r : BitVec 32), MeetupRegistered.family_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupRegistered.family_checked] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : MeetupRegistered.Owed :=
  { new_safe, new_inv, read_checked_safe, read_checked_inv, family_checked_safe, family_checked_same }

end Claims
end MeetupRegistered
