import MeetupRegisterOwed

/-! The proofs about MeetupRegister, gosh's class (src/strong/meetupregister.h): what a meetup takes
a REGISTER's opened text for. Nothing here is trusted, and nothing here says what is owed: that is
`MeetupRegister.Owed`, generated from the class as it stands, and `owed`, at the end, is a proof of
it. -/

namespace MeetupRegister
namespace Claims

theorem new_safe : MeetupRegister.new.isSome := by
  simp [MeetupRegister.new]

theorem new_inv : ∀ (me : MeetupRegister), MeetupRegister.new = some me → Inv me := by
  intro me h; simp [MeetupRegister.new] at h; subst h; simp [Inv]

/-- `read_checked` gives a result, and what it leaves keeps the invariant; and it leaves either
what was there, or a family of 4 or 6 read from a text of 27 bytes. It reads bytes 0 and 19 to 26
only where it has just found there are 27. -/
theorem read_ok (me : MeetupRegister) (text : Prooc.Bytes) (hinv : Inv me) :
    ∃ me' r, MeetupRegister.read_checked me text = some (me', r) ∧ Inv me' ∧
      (me' = me ∨ (Prooc.Bytes.size text = 27#64 ∧ (me'.family = 4#32 ∨ me'.family = 6#32))) := by
  have hlen := Prooc.Bytes.size_toNat text
  simp only [MeetupRegister.read_checked]
  by_cases h27 : Prooc.Bytes.size text = 27#64
  · have h27' : text.bytes.size = 27 := by bv_omega
    simp (disch := omega) [h27, Prooc.Bytes.read_of_lt]
    by_cases h4 : (text.byte 0).setWidth 32 = 4#32
    · simp [h4, Inv]
    · by_cases h6 : (text.byte 0).setWidth 32 = 6#32
      · simp [h6, Inv]
      · simp [h4, h6, hinv]
  · simp [h27, hinv]

theorem read_checked_safe : ∀ (me : MeetupRegister) (text : Prooc.Bytes), Inv me → (MeetupRegister.read_checked me text).isSome := by
  intro me text h
  obtain ⟨me', r, hr, _, _⟩ := read_ok me text h
  simp [hr]

theorem read_checked_inv : ∀ (me : MeetupRegister) (text : Prooc.Bytes) (me' : MeetupRegister) (r : BitVec 8),
    Inv me → MeetupRegister.read_checked me text = some (me', r) → Inv me' := by
  intro me text me' r h hr
  obtain ⟨me2, r2, hr2, hinv2, _⟩ := read_ok me text h
  rw [hr2] at hr
  cases hr
  exact hinv2

theorem family_checked_safe : ∀ (me : MeetupRegister), Inv me → (MeetupRegister.family_checked me).isSome := by
  intro me _; simp [MeetupRegister.family_checked]
theorem family_checked_same : ∀ (me me' : MeetupRegister) (r : BitVec 32), MeetupRegister.family_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupRegister.family_checked] at h; exact h.1.symm
theorem time_checked_safe : ∀ (me : MeetupRegister), Inv me → (MeetupRegister.time_checked me).isSome := by
  intro me _; simp [MeetupRegister.time_checked]
theorem time_checked_same : ∀ (me me' : MeetupRegister) (r : BitVec 64), MeetupRegister.time_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupRegister.time_checked] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : MeetupRegister.Owed :=
  { new_safe, new_inv, read_checked_safe, read_checked_inv, family_checked_safe, family_checked_same, time_checked_safe,
    time_checked_same }

end Claims
end MeetupRegister
