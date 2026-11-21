import MeetupTimeOwed

/-! The proofs about MeetupTime, gosh's class (src/strong/meetup/time.h): what an end takes a
TIME's opened text for. Nothing here is trusted, and nothing here says what is owed: that is
`MeetupTime.Owed`, generated from the class as it stands, and `owed`, at the end, is a proof of
it. -/

namespace MeetupTime
namespace Claims

theorem new_safe : MeetupTime.new.isSome := by
  simp [MeetupTime.new]

theorem new_inv : ∀ (me : MeetupTime), MeetupTime.new = some me → Inv me := by
  intro me h; simp [MeetupTime.new] at h; subst h; simp [Inv]

/-- `read_checked` gives a result, and what it leaves keeps the invariant; and it leaves either
what was there, or what it read from a text of 16 bytes. It reads bytes 0 to 15 only where it has
just found there are 16, and keeps a counter only where it has just found it is under 2^62. -/
theorem read_ok (me : MeetupTime) (text : Prooc.Bytes) (hinv : Inv me) :
    ∃ me' r, MeetupTime.read_checked me text = some (me', r) ∧ Inv me' ∧
      (me' = me ∨ Prooc.Bytes.size text = 16#64) := by
  have hlen := Prooc.Bytes.size_toNat text
  simp only [MeetupTime.read_checked]
  by_cases h16 : Prooc.Bytes.size text = 16#64
  · have h16' : text.bytes.size = 16 := by bv_omega
    simp (disch := omega) [h16, Prooc.Bytes.read_of_lt]
    split <;> simp_all [Inv, BitVec.le_def, BitVec.lt_def]
  · simp [h16, hinv]

theorem read_checked_safe : ∀ (me : MeetupTime) (text : Prooc.Bytes), Inv me → (MeetupTime.read_checked me text).isSome := by
  intro me text h
  obtain ⟨me', r, hr, _, _⟩ := read_ok me text h
  simp [hr]

theorem read_checked_inv : ∀ (me : MeetupTime) (text : Prooc.Bytes) (me' : MeetupTime) (r : BitVec 8),
    Inv me → MeetupTime.read_checked me text = some (me', r) → Inv me' := by
  intro me text me' r h hr
  obtain ⟨me2, r2, hr2, hinv2, _⟩ := read_ok me text h
  rw [hr2] at hr
  cases hr
  exact hinv2

theorem answering_checked_safe : ∀ (me : MeetupTime), Inv me → (MeetupTime.answering_checked me).isSome := by
  intro me _; simp [MeetupTime.answering_checked]
theorem answering_checked_same : ∀ (me me' : MeetupTime) (r : BitVec 64), MeetupTime.answering_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupTime.answering_checked] at h; exact h.1.symm
theorem time_checked_safe : ∀ (me : MeetupTime), Inv me → (MeetupTime.time_checked me).isSome := by
  intro me _; simp [MeetupTime.time_checked]
theorem time_checked_same : ∀ (me me' : MeetupTime) (r : BitVec 64), MeetupTime.time_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupTime.time_checked] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : MeetupTime.Owed :=
  { new_safe, new_inv, read_checked_safe, read_checked_inv, answering_checked_safe, answering_checked_same, time_checked_safe,
    time_checked_same }

end Claims
end MeetupTime
