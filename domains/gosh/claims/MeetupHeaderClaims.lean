import MeetupHeaderOwed

/-! The proofs about MeetupHeader, gosh's class (src/strong/meetupheader.h): what a meetup, and an
end, take a datagram from anyone for. Nothing here is trusted, and nothing here says what is
owed: that is `MeetupHeader.Owed`, generated from the class as it stands, and `owed`, at the end,
is a proof of it. -/

namespace MeetupHeader
namespace Claims

theorem new_safe : MeetupHeader.new.isSome := by
  simp [MeetupHeader.new]

theorem new_inv : ∀ (me : MeetupHeader), MeetupHeader.new = some me → Inv me := by
  intro me h; simp [MeetupHeader.new] at h; subst h; simp [Inv]

/-- `kind_of` always gives a kind, and leaves the object: what it gives is from 0 to 5. -/
theorem kind_of_ok (me : MeetupHeader) (a b c : BitVec 32) :
    ∃ k, MeetupHeader.kind_of me a b c = some (me, k) ∧ k ≤ 5#32 := by
  simp only [MeetupHeader.kind_of]
  repeat' split
  all_goals simp

/-- `right_length` always gives an answer, and leaves the object. Where the answer is not 0, the
length is one a message of that kind has. -/
theorem right_length_ok (me : MeetupHeader) (k : BitVec 32) (n : BitVec 64) :
    ∃ f, MeetupHeader.right_length me k n = some (me, f) ∧
      (f ≠ 0#32 → (k = 1#32 ∧ n = 78#64) ∨ (k = 2#32 ∧ n = 70#64) ∨ (k = 3#32 ∧ 52#64 ≤ n ∧ n ≤ 1551#64)
        ∨ (k = 4#32 ∧ 10#64 ≤ n ∧ n ≤ 1509#64) ∨ (k = 5#32 ∧ n = 67#64)) := by
  simp only [MeetupHeader.right_length]
  repeat' split
  all_goals simp_all

/-- Every way through what is left of a method: take each `if` both ways, let `simp` run what
follows, and leave what remains, comparisons of numbers, to `bv_omega`. -/
macro "walk" : tactic =>
  `(tactic| (iterate 8 (all_goals (repeat' split)
                        all_goals (try simp_all))
             all_goals (try simp_all [Inv])
             all_goals (try bv_omega)))

/-- `read_checked` gives a result, and what it leaves keeps the invariant; and it leaves either
what was there, or a head of this very datagram. It reads bytes 0 to 8 only where there are 9, and
byte 25 only where the kind's length, which it has just tested, says there are at least 52. -/
theorem read_ok (me : MeetupHeader) (data : Prooc.Bytes) (hinv : Inv me) :
    ∃ me' r, MeetupHeader.read_checked me data = some (me', r) ∧ Inv me' ∧ (me' = me ∨ me'.whole = Prooc.Bytes.size data) := by
  have hlen := Prooc.Bytes.size_toNat data
  simp only [MeetupHeader.read_checked]
  by_cases h9 : Prooc.Bytes.size data < 9#64
  · simp [h9, hinv]
  · have h9' : 9 ≤ data.bytes.size := by bv_omega
    obtain ⟨k, hk, hk5⟩ := kind_of_ok me ((data.byte 5).setWidth 32) ((data.byte 6).setWidth 32) ((data.byte 7).setWidth 32)
    obtain ⟨f, hf, hfits⟩ := right_length_ok me k (Prooc.Bytes.size data)
    by_cases hf0 : f = 0#32
    · -- no length for this kind: nothing is kept
      simp (disch := omega) [h9, Prooc.Bytes.read_of_lt, hk, hf, hf0]
      walk
    · have hcase := hfits hf0
      by_cases hk4 : k = 4#32
      · -- PASSED
        simp (disch := omega) [h9, Prooc.Bytes.read_of_lt, hk, hf, hf0, hk4]
        walk
      · -- the others are at least 52 bytes: byte 25 is there
        have h26 : 26 ≤ data.bytes.size := by
          rcases hcase with h | h | h | h | h <;> bv_omega
        simp (disch := omega) [h9, Prooc.Bytes.read_of_lt, hk, hf, hf0, hk4]
        walk

theorem read_checked_safe : ∀ (me : MeetupHeader) (data : Prooc.Bytes), Inv me → (MeetupHeader.read_checked me data).isSome := by
  intro me data h
  obtain ⟨me', r, hr, _, _⟩ := read_ok me data h
  simp [hr]

theorem read_checked_inv : ∀ (me : MeetupHeader) (data : Prooc.Bytes) (me' : MeetupHeader) (r : BitVec 8),
    Inv me → MeetupHeader.read_checked me data = some (me', r) → Inv me' := by
  intro me data me' r h hr
  obtain ⟨me2, r2, hr2, hinv2, _⟩ := read_ok me data h
  rw [hr2] at hr
  cases hr
  exact hinv2

theorem kind_checked_safe : ∀ (me : MeetupHeader), Inv me → (MeetupHeader.kind_checked me).isSome := by
  intro me _; simp [MeetupHeader.kind_checked]
theorem kind_checked_same : ∀ (me me' : MeetupHeader) (r : BitVec 32), MeetupHeader.kind_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupHeader.kind_checked] at h; exact h.1.symm
theorem end_checked_safe : ∀ (me : MeetupHeader), Inv me → (MeetupHeader.end_checked me).isSome := by
  intro me _; simp [MeetupHeader.end_checked]
theorem end_checked_same : ∀ (me me' : MeetupHeader) (r : BitVec 32), MeetupHeader.end_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupHeader.end_checked] at h; exact h.1.symm
theorem whole_checked_safe : ∀ (me : MeetupHeader), Inv me → (MeetupHeader.whole_checked me).isSome := by
  intro me _; simp [MeetupHeader.whole_checked]
theorem whole_checked_same : ∀ (me me' : MeetupHeader) (r : BitVec 64), MeetupHeader.whole_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupHeader.whole_checked] at h; exact h.1.symm
theorem sealed_from_checked_safe : ∀ (me : MeetupHeader), Inv me → (MeetupHeader.sealed_from_checked me).isSome := by
  intro me _; simp [MeetupHeader.sealed_from_checked]
theorem sealed_from_checked_same : ∀ (me me' : MeetupHeader) (r : BitVec 64), MeetupHeader.sealed_from_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupHeader.sealed_from_checked] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : MeetupHeader.Owed :=
  { new_safe, new_inv, read_checked_safe, read_checked_inv, kind_checked_safe, kind_checked_same, end_checked_safe,
    end_checked_same, whole_checked_safe, whole_checked_same, sealed_from_checked_safe, sealed_from_checked_same }

end Claims
end MeetupHeader
