import MeetupCounterOwed

/-! The proofs about MeetupCounter, gosh's type for a counter of 62 bits (src/meetup/counter.h).
Nothing here is trusted, and nothing here says what is owed: that is `MeetupCounter.Owed`,
generated from the class as it stands, and `owed`, at the end, is a proof of it. -/

namespace MeetupCounter
namespace Claims

theorem new_safe : ∀ (nonce : BitVec 64), (MeetupCounter.new nonce).isSome := by
  intro nonce; simp [MeetupCounter.new]

/-- However it is made, it is at most 2^62 - 1: the constructor keeps only those bits. -/
theorem new_inv : ∀ (nonce : BitVec 64) (me : MeetupCounter), MeetupCounter.new nonce = some me → Inv me := by
  intro nonce me h
  simp [MeetupCounter.new] at h
  subst h
  simp only [Inv, BitVec.le_def, BitVec.toNat_and, BitVec.toNat_ofNat]
  exact Nat.le_trans Nat.and_le_right (by decide)

theorem number_safe : ∀ (me : MeetupCounter), Inv me → (MeetupCounter.number me).isSome := by
  intro me _; simp [MeetupCounter.number]

theorem number_same : ∀ (me me' : MeetupCounter) (r : BitVec 64),
    MeetupCounter.number me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupCounter.number] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : MeetupCounter.Owed :=
  { new_safe, new_inv, number_safe, number_same }

end Claims
end MeetupCounter
