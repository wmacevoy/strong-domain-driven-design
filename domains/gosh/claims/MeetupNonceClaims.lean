import MeetupNonceOwed

/-! The proofs about MeetupNonce, gosh's class (src/strong/meetup/nonce.h): what a meetup message
is sealed with. Nothing here is trusted, and nothing here says what is owed: that is
`MeetupNonce.Owed`, generated from the class as it stands, and `owed`, at the end, is a proof of
it.

The class has no array and no loop, so "no memory error" and "it ends" are immediate. What takes
work is its numbers: that the low 62 bits, bit 62 and bit 63 of a 64-bit number are the whole of
it. That is said once of plain numbers (`nat_back`, `nat_parts`), by arithmetic, and carried to
the 64-bit values the model uses. -/

namespace MeetupNonce
namespace Claims

/-- The low 62 bits of anything are at most 2^62 - 1. -/
theorem low_le (x : BitVec 64) : x &&& 4611686018427387903#64 ≤ 4611686018427387903#64 := by
  have := @Nat.and_le_right x.toNat 4611686018427387903
  simp [BitVec.le_def]; exact this

/-- Bit 62 of anything is 0 or 1. -/
theorem end_le (x : BitVec 64) : ((x >>> 62) &&& 1#64).setWidth 32 ≤ 1#32 := by
  have := @Nat.and_le_right (x.toNat >>> 62) 1
  simp [BitVec.le_def]; omega

/-- Bit 63 of anything is 0 or 1. -/
theorem by_le (x : BitVec 64) : (x >>> 63).setWidth 32 ≤ 1#32 := by
  simp [BitVec.le_def, Nat.shiftRight_eq_div_pow]; omega

/-- A number below 2^64 is its bit 63, its bit 62 and its low 62 bits, put together. -/
theorem nat_back (n : Nat) (h : n < 2 ^ 64) :
    (n / 2 ^ 63) <<< 63 ||| (n / 2 ^ 62 % 2) <<< 62 ||| n % 2 ^ 62 = n := by
  have a : (n / 2 ^ 62 % 2) <<< 62 ||| n % 2 ^ 62 = (n / 2 ^ 62 % 2) <<< 62 + n % 2 ^ 62 :=
    (Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)) _).symm
  have b : (n / 2 ^ 63) <<< 63 ||| ((n / 2 ^ 62 % 2) <<< 62 + n % 2 ^ 62)
      = (n / 2 ^ 63) <<< 63 + ((n / 2 ^ 62 % 2) <<< 62 + n % 2 ^ 62) := by
    refine (Nat.shiftLeft_add_eq_or_of_lt ?_ _).symm
    simp only [Nat.shiftLeft_eq]; omega
  rw [Nat.or_assoc, a, b]; simp only [Nat.shiftLeft_eq]; omega

/-- The same of a 64-bit value, as `read_checked` takes it apart and `value_checked` puts it
together: a nonce read and written again is that nonce. -/
theorem back (x : BitVec 64) :
    ((((x >>> 63).setWidth 32).setWidth 64 <<< 63) ||| ((((x >>> 62) &&& 1#64).setWidth 32).setWidth 64 <<< 62))
      ||| (x &&& 4611686018427387903#64) = x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hlow := Nat.and_two_pow_sub_one_eq_mod x.toNat 62
  have h1 := Nat.and_two_pow_sub_one_eq_mod (x.toNat >>> 62) 1
  have hn := nat_back x.toNat hx
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_and, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq] at hlow h1 hn ⊢
  rw [hlow, h1]
  have e1 : x.toNat / 9223372036854775808 % 4294967296 % 18446744073709551616 * 9223372036854775808 % 18446744073709551616
      = x.toNat / 9223372036854775808 * 9223372036854775808 := by omega
  have e2 : x.toNat / 4611686018427387904 % 2 % 4294967296 % 18446744073709551616 * 4611686018427387904 % 18446744073709551616
      = x.toNat / 4611686018427387904 % 2 * 4611686018427387904 := by
    have t : x.toNat / 4611686018427387904 % 2 = 0 ∨ x.toNat / 4611686018427387904 % 2 = 1 := by omega
    rcases t with t | t <;> rw [t]
  rw [e1, e2]; exact hn

theorem new_safe : MeetupNonce.new.isSome := by
  simp [MeetupNonce.new]

theorem new_inv : ∀ (me : MeetupNonce), MeetupNonce.new = some me → Inv me := by
  intro me h; simp [MeetupNonce.new] at h; subst h; simp [Inv]

theorem set_checked_safe : ∀ (me : MeetupNonce) (an_end sealed_by_meetup : BitVec 32) (a_counter : BitVec 64),
    Inv me → (MeetupNonce.set_checked me an_end sealed_by_meetup a_counter).isSome := by
  intro me e m c _; simp only [MeetupNonce.set_checked]; repeat' split
  all_goals simp

theorem set_checked_inv : ∀ (me : MeetupNonce) (an_end sealed_by_meetup : BitVec 32) (a_counter : BitVec 64) (me' : MeetupNonce) (r : Unit),
    Inv me → MeetupNonce.set_checked me an_end sealed_by_meetup a_counter = some (me', r) → Inv me' := by
  intro me e m c me' r _ h
  have hc := low_le c
  by_cases he : e = 0#32 <;> by_cases hm : m = 0#32 <;> simp [MeetupNonce.set_checked, he, hm] at h <;>
    (first | (obtain ⟨rfl, _⟩ := h) | subst h) <;> simp [Inv, hc]

theorem read_checked_safe : ∀ (me : MeetupNonce) (nonce : BitVec 64), Inv me → (MeetupNonce.read_checked me nonce).isSome := by
  intro me n _; simp [MeetupNonce.read_checked]

theorem read_checked_inv : ∀ (me : MeetupNonce) (nonce : BitVec 64) (me' : MeetupNonce) (r : Unit),
    Inv me → MeetupNonce.read_checked me nonce = some (me', r) → Inv me' := by
  intro me n me' r _ h
  simp only [MeetupNonce.read_checked] at h
  injection h with h; injection h with h _; subst h
  exact ⟨⟨end_le n, by_le n⟩, low_le n⟩

theorem value_checked_safe : ∀ (me : MeetupNonce), Inv me → (MeetupNonce.value_checked me).isSome := by
  intro me _; simp [MeetupNonce.value_checked]
theorem value_checked_same : ∀ (me me' : MeetupNonce) (r : BitVec 64), MeetupNonce.value_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupNonce.value_checked] at h; exact h.1.symm
theorem end_checked_safe : ∀ (me : MeetupNonce), Inv me → (MeetupNonce.end_checked me).isSome := by
  intro me _; simp [MeetupNonce.end_checked]
theorem end_checked_same : ∀ (me me' : MeetupNonce) (r : BitVec 32), MeetupNonce.end_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupNonce.end_checked] at h; exact h.1.symm
theorem by_meetup_checked_safe : ∀ (me : MeetupNonce), Inv me → (MeetupNonce.by_meetup_checked me).isSome := by
  intro me _; simp [MeetupNonce.by_meetup_checked]
theorem by_meetup_checked_same : ∀ (me me' : MeetupNonce) (r : BitVec 32), MeetupNonce.by_meetup_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupNonce.by_meetup_checked] at h; exact h.1.symm
theorem counter_checked_safe : ∀ (me : MeetupNonce), Inv me → (MeetupNonce.counter_checked me).isSome := by
  intro me _; simp [MeetupNonce.counter_checked]
theorem counter_checked_same : ∀ (me me' : MeetupNonce) (r : BitVec 64), MeetupNonce.counter_checked me = some (me', r) → me' = me := by
  intro me me' r h; simp [MeetupNonce.counter_checked] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : MeetupNonce.Owed :=
  { new_safe, new_inv, set_checked_safe, set_checked_inv, read_checked_safe, read_checked_inv, value_checked_safe,
    value_checked_same, end_checked_safe, end_checked_same, by_meetup_checked_safe, by_meetup_checked_same,
    counter_checked_safe, counter_checked_same }

end Claims
end MeetupNonce
