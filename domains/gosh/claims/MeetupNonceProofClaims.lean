import MeetupNonceProofOwed
import MeetupNonceClaims

/-!
Proofs of what proofs/MeetupNonce.proof.cpp claims, as gen/MeetupNonceProofOwed.lean states it.
Written by an agent, and trusted for nothing: prove.sh checks it against that statement and
audits it.

The first rests on `back` (claims/MeetupNonceClaims.lean): bit 63, bit 62 and the low 62 bits of
a 64-bit number are the whole of it. The second is the other way, said here (`parts`): from a
sender (one of four) and a counter below 2^62 put together, each comes out again.
-/

namespace MeetupNonceProof
namespace Claims

/-- Of plain numbers: k is the sender (0 to 3), c the counter. Put together, each comes out. -/
theorem nat_parts (k c : Nat) (_ : k < 4) (hc : c < 2 ^ 62) :
    (k <<< 62 ||| c) / 2 ^ 63 = k / 2 ∧ (k <<< 62 ||| c) / 2 ^ 62 % 2 = k % 2 ∧ (k <<< 62 ||| c) % 2 ^ 62 = c := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hc]
  simp only [Nat.shiftLeft_eq]
  omega

/-- A 32-bit number that is at most 1 is 0 or 1. -/
theorem bit (x : BitVec 32) (h : x ≤ 1#32) : x = 0#32 ∨ x = 1#32 := by
  simp [BitVec.le_def] at h
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with h | h
  · left; exact BitVec.eq_of_toNat_eq h
  · right; exact BitVec.eq_of_toNat_eq h

/-- The same of the 64-bit values the model uses, for each of the four senders. -/
theorem parts (m e : BitVec 32) (c : BitVec 64) (hm : m ≤ 1#32) (he : e ≤ 1#32) (hc : c ≤ 4611686018427387903#64) :
    (((((m.setWidth 64 <<< 63) ||| (e.setWidth 64 <<< 62)) ||| c) >>> 62) &&& 1#64).setWidth 32 = e
      ∧ ((((m.setWidth 64 <<< 63) ||| (e.setWidth 64 <<< 62)) ||| c) >>> 63).setWidth 32 = m
      ∧ (((m.setWidth 64 <<< 63) ||| (e.setWidth 64 <<< 62)) ||| c) &&& 4611686018427387903#64 = c := by
  generalize hv : ((m.setWidth 64 <<< 63) ||| (e.setWidth 64 <<< 62)) ||| c = v
  have hc' : c.toNat < 2 ^ 62 := by simp [BitVec.le_def] at hc; omega
  have hm' := bit m hm
  have he' := bit e he
  have key : ∀ k : Nat, k < 4 → v.toNat = k <<< 62 ||| c.toNat →
      ((v >>> 62) &&& 1#64).setWidth 32 = BitVec.ofNat 32 (k % 2) ∧ (v >>> 63).setWidth 32 = BitVec.ofNat 32 (k / 2)
        ∧ v &&& 4611686018427387903#64 = c := by
    intro k hk hv
    obtain ⟨p63, p62, plow⟩ := nat_parts k c.toNat hk hc'
    have hlow := Nat.and_two_pow_sub_one_eq_mod v.toNat 62
    have h1 := Nat.and_two_pow_sub_one_eq_mod (v.toNat >>> 62) 1
    refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_and, BitVec.toNat_ofNat] <;>
      simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.shiftRight_eq_div_pow] at hlow h1 p63 p62 plow ⊢
    · rw [h1, hv, p62]
    · rw [hv, p63]
    · rw [hlow, hv, plow]
  rcases hm' with rfl | rfl <;> rcases he' with rfl | rfl
  · exact key 0 (by decide) (by rw [← hv]; simp)
  · exact key 1 (by decide) (by rw [← hv]; simp)
  · exact key 2 (by decide) (by rw [← hv]; simp)
  · exact key 3 (by decide) (by rw [← hv]; simp)

/-- A counter of 62 bits is its own low 62 bits. -/
theorem low_same (c : BitVec 64) (hc : c ≤ 4611686018427387903#64) : c &&& 4611686018427387903#64 = c := by
  apply BitVec.eq_of_toNat_eq
  have h := Nat.and_two_pow_sub_one_eq_mod c.toNat 62
  simp [BitVec.le_def] at hc
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at h ⊢
  rw [h]; omega

/-- `set_checked`, handed a sender there is and a counter of 62 bits, keeps exactly those. -/
theorem set_eq (me : MeetupNonce) (e m : BitVec 32) (c : BitVec 64) (he : e ≤ 1#32) (hm : m ≤ 1#32) (hc : c ≤ 4611686018427387903#64) :
    MeetupNonce.set_checked me e m c = some ({ «end» := e, by_meetup := m, counter := c }, ()) := by
  have hl := low_same c hc
  rcases bit e he with rfl | rfl <;> rcases bit m hm with rfl | rfl <;> simp [MeetupNonce.set_checked, hl]

/-- Everything owed. -/
theorem owed : MeetupNonceProof.Owed where
  every_nonce_reads_as_a_sender_and_a_counter_that_write_it_again_loop1 := by
    intro n
    refine ⟨_, rfl, _, rfl, ⟨⟨MeetupNonce.Claims.end_le n, MeetupNonce.Claims.by_le n⟩, MeetupNonce.Claims.low_le n⟩,
      ⟨_, _, _, rfl, rfl, rfl, ⟨MeetupNonce.Claims.end_le n, MeetupNonce.Claims.by_le n⟩, MeetupNonce.Claims.low_le n⟩,
      ⟨_, rfl, MeetupNonce.Claims.back n⟩, trivial⟩
  a_sender_and_a_counter_written_as_a_nonce_are_read_again_as_themselves_loop3 := by
    intro e m c _ he _ hm _ hc
    obtain ⟨p1, p2, p3⟩ := parts m e c hm he hc
    exact ⟨_, rfl, _, set_eq _ e m c he hm hc, _, rfl, _, rfl, ⟨_, _, _, rfl, rfl, rfl, ⟨p1, p2⟩, p3⟩, trivial⟩

end Claims
end MeetupNonceProof
