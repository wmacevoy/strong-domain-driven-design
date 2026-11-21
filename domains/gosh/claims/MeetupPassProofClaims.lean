import MeetupPassProofOwed
import MeetupPassClaims

/-!
Proofs of what proofs/MeetupPass.proof.cpp claims, as gen/MeetupPassProofOwed.lean states it.
Written by an agent, and trusted for nothing: prove.sh checks it against that statement and
audits it.

They rest on `read_ok` (claims/MeetupPassClaims.lean): `read_checked` ends with no memory error,
keeps the invariant, and leaves what was there or a length of the text it was handed.
-/

namespace MeetupPassProof
namespace Claims

open MeetupPass in
/-- Everything owed. -/
theorem owed : MeetupPassProof.Owed where
  whatever_is_opened_is_a_datagram_of_1500_bytes_at_most_or_is_not_read := by
    simp [MeetupPass.new, MeetupPass.Inv, MeetupPass.length_checked]
  whatever_is_opened_is_a_datagram_of_1500_bytes_at_most_or_is_not_read_loop1 := by
    intro bytes me hinv
    intros
    obtain ⟨me', r, hr, hinv', _⟩ := MeetupPass.Claims.read_ok me bytes hinv
    refine ⟨me', r, hr, ?_⟩
    simp_all [MeetupPass.length_checked, MeetupPass.Inv]
  a_pass_that_is_read_is_of_the_text_it_was_handed_loop1 := by
    intro bytes
    have hnew : MeetupPass.Inv { length := 0#64 } := by simp [MeetupPass.Inv]
    obtain ⟨me', r, hr, _, hof⟩ := MeetupPass.Claims.read_ok _ bytes hnew
    refine ⟨{ length := 0#64 }, ?_, me', r, hr, ?_⟩
    · first | rfl | simp [MeetupPass.new, MeetupPass.raw]
    · rcases hof with h | h <;> simp_all [MeetupPass.length_checked]

end Claims
end MeetupPassProof
