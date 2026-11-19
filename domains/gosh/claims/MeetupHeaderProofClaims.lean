import MeetupHeaderProofOwed
import MeetupHeaderClaims

/-!
Proofs of what proofs/MeetupHeader.proof.cpp claims, as gen/MeetupHeaderProofOwed.lean states it.
Written by an agent, and trusted for nothing: prove.sh checks it against that statement and
audits it.

They rest on `read_ok` (claims/MeetupHeaderClaims.lean): `read_checked` ends with no memory error,
keeps the invariant, and leaves what was there or a head of the datagram it was handed. What a
`PROVE` asks of the head's numbers then follows from the invariant, which is comparisons.
-/

namespace MeetupHeaderProof
namespace Claims

open MeetupHeader in
/-- Everything owed. -/
theorem owed : MeetupHeaderProof.Owed where
  whatever_is_received_is_one_of_the_five_messages_at_its_length_or_is_not_read := by
    simp [MeetupHeader.new, MeetupHeader.Inv, MeetupHeader.kind_checked, MeetupHeader.end_checked, MeetupHeader.whole_checked,
      MeetupHeader.sealed_from_checked]
  whatever_is_received_is_one_of_the_five_messages_at_its_length_or_is_not_read_loop1 := by
    intro bytes me hinv
    intros
    obtain ⟨me', r, hr, hinv', _⟩ := MeetupHeader.Claims.read_ok me bytes hinv
    refine ⟨me', r, hr, ?_⟩
    simp_all [MeetupHeader.Inv, MeetupHeader.kind_checked, MeetupHeader.end_checked, MeetupHeader.whole_checked,
      MeetupHeader.sealed_from_checked]
    bv_omega
  a_head_that_is_read_is_of_the_datagram_it_was_handed_loop1 := by
    intro bytes
    have hnew : MeetupHeader.Inv { kind := 0#32, «end» := 0#32, whole := 0#64, sealed_from := 0#64 } := by simp [MeetupHeader.Inv]
    obtain ⟨me', r, hr, _, hof⟩ := MeetupHeader.Claims.read_ok _ bytes hnew
    refine ⟨{ kind := 0#32, «end» := 0#32, whole := 0#64, sealed_from := 0#64 }, ?_, me', r, hr, ?_⟩
    · first | rfl | simp [MeetupHeader.new, MeetupHeader.raw]
    · rcases hof with h | h <;> simp_all [MeetupHeader.kind_checked, MeetupHeader.whole_checked]

end Claims
end MeetupHeaderProof
