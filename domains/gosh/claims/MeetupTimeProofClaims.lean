import MeetupTimeProofOwed
import MeetupTimeClaims

/-!
Proofs of what proofs/MeetupTime.proof.cpp claims, as gen/MeetupTimeProofOwed.lean states it.
Written by an agent, and trusted for nothing: prove.sh checks it against that statement and
audits it.

They rest on `read_ok` (claims/MeetupTimeClaims.lean): `read_checked` ends with no memory error,
and keeps the invariant. What a `PROVE` asks of the counter is the invariant itself.
-/

namespace MeetupTimeProof
namespace Claims

open MeetupTime in
/-- Everything owed. -/
theorem owed : MeetupTimeProof.Owed where
  whatever_is_opened_answers_a_counter_there_can_be := by
    simp [MeetupTime.new, MeetupTime.Inv, MeetupTime.answering_checked]
  whatever_is_opened_answers_a_counter_there_can_be_loop1 := by
    intro bytes me hinv
    intros
    obtain ⟨me', r, hr, hinv'⟩ := MeetupTime.Claims.read_ok me bytes hinv
    refine ⟨me', r, hr, ?_⟩
    simp_all [MeetupTime.answering_checked, MeetupTime.Inv]

end Claims
end MeetupTimeProof
