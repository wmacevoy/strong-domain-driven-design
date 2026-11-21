import MeetupTimeProofOwed
import MeetupTimeClaims

/-!
Proofs of what proofs/MeetupTime.proof.cpp claims, as gen/MeetupTimeProofOwed.lean states it.
Written by an agent, and trusted for nothing: prove.sh checks it against that statement and
audits it.

They rest on `read_ok` (claims/MeetupTimeClaims.lean): `read_checked` ends with no memory error,
keeps the invariant, and leaves what was there or what it read from a text of 16 bytes. What a
`PROVE` asks of the counter is the invariant itself.
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
    obtain ⟨me', r, hr, hinv', _⟩ := MeetupTime.Claims.read_ok me bytes hinv
    refine ⟨me', r, hr, ?_⟩
    simp_all [MeetupTime.answering_checked, MeetupTime.Inv]
  a_time_that_is_read_is_of_a_text_of_16_bytes_loop1 := by
    intro bytes
    have hnew : MeetupTime.Inv { answering := 0#64, time := 0#64 } := by simp [MeetupTime.Inv]
    obtain ⟨me', r, hr, _, hof⟩ := MeetupTime.Claims.read_ok _ bytes hnew
    refine ⟨{ answering := 0#64, time := 0#64 }, ?_, me', r, hr, ?_⟩
    · first | rfl | simp [MeetupTime.new, MeetupTime.raw]
    · rcases hof with h | h <;> simp_all [MeetupTime.answering_checked, MeetupTime.time_checked]

end Claims
end MeetupTimeProof
