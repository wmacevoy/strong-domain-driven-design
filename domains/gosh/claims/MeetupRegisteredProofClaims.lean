import MeetupRegisteredProofOwed
import MeetupRegisteredClaims

/-!
Proofs of what proofs/MeetupRegistered.proof.cpp claims, as gen/MeetupRegisteredProofOwed.lean states
it. Written by an agent, and trusted for nothing: prove.sh checks it against that statement and
audits it.

They rest on `read_ok` (claims/MeetupRegisteredClaims.lean): `read_checked` ends with no memory error,
and keeps the invariant. What a `PROVE` asks of the family is the invariant itself.
-/

namespace MeetupRegisteredProof
namespace Claims

open MeetupRegistered in
/-- Everything owed. -/
theorem owed : MeetupRegisteredProof.Owed where
  whatever_is_opened_says_a_family_there_is_or_is_not_read := by
    simp [MeetupRegistered.new, MeetupRegistered.Inv, MeetupRegistered.family_checked]
  whatever_is_opened_says_a_family_there_is_or_is_not_read_loop1 := by
    intro bytes me hinv
    intros
    obtain ⟨me', r, hr, hinv'⟩ := MeetupRegistered.Claims.read_ok me bytes hinv
    refine ⟨me', r, hr, ?_⟩
    simp_all [MeetupRegistered.family_checked, MeetupRegistered.Inv]

end Claims
end MeetupRegisteredProof
