import StunAnswerProofOwed
import StunAnswerClaims

/-!
Proofs of what proofs/StunAnswer.proof.cpp claims, as gen/StunAnswerProofOwed.lean states it.
Written by an agent, and trusted for nothing: prove.sh checks it against that statement and
audits it.

Nothing new is worked out here. What the proof file says of every datagram is what was already
owed and proved of `parse_checked` (it ends, with no memory error, and leaves the invariant:
claims/StunAnswerClaims.lean), and the invariant itself says the family is 0, 4 or 6.
-/

namespace StunAnswerProof
namespace Claims

/-- What `kept_family_checked` gives, of anything that keeps the invariant: 0, 4 or 6. -/
theorem family (me : StunAnswer) (h : StunAnswer.Inv me) :
    ∃ r1 r2 r3, StunAnswer.kept_family_checked me = some (me, r1) ∧ StunAnswer.kept_family_checked me = some (me, r2)
      ∧ StunAnswer.kept_family_checked me = some (me, r3) ∧ (((r1 = 0#32) ∨ (r2 = 4#32)) ∨ (r3 = 6#32)) :=
  ⟨me.family, me.family, me.family, by simp [StunAnswer.kept_family_checked], by simp [StunAnswer.kept_family_checked],
    by simp [StunAnswer.kept_family_checked], h.1⟩

/-- Everything owed. -/
theorem owed : StunAnswerProof.Owed where
  whatever_is_received_is_read_safely_and_what_is_kept_is_an_address := by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp StunAnswer.Claims.owed.new_safe
    have hi := StunAnswer.Claims.owed.new_inv a ha
    exact ⟨a, ha, ⟨hi, hi, family a hi⟩, fun _ _ _ _ => trivial⟩
  whatever_is_received_is_read_safely_and_what_is_kept_is_an_address_loop1 := by
    intro bytes me hinv _ _
    obtain ⟨fuel, me', r, h, hinv'⟩ := StunAnswer.Claims.owed.parse_checked_ends me bytes hinv
    exact ⟨fuel, me', r, h, hinv', family me' hinv', hinv', hinv', family me' hinv'⟩

end Claims
end StunAnswerProof
