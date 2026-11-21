import MeetupRegisterProofOwed
import MeetupRegisterClaims

/-!
Proofs of what proofs/MeetupRegister.proof.cpp claims, as gen/MeetupRegisterProofOwed.lean states it.
Written by an agent, and trusted for nothing: prove.sh checks it against that statement and
audits it.

They rest on `read_ok` (claims/MeetupRegisterClaims.lean): `read_checked` ends with no memory error,
and keeps the invariant. What a `PROVE` asks of the family then follows from the invariant.
-/

namespace MeetupRegisterProof
namespace Claims

/-- What the invariant says of the family, as the PROVEs ask it. -/
theorem fam (m : MeetupRegister) (h : MeetupRegister.Inv m) : (m.family = 0#32 ∨ m.family = 4#32) ∨ m.family = 6#32 :=
  Or.elim h (fun h => Or.elim h (fun h => Or.inl (Or.inl h.1)) (fun h => Or.inl (Or.inr h))) (fun h => Or.inr h)

open MeetupRegister in
/-- Everything owed. -/
theorem owed : MeetupRegisterProof.Owed where
  whatever_is_opened_is_a_register_of_a_family_there_is_or_is_not_read := by
    simp [MeetupRegister.new, MeetupRegister.Inv, MeetupRegister.family_checked]
  whatever_is_opened_is_a_register_of_a_family_there_is_or_is_not_read_loop1 := by
    intro bytes me hinv
    intros
    obtain ⟨me', r, hr, hinv'⟩ := MeetupRegister.Claims.read_ok me bytes hinv
    refine ⟨me', r, hr, ?_⟩
    simp [MeetupRegister.family_checked, hinv', fam _ hinv']

end Claims
end MeetupRegisterProof
