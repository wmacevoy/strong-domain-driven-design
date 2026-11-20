import MeetupRegisterProofOwed
import MeetupRegisterClaims

/-!
Proofs of what proofs/MeetupRegister.proof.cpp claims, as gen/MeetupRegisterProofOwed.lean states it.
Written by an agent, and trusted for nothing: prove.sh checks it against that statement and
audits it.

They rest on `read_ok` (claims/MeetupRegisterClaims.lean): `read_checked` ends with no memory error,
keeps the invariant, and leaves what was there or a family read from a text of 27 bytes. What a
`PROVE` asks of the family then follows from the invariant.
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
    obtain ⟨me', r, hr, hinv', _⟩ := MeetupRegister.Claims.read_ok me bytes hinv
    refine ⟨me', r, hr, ?_⟩
    simp [MeetupRegister.family_checked, hinv', fam _ hinv']
  a_register_that_is_read_is_of_a_text_of_27_bytes_loop1 := by
    intro bytes
    have hnew : MeetupRegister.Inv { family := 0#32, time := 0#64 } := by simp [MeetupRegister.Inv]
    obtain ⟨me', r, hr, _, hof⟩ := MeetupRegister.Claims.read_ok _ bytes hnew
    refine ⟨{ family := 0#32, time := 0#64 }, ?_, me', r, hr, ?_⟩
    · first | rfl | simp [MeetupRegister.new, MeetupRegister.raw]
    · rcases hof with h | h <;> simp_all [MeetupRegister.family_checked]

end Claims
end MeetupRegisterProof
