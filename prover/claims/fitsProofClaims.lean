import fitsProofOwed

/-! The proofs of what proofs/fits.proof.cpp claims, as gen/fitsProofOwed.lean states it. Trusted
for nothing: checked against that statement and audited. -/

namespace fitsProof
namespace Claims

/-- Everything owed. -/
theorem owed : fitsProof.Owed where
  what_fits_is_at_most_the_room_and_what_there_is_loop2 := by
    intro n room
    simp only [fits.call, fits.raw]
    by_cases h : n > room <;> simp [h] <;> bv_omega

end Claims
end fitsProof
