import JarProofOwed

/-! The proofs of what proofs/Jar.proof.cpp claims of the set {Jar, fits}, as gen/JarProofOwed.lean
states it. Trusted for nothing: checked against that statement and audited. -/

namespace JarProof
namespace Claims

/-- Everything owed. -/
theorem owed : JarProof.Owed where
  what_fits_is_what_a_jar_takes_loop1 := by
    intro n
    simp only [Jar.new, Jar.add, Jar.count, fits.call, fits.raw]
    by_cases h : 100#32 < n
    · simp [h]
    · simp [h]

end Claims
end JarProof
