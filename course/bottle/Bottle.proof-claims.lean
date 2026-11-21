import BottleProofOwed

/-!
Lesson 5: the proofs of what Bottle.proof.cpp claims, as gen/BottleProofOwed.lean states it.
Trusted for nothing: checked against that statement and audited. Each is the same few steps:
run the methods (`simp_all`), take each branch (`split`), and leave the comparisons to `bv_omega`.
-/

namespace BottleProof
namespace Claims

macro "run_bottle" : tactic =>
  `(tactic| (intros
             simp_all [Bottle.new, Bottle.raw, Bottle.getVolume, Bottle.getMaxVolume, Bottle.setVolume, Bottle.setMaxVolume, Bottle.Inv]
             all_goals (repeat' split)
             all_goals simp_all
             all_goals (try bv_omega)
             all_goals (repeat' split)
             all_goals (try simp_all)
             all_goals (try bv_omega)))

/-- Everything owed. -/
theorem owed : BottleProof.Owed where
  a_bottle_never_holds_more_than_its_size := by run_bottle
  a_bottle_never_holds_more_than_its_size_loop2 := by run_bottle
  a_bottle_never_holds_more_than_its_size_loop1 := by run_bottle
  a_smaller_bottle_spills_what_no_longer_fits_loop3 := by run_bottle

end Claims
end BottleProof
