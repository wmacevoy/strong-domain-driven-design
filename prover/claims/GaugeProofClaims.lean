import GaugeProofOwed

/-!
Proofs of what proofs/Gauge.proof.cpp claims, as gen/GaugeProofOwed.lean states it. Written by an
agent, and trusted for nothing: prove.sh checks it against that statement and audits it.

Each is the same few steps: open the methods (they are a few lines each), let `simp` run them, and
leave what is left, comparisons of 32-bit numbers, to `bv_omega`.
-/

namespace GaugeProof
namespace Claims

macro "run_gauge" : tactic =>
  `(tactic| (intros
             simp_all [Gauge.new, Gauge.raw, Gauge.get, Gauge.getLimit, Gauge.set, Gauge.setLimit, Gauge.Inv]
             all_goals (repeat' split)
             all_goals simp_all
             all_goals (try bv_omega)
             all_goals (repeat' split)
             all_goals (try simp_all)
             all_goals (try bv_omega)))

/-- Everything owed. -/
theorem owed : GaugeProof.Owed where
  a_gauge_is_never_above_its_limit := by run_gauge
  a_gauge_is_never_above_its_limit_loop2 := by run_gauge
  a_gauge_is_never_above_its_limit_loop1 := by run_gauge
  lowering_the_limit_brings_the_level_down_with_it_loop3 := by run_gauge

end Claims
end GaugeProof
