import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral

/-! Independent specification of K03.08.criterion, paper.tex:1955–1966.
The sums use suprema and infima on the closed cells of arbitrary finite
strict partitions, with the boundedness hypothesis from the integral interface.
Integrability is the existing Darboux predicate, not measure integrability. -/

namespace Specs.SingleVariableAnalysis.Ch08.Criterion

open _root_.SingleVariableAnalysis.Riemann

/-- A bounded real function on a nondegenerate interval is Darboux integrable
exactly when its upper and lower sums can have arbitrarily small gap. -/
def darbouxCriterion : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ} (_hab : a < b)
    (hf : DarbouxSums.boundedOnIntervalValue f a b),
    Integral.realIntegrableValue f a b ↔
      ∀ ε : ℝ, 0 < ε → ∃ P : PartitionData a b,
        DarbouxSums.upperSumValue f P hf - DarbouxSums.lowerSumValue f P hf < ε

end Specs.SingleVariableAnalysis.Ch08.Criterion
