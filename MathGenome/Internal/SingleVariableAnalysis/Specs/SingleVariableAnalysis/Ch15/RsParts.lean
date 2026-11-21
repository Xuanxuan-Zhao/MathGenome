import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsSums
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent specification of K03.15.rs_parts, paper.tex:3737–3750.
Both functions retain their actual values on the closed interval. The two
integrals are the upstream bounded refinement integrals, with arbitrary tags
in closed partition cells. The singleton interval is included. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsParts

/-- Existence of both integrals and their integration by parts identity. -/
def integrationByParts : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ (f α : ℝ → ℝ),
    ContinuousOn f (Set.Icc a b) →
    ContinuousOn α (Set.Icc a b) →
    Variation.boundedVariationValue f a b →
    Variation.boundedVariationValue α a b →
    ∃ I J : ℝ,
      RsSums.integralValue a b f α I ∧
      RsSums.integralValue a b α f J ∧
      I + J = f b * α b - f a * α a

end Specs.SingleVariableAnalysis.Ch15.RsParts
