import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! K03.15.c1_variation, paper.tex:3654–3666.
`g` is the continuous derivative extension on the closed interval. Derivatives
within that interval give the usual derivative in its interior and the available
one-sided derivative at either endpoint. On a singleton this imposes no extra
condition. The normed real vector space statement includes both ℝ and ℂ, always
with real increments. The integral is the project's proper Darboux integral;
its existence is part of the conclusion. -/
namespace Specs.SingleVariableAnalysis.Ch15.C1Variation
open Specs.SingleVariableAnalysis.Ch08

universe u

def c1Variation : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) (a b : ℝ), a ≤ b →
    (∀ x ∈ Set.Icc a b, HasDerivWithinAt f (g x) (Set.Icc a b) x) →
    ContinuousOn g (Set.Icc a b) →
    ∃ hn : Integral.realIntegrableValue (fun x => ‖g x‖) a b,
      Variation.totalVariationValue f a b =
        ENNReal.ofReal (Integral.realIntegralValue (fun x => ‖g x‖) hn)

end Specs.SingleVariableAnalysis.Ch15.C1Variation
