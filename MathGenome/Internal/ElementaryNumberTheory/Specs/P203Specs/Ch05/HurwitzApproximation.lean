import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.FareyMediants
import Mathlib.NumberTheory.Real.Irrational

/-! Independent specification of the existence assertion of Hurwitz's theorem,
`paper.tex`, lines 2344–2383. The separate optimality assertion is allocated to
E07_HurwitzOptimality. Integer denominators are positive and pairs are reduced
in the canonical upstream sense. Infinitude is of distinct reduced pairs. -/
namespace P203Specs.Ch05

def HurwitzApproximation : Prop :=
  ∀ x : ℝ, Irrational x →
    {v : Fraction | Reduced v ∧
      |x - (v.1 : ℝ) / (v.2 : ℝ)| <
        1 / (Real.sqrt 5 * (v.2 : ℝ) ^ 2)}.Infinite

end P203Specs.Ch05
