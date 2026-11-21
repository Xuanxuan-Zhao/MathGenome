import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.NormSquareConjugate
import Mathlib.Analysis.Convex.Function

/-! Asplund's conditional combination theorem, paper.tex:7012–7022.
All norms are on the original real vector space. Quantitative equivalence to
its reference norm ensures that their continuous linear dual is the common one.
There is no completeness, reflexivity, or nontriviality hypothesis. -/
namespace ExpandedFA.Asplund.SimultaneousRenorming

/-- The unit-sphere midpoint definition, for a specified norm function. -/
def SphereStrictConvex {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : V → ℝ) : Prop :=
  ∀ x y : V, p x = 1 → p y = 1 → x ≠ y →
    p ((1 / 2 : ℝ) • (x + y)) < 1

namespace Spec

/-- Both the output norm and its actual supremum-defined dual norm are rotund.
The initial norms are equivalent to the common reference norm topology. -/
def SimultaneousRenorming : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p₁ p₂ : E → ℝ),
    NormSquareConjugate.EquivalentNorm p₁ →
    NormSquareConjugate.EquivalentNorm p₂ →
    SphereStrictConvex p₁ →
    SphereStrictConvex (NormSquareConjugate.dualNorm p₂) →
    ∃ p : E → ℝ, NormSquareConjugate.EquivalentNorm p ∧
      SphereStrictConvex p ∧ SphereStrictConvex (NormSquareConjugate.dualNorm p)

end Spec
end ExpandedFA.Asplund.SimultaneousRenorming
