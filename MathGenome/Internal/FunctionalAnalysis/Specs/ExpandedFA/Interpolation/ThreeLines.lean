import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Independent statement of the three-lines lemma, paper.tex:18085.
The bounds are arbitrary real numbers: their nonnegativity follows from the
boundary inequalities, and neither is required to be strictly positive.
-/

namespace Specs.ExpandedFA.Interpolation

/-- The full scalar three-lines estimate on the unit strip. -/
def ThreeLines : Prop :=
  ∀ (F : ℂ → ℂ) (M₀ M₁ θ : ℝ),
    (∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖F z‖ ≤ C) →
    ContinuousOn F {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} →
    DifferentiableOn ℂ F {z : ℂ | 0 < z.re ∧ z.re < 1} →
    (∀ t : ℝ, ‖F ((t : ℂ) * Complex.I)‖ ≤ M₀) →
    (∀ t : ℝ, ‖F (1 + (t : ℂ) * Complex.I)‖ ≤ M₁) →
    0 < θ → θ < 1 →
    ‖F (θ : ℂ)‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ

end Specs.ExpandedFA.Interpolation
