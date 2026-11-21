import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions
import Mathlib.Analysis.Convex.Function

/-! The Slater clause of `fa2:p2:subgradient-slater`, paper.tex:8159–8169.
A finite function is represented by `φ : X → ℝ`; its subdifferential is
that of its canonical inclusion in the shared `WithTop ℝ` value space.
There is no completeness, differentiability, or nonzero-normal assumption.
The growth clause is covered by the upstream `GlobalGrowth` specifications. -/
namespace ExpandedFA.BanachConvex.SlaterSpec

universe u

/-- The exact normal cone, with complementary slackness at every feasible
point, including inactive constraints and the zero normal. -/
def SlaterNormalCone : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : X → ℝ), Continuous φ → ConvexOn ℝ Set.univ φ →
    (∃ z, φ z < 0) → ∀ x, φ x ≤ 0 →
    Spec.NormalConeValue X {y | φ y ≤ 0} x =
      {g | ∃ (f : X →L[ℝ] ℝ) (μ : ℝ),
        f ∈ Spec.SubdifferentialValue X (fun y => (φ y : WithTop ℝ)) x ∧
        0 ≤ μ ∧ μ * φ x = 0 ∧ g = μ • f}

/-- At a strictly feasible point the normal cone is precisely {0}. -/
def StrictSublevelNormalCone : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : X → ℝ), Continuous φ → ConvexOn ℝ Set.univ φ →
    ∀ x, φ x < 0 → Spec.NormalConeValue X {y | φ y ≤ 0} x = {0}

end ExpandedFA.BanachConvex.SlaterSpec
