import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.SmoothConstraintModels
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent statement of paper.tex, Theorem `thm:constrained-growth`.
The functions are ambient representatives of data on the open domain `U`.
`ContDiffAt ℝ 2` expresses C² regularity on a neighborhood of the feasible
point; no regularity away from that neighborhood is required. All finite
constraint index types, and the ambient dimension, may be empty/zero. -/
noncomputable section
universe u v w
namespace VariationalNotes.Ch06.Specs

/-- One fixed KKT pair, positive Hessian on its nonzero critical directions,
gives quadratic growth and strict relative local minimality. The Hessian
is the actual derivative of the derivative of the shared Lagrangian. -/
def constrainedQuadraticGrowth : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {I : Type v} {J : Type w}
    [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ)
    (a : X) (lam : I → ℝ) (nu : J → ℝ),
    IsOpen U → ContDiffAt ℝ 2 f a →
    (∀ i, ContDiffAt ℝ 2 (g i) a) →
    (∀ j, ContDiffAt ℝ 2 (h j) a) →
    KKT U f g h a lam nu →
    (∀ d ∈ criticalCone f g h a, d ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (lagrangian f g h lam nu)) a d d) →
    (∃ c > 0, ∃ ρ > 0, ∀ x ∈ feasibleSet U g h,
      ‖x - a‖ < ρ → f a + c * ‖x - a‖ ^ 2 ≤ f x) ∧
    (∃ ρ > 0, ∀ x ∈ feasibleSet U g h,
      ‖x - a‖ < ρ → x ≠ a → f a < f x)

end VariationalNotes.Ch06.Specs
