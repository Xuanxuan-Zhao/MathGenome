import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.StrongConvexityBounds
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.DifferentiabilityMonotonicity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
universe u
namespace VariationalNotes.Existence

theorem strongConvexity_support : Specs.strongConvexity_support.{u} := by
  intro E _ _ _ J μ _ hJ hconv x y
  let g : E → ℝ := fun z => J z - μ * ‖z‖ ^ 2 / 2
  let D : E → E →L[ℝ] ℝ := fun z =>
    fderiv ℝ J z - (μ / 2) • (2 • innerSL ℝ z)
  -- Differentiate the objective after subtracting the quadratic.
  have hd : ∀ z ∈ (univ : Set E), HasFDerivAt g (D z) z := by
    intro z _
    have hq := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (μ / 2)
    convert (hJ z).hasFDerivAt.sub hq using 1
    ext w
    dsimp [g, D]
    ring
  -- Apply the ordinary supporting inequality to this convex function.
  have hs := (ConvexAnalysis.convexOn_iff_derivative_supports univ g D
    isOpen_univ convex_univ hd).mp hconv x (mem_univ x) y (mem_univ y)
  have hD : D x (y - x) =
      inner ℝ (gradient J x) (y - x) - μ * inner ℝ x (y - x) := by
    simp [D, inner_gradient_left]
    ring
  rw [hD] at hs
  dsimp [g] at hs
  simp only [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq] at hs ⊢
  rw [real_inner_comm x y]
  nlinarith

theorem strongConvexity_bounds : Specs.strongConvexity_bounds.{u} := by
  intro E _ _ _ J μ hμ hJ hconv xstar hmin x
  have hs := strongConvexity_support J μ hμ hJ hconv
  constructor
  · have hzero : fderiv ℝ J xstar = 0 :=
      (show IsLocalMin J xstar from Eventually.of_forall hmin).hasFDerivAt_eq_zero
        (hJ xstar).hasFDerivAt
    have h := hs xstar x
    rw [inner_gradient_left, hzero, zero_apply] at h
    linarith
  · have h := hs x xstar
    have hcs := real_inner_le_norm (gradient J x) (x - xstar)
    have hi : inner ℝ (gradient J x) (xstar - x) =
        - inner ℝ (gradient J x) (x - xstar) := by
      rw [← inner_neg_right, neg_sub]
    rw [hi, norm_sub_rev xstar x] at h
    apply (le_div_iff₀ (show 0 < 2 * μ by positivity)).mpr
    -- Completing the scalar square preserves the exact constant 1 / (2μ).
    nlinarith [sq_nonneg (μ * ‖x - xstar‖ - ‖gradient J x‖)]

end VariationalNotes.Existence
