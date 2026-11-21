import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent statement of paper.tex, Theorem `thm:pde-cea`.
The bilinear form is initially algebraic; its boundedness is an explicit hypothesis.
`Metric.infDist` is the infimum of `‖u - v‖` over the (nonempty) trial subspace.
No symmetry, nonzero dimension, or sign assumption on M is imposed. -/
namespace P201Specs.Common
open scoped Topology
universe u

def CoerciveGalerkin : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (M α : ℝ) (ℓ : V →L[ℝ] ℝ),
    (∀ x y, |a x y| ≤ M * ‖x‖ * ‖y‖) →
    0 < α → (∀ x, α * ‖x‖ ^ 2 ≤ a x x) →
    ∀ (W : ℕ → Submodule ℝ V),
    (∀ m, FiniteDimensional ℝ (W m)) → Monotone W →
    Dense (⋃ m, (W m : Set V)) →
    ∃ (u : V) (uₘ : ∀ m, W m),
      (∀ v, a u v = ℓ v) ∧
      (∀ w, (∀ v, a w v = ℓ v) → w = u) ∧
      (∀ m (v : W m), a (uₘ m : V) (v : V) = ℓ (v : V)) ∧
      (∀ m (w : W m),
        (∀ v : W m, a (w : V) (v : V) = ℓ (v : V)) → w = uₘ m) ∧
      (∀ m, ‖u - (uₘ m : V)‖ ≤ (M / α) * Metric.infDist u (W m : Set V)) ∧
      Filter.Tendsto (fun m => (uₘ m : V)) Filter.atTop (𝓝 u)

end P201Specs.Common
