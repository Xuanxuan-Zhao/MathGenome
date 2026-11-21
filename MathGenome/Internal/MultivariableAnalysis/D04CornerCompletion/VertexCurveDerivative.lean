import MathGenome.Internal.MultivariableAnalysis.D04CornerCompletion.BoxGeometry
import MathGenome.Internal.MultivariableAnalysis.Specs.D04CornerCompletion.VertexCurveDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Filter Topology
open Specs.D04.C01.EuclideanInterfaces.Model

namespace D04CornerCompletion

/-- A two-sided differentiable curve in a box has zero velocity at a vertex. -/
theorem vertex_curve_derivative_zero
    {n : ℕ} (_hn : 2 ≤ n) (a b : E n)
    (_hab : ∀ i : Fin n, a i < b i) (v : E n)
    (hv : IsBoxVertex a b v) (γ : ℝ → E n) (z : E n)
    (hγ : HasDerivAt γ z (0 : ℝ)) (hγ0 : γ 0 = v)
    (hbox : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ box a b) : z = 0 := by
  ext i
  change z i = 0
  have hi : HasDerivAt (fun t : ℝ => γ t i) (z i) 0 := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt 0 hγ
  rcases hv i with hlow | hupp
  · have hmin : IsLocalMin (fun t : ℝ => γ t i) 0 := by
      filter_upwards [hbox] with t ht
      change γ 0 i ≤ γ t i
      rw [hγ0, hlow]
      exact (ht i).1
    exact hmin.hasDerivAt_eq_zero hi
  · have hmax : IsLocalMax (fun t : ℝ => γ t i) 0 := by
      filter_upwards [hbox] with t ht
      change γ t i ≤ γ 0 i
      rw [hγ0, hupp]
      exact (ht i).2
    exact hmax.hasDerivAt_eq_zero hi

end D04CornerCompletion
