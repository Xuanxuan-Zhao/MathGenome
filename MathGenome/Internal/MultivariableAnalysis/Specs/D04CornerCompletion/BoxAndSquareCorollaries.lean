import MathGenome.Internal.MultivariableAnalysis.Specs.D04CornerCompletion.BoxGeometry

/-! Independent propositions for the box and square corollaries. -/

open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04CornerCompletion.BoxGeometry.Model
open scoped ContDiff

namespace Specs.D04CornerCompletion.BoxAndSquareCorollaries

/-- A nondegenerate box in dimension at least two is not an embedded C¹
manifold with smooth boundary in the original ambient-compatible sense. -/
def box_not_isEmbeddedManifoldType : Prop :=
  ∀ {n : ℕ} (_hn : 2 ≤ n) (a b : E n)
    (_hab : ∀ i : Fin n, a i < b i),
    ¬ IsEmbeddedManifold (1 : ℕ∞ω) n (box a b)

/-- The actual coordinatewise unit square has no centered embedded C¹ chart
at its coordinatewise zero vector. -/
def square_no_centered_origin_chartType : Prop :=
  ¬ ∃ (c : EmbeddedChart (1 : ℕ∞ω) 2 2
      {x : E 2 | ∀ i : Fin 2, (0 : ℝ) ≤ x i ∧ x i ≤ 1}) (u : E 2),
    CenteredAt c u ∧ c.toFun u = (0 : E 2)

/-- The coordinatewise unit square is not an embedded C¹ two-manifold with
smooth boundary in its original Euclidean ambient space. -/
def square_not_isEmbeddedManifoldType : Prop :=
  ¬ IsEmbeddedManifold (1 : ℕ∞ω) 2
    {x : E 2 | ∀ i : Fin 2, (0 : ℝ) ≤ x i ∧ x i ≤ 1}

end Specs.D04CornerCompletion.BoxAndSquareCorollaries
