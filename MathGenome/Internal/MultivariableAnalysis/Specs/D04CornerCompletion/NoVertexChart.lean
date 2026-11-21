import MathGenome.Internal.MultivariableAnalysis.Specs.D04CornerCompletion.BoxGeometry

/-! Independent full proposition for the box-vertex chart obstruction. -/

open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04CornerCompletion.BoxGeometry.Model
open scoped ContDiff

namespace Specs.D04CornerCompletion.NoVertexChart

/-- Neither an interior-model chart nor a centered half-space chart can map its
center to a vertex of a nondegenerate box in dimension at least two. -/
def no_centered_vertex_chartType : Prop :=
  ∀ {n : ℕ} (_hn : 2 ≤ n) (a b : E n)
    (_hab : ∀ i : Fin n, a i < b i) (v : E n)
    (_hv : IsBoxVertex a b v),
    ¬ ∃ (c : EmbeddedChart (1 : ℕ∞ω) n n (box a b)) (u : E n),
      CenteredAt c u ∧ c.toFun u = v

end Specs.D04CornerCompletion.NoVertexChart
