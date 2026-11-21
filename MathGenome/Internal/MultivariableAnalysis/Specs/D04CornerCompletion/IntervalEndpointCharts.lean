import MathGenome.Internal.MultivariableAnalysis.Specs.D04CornerCompletion.BoxGeometry

/-! Smooth boundary charts at both endpoints of a nondegenerate interval,
in the unchanged Euclidean and embedded-chart models. -/
open scoped ContDiff
namespace Specs.D04CornerCompletion.IntervalEndpointCharts
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04CornerCompletion.BoxGeometry.Model

def interval_endpoint_chartsType : Prop :=
  ∀ (a b : E 1), a (0 : Fin 1) < b (0 : Fin 1) →
    ∀ v : E 1, v = a ∨ v = b →
      ∃ c : EmbeddedChart (∞ : ℕ∞ω) 1 1 (box a b),
        c.half = true ∧ CenteredAt c (0 : E 1) ∧ c.toFun (0 : E 1) = v

end Specs.D04CornerCompletion.IntervalEndpointCharts
