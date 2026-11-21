import MathGenome.Internal.MultivariableAnalysis.Specs.D04CornerCompletion.BoxGeometry

/-! Independent proposition for the two-sided curve obstruction at a box vertex. -/

open Filter Topology
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04CornerCompletion.BoxGeometry.Model

namespace Specs.D04CornerCompletion.VertexCurveDerivative

/-- The derivative of a curve locally contained in a box at a vertex is zero.
Containment is in a full real neighborhood of zero. -/
def vertex_curve_derivative_zeroType : Prop :=
  ∀ {n : ℕ} (_hn : 2 ≤ n) (a b : E n)
    (_hab : ∀ i : Fin n, a i < b i) (v : E n)
    (_hv : IsBoxVertex a b v) (γ : ℝ → E n) (z : E n),
    HasDerivAt γ z (0 : ℝ) → γ 0 = v →
    (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ box a b) → z = 0

end Specs.D04CornerCompletion.VertexCurveDerivative
