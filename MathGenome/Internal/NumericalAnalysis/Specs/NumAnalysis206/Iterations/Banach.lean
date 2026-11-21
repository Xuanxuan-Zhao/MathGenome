import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Logic.Function.Iterate

/-!
Independent specification of paper.tex, Theorem p206:W66.
The fixed-point uniqueness clause ranges over all fixed points, and convergence
is required for every initial point, including a point already fixed by `T`.
-/

open Filter
open scoped Topology

universe u

namespace Specs.NumAnalysis206.Iterations

/-- Banach's theorem for a real contraction factor, including factor zero. -/
def BanachStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [Nonempty X] [CompleteSpace X]
    (T : X → X) (q : ℝ),
    0 ≤ q → q < 1 →
    (∀ x y : X, dist (T x) (T y) ≤ q * dist x y) →
    ∃ p : X, T p = p ∧
      (∀ p' : X, T p' = p' → p' = p) ∧
      ∀ x₀ : X, Tendsto (fun n : ℕ => T^[n] x₀) atTop (𝓝 p)

end Specs.NumAnalysis206.Iterations
