import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Logic.Function.Iterate

/-! Independent specification of paper.tex, Corollary p206:W67. -/

open Filter
open scoped Topology

universe u

namespace Specs.NumAnalysis206.Iterations

/-- A contraction on a nonempty closed invariant domain has a unique fixed
point within that domain. Every ambient orbit starting there stays there and
converges to this point. No condition on `T` outside `D` is imposed. -/
def ClosedDomainStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompleteSpace X]
    (D : Set X) (T : X → X) (q : ℝ),
    D.Nonempty → IsClosed D → Set.MapsTo T D D →
    0 ≤ q → q < 1 →
    (∀ x ∈ D, ∀ y ∈ D, dist (T x) (T y) ≤ q * dist x y) →
    ∃ p : X, p ∈ D ∧ T p = p ∧
      (∀ p' : X, p' ∈ D → T p' = p' → p' = p) ∧
      ∀ x₀ : X, x₀ ∈ D →
        (∀ n : ℕ, T^[n] x₀ ∈ D) ∧
        Tendsto (fun n : ℕ => T^[n] x₀) atTop (𝓝 p)

end Specs.NumAnalysis206.Iterations
