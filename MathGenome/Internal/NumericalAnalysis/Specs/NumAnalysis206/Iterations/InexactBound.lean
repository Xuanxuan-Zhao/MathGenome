import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Independent statements of the finite bounds in paper.tex, W71.
The ambient space need not be complete: the fixed point and membership of
all computed iterates in the contraction domain are explicit hypotheses. -/

namespace Specs.NumAnalysis206.Iterations

/-- The finite convolution estimate, with an empty sum for `n = 0`.
Natural powers retain the convention `0 ^ 0 = 1`. -/
def InexactConvolutionBound : Prop :=
  ∀ {X : Type*} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (p : X) (x : ℕ → X) (δ : ℕ → ℝ),
    0 ≤ q → q < 1 →
    (∀ z ∈ D, T z ∈ D) →
    (∀ u ∈ D, ∀ v ∈ D, dist (T u) (T v) ≤ q * dist u v) →
    p ∈ D → T p = p → (∀ j, x j ∈ D) →
    (∀ j, dist (x (j + 1)) (T (x j)) ≤ δ j) →
    ∀ n : ℕ, dist (x n) p ≤ q ^ n * dist (x 0) p +
      ∑ j ∈ Finset.range n, q ^ (n - 1 - j) * δ j

/-- The finite geometric bound when all step errors have a common upper bound. -/
def InexactCommonBound : Prop :=
  ∀ {X : Type*} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (p : X) (x : ℕ → X) (δ : ℕ → ℝ) (ε : ℝ),
    0 ≤ q → q < 1 →
    (∀ z ∈ D, T z ∈ D) →
    (∀ u ∈ D, ∀ v ∈ D, dist (T u) (T v) ≤ q * dist u v) →
    p ∈ D → T p = p → (∀ j, x j ∈ D) →
    (∀ j, dist (x (j + 1)) (T (x j)) ≤ δ j) →
    (∀ j, δ j ≤ ε) →
    ∀ n : ℕ, dist (x n) p ≤ q ^ n * dist (x 0) p +
      ε * (1 - q ^ n) / (1 - q)

end Specs.NumAnalysis206.Iterations
