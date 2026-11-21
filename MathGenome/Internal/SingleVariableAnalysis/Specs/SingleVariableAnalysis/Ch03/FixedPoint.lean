import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Logic.Function.Iterate

/-!
Independent specification of K03.03.fixed_point (paper.tex:617–632).

`X` is any nonempty complete metric space, not necessarily a scalar space.
The contraction constant is the real number of the source, with `0 ≤ q < 1`.
`T^[n] x₀` denotes the canonical orbit: its zeroth term is `x₀` and its
successor is `T (T^[n] x₀)`. The fixed point is independent of the starting
point. Uniqueness is among all fixed points, without extra orbit properties.
All bounds quantify over `n : ℕ`, so include `n = 0` and the usual `q^0 = 1`
even for `q = 0`. The second statement also covers any sequence presented
by the recurrence rather than by the canonical iterate notation.
-/
namespace Specs.SingleVariableAnalysis.Ch03.FixedPoint

open scoped Topology
universe u

def contractionPrinciple : Prop :=
  ∀ {X : Type u} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (T : X → X) (q : ℝ),
    0 ≤ q → q < 1 → (∀ x y, dist (T x) (T y) ≤ q * dist x y) →
    ∃ p : X, T p = p ∧ (∀ r : X, T r = r → r = p) ∧
      ∀ x₀ : X,
        Filter.Tendsto (fun n : ℕ => T^[n] x₀) Filter.atTop (𝓝 p) ∧
        ∀ n : ℕ,
          dist (T^[n] x₀) p ≤ q ^ n / (1 - q) * dist (T x₀) x₀ ∧
          dist (T^[n] x₀) p ≤ dist (T^[n + 1] x₀) (T^[n] x₀) / (1 - q)

def contractionOrbit : Prop :=
  ∀ {X : Type u} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (T : X → X) (q : ℝ),
    0 ≤ q → q < 1 → (∀ x y, dist (T x) (T y) ≤ q * dist x y) →
    ∃ p : X, T p = p ∧ (∀ r : X, T r = r → r = p) ∧
      ∀ x : ℕ → X, (∀ n, x (n + 1) = T (x n)) →
        Filter.Tendsto x Filter.atTop (𝓝 p) ∧
        ∀ n : ℕ,
          dist (x n) p ≤ q ^ n / (1 - q) * dist (x 1) (x 0) ∧
          dist (x n) p ≤ dist (x (n + 1)) (x n) / (1 - q)

end Specs.SingleVariableAnalysis.Ch03.FixedPoint
