import Mathlib.Topology.MetricSpace.Contracting

open scoped Topology

namespace Specs.VariationalNotes.FixedPoints

universe u

/-- Proposition 10.4.1: existence and uniqueness of a fixed point, convergence
from every starting point, and the a priori error estimate. The indices include
zero and the contraction constant is allowed to be zero. -/
def BanachContraction : Prop :=
  ∀ (M : Type u) [MetricSpace M] [Nonempty M] [CompleteSpace M]
    (q : ℝ) (T : M → M),
    0 ≤ q → q < 1 →
    (∀ x y : M, dist (T x) (T y) ≤ q * dist x y) →
    ∃ xstar : M,
      T xstar = xstar ∧
      (∀ y : M, T y = y → y = xstar) ∧
      ∀ x0 : M,
        Filter.Tendsto (fun n : ℕ => (T^[n]) x0) Filter.atTop (𝓝 xstar) ∧
        ∀ n : ℕ, dist ((T^[n]) x0) xstar ≤
          q ^ n * dist x0 (T x0) / (1 - q)

end Specs.VariationalNotes.FixedPoints
