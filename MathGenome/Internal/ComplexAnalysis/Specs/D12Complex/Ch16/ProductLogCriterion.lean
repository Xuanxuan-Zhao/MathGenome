import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.PrincipalLogarithm
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Ordered scalar products: no unconditional summability is imposed on the
logarithm series. The index `n` denotes the first `n` factors, starting at zero. -/
noncomputable section
open Filter
open scoped Topology

namespace Specs.D12Complex.Ch16.ProductLogCriterion
open _root_.D12Complex

/-- The sum is an ordered series on a tail, and the full product retains
its finite prefix. Convergence of the factors to one validates the late
principal branch; no extra branch or absolute-convergence hypothesis is imposed. -/
def product_log_criterion_type : Prop :=
  ∀ u : ℕ → ℂ, (∀ n, u n ≠ 0) →
    ((∃ P : ℂ, P ≠ 0 ∧
      Tendsto (fun n => ∏ k ∈ Finset.range n, u k) atTop (𝓝 P)) ↔
    (Tendsto u atTop (𝓝 1) ∧
      ∃ N : ℕ, ∃ S : ℂ, Tendsto
          (fun n => ∑ k ∈ Finset.range n, PrincipalLog (u (k + N))) atTop (𝓝 S)))

def product_nonzero_of_summable_norm_type : Prop :=
  ∀ u : ℕ → ℂ, (∀ n, u n ≠ 0) → Summable (fun n => ‖u n - 1‖) →
    ∃ P : ℂ, P ≠ 0 ∧
      Tendsto (fun n => ∏ k ∈ Finset.range n, u k) atTop (𝓝 P)

end Specs.D12Complex.Ch16.ProductLogCriterion
