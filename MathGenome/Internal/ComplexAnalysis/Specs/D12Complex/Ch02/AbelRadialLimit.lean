import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic

/-! Independent statements for paper.tex:503–532 (D12.02.06).
The parameter is real and lies in [0,1). Convergence at the boundary is
ordinary series convergence, not absolute convergence. -/

open Filter
open scoped Topology

namespace Specs.D12Complex.Ch02.AbelRadialLimit

/-- Absolute convergence along every interior point of the radius. -/
def absolute_convergence_type : Prop :=
  ∀ (a : ℕ → ℂ) (ζ S : ℂ), ζ ≠ 0 →
    Tendsto (fun N => ∑ n ∈ Finset.range N, a n * ζ ^ n) atTop (𝓝 S) →
    ∀ t : ℝ, 0 ≤ t → t < 1 →
      Summable (fun n => ‖a n * ((t : ℂ) * ζ) ^ n‖)

/-- The one-sided radial limit; no unrestricted complex approach is asserted. -/
def radial_limit_type : Prop :=
  ∀ (a : ℕ → ℂ) (ζ S : ℂ), ζ ≠ 0 →
    Tendsto (fun N => ∑ n ∈ Finset.range N, a n * ζ ^ n) atTop (𝓝 S) →
    Tendsto (fun t : ℝ => ∑' n, a n * ((t : ℂ) * ζ) ^ n)
      (𝓝[Set.Ico 0 1] 1) (𝓝 S)

/-- The geometric series is absolutely convergent in the open unit disk
and has the specified rational sum. -/
def geometric_sum_type : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 →
    Summable (fun n : ℕ => ‖z ^ n‖) ∧ HasSum (fun n : ℕ => z ^ n) (1 / (1 - z))

/-- This is holomorphy of the actual series sum on the open disk. -/
def geometric_holomorphic_type : Prop :=
  _root_.D12Complex.HolomorphicOn (Metric.ball 0 1) (fun z : ℂ => ∑' n : ℕ, z ^ n)

/-- At every unit-circle point the terms fail the necessary test, and the
partial sums have no ordinary finite limit. -/
def geometric_boundary_divergence_type : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    (¬ Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0)) ∧
    (¬ Summable (fun n : ℕ => z ^ n)) ∧
    (¬ ∃ S : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N, z ^ n) atTop (𝓝 S))

/-- Interior holomorphy does not force a finite radial boundary limit at 1. -/
def geometric_no_finite_radial_limit_type : Prop :=
  ¬ ∃ S : ℂ, Tendsto (fun t : ℝ => ∑' n : ℕ, (t : ℂ) ^ n)
    (𝓝[Set.Ico 0 1] 1) (𝓝 S)

end Specs.D12Complex.Ch02.AbelRadialLimit
