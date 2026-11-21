import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Independent statements for the factorial-series part of paper.tex,
D12.19.07, lines 3270–3275 and 3288–3302. Index n : ℕ represents the
source index n+1, so the first terms are z, z², z⁶, … . -/
noncomputable section
open Set Metric Filter
open scoped Topology

namespace Specs.D12Complex.Ch19.FactorialNaturalBoundary
open _root_.D12Complex

def series_type := ℂ → ℂ
def series_value : series_type := fun z => ∑' n : ℕ, z ^ (n+1).factorial

/-- An explicit summable geometric majorant on every compact subdisk.
This is normal (absolute uniform) convergence, including the zero-radius disk. -/
def normal_convergence_type : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 →
    Summable (fun n : ℕ => r^n) ∧
    (∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) r, ‖z^(n+1).factorial‖ ≤ r^n) ∧
    TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, z^(n+1).factorial)
      series_value atTop (closedBall (0 : ℂ) r)

def holomorphic_type : Prop := HolomorphicOn (ball (0 : ℂ) 1) series_value

/-- In fact the modulus tends to infinity along each root-of-unity radius. -/
def radial_unbounded_type : Prop :=
  ∀ ξ : ℂ, (∃ q : ℕ, 0 < q ∧ ξ^q = 1) →
    Tendsto (fun r : ℝ => ‖series_value ((r : ℂ)*ξ)‖) (𝓝[<] (1 : ℝ)) atTop

/-- Failure of extension across every point of the unit circle. The agreement
is on the entire overlap, with no extra connectedness or regularity premise. -/
def natural_boundary_type : Prop :=
  ∀ ξ : ℂ, ‖ξ‖ = 1 →
    ¬ ∃ (U : Set ℂ) (g : ℂ → ℂ), IsOpen U ∧ ξ ∈ U ∧
      HolomorphicOn U g ∧ EqOn g series_value (U ∩ ball (0 : ℂ) 1)

end Specs.D12Complex.Ch19.FactorialNaturalBoundary
