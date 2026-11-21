import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.LatticeGeometry
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-! Independent specification of paper.tex:3852–3874 (D12.22.04).
The all-lattice regularized sum includes the zero term, which is exactly 1/z².
The explicit nonzero-index formula is required separately below. Values assigned
at lattice points are irrelevant to the meromorphic germs, which are specified
on punctured neighborhoods. Normal convergence is the compact Weierstrass
majorant condition, hence includes absolute convergence and uniform tails. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch22.WeierstrassSeries

abbrev lattice := Specs.D12Complex.Ch22.LatticeGeometry.lattice

def weierstrassP (ω₁ ω₂ z : ℂ) : ℂ :=
  ∑' l : lattice ω₁ ω₂, (1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)

def weierstrassP_type := ℂ → ℂ → ℂ → ℂ

def series_representation_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ z : ℂ,
    weierstrassP ω₁ ω₂ z = 1 / z ^ 2 +
      ∑' l : {l : lattice ω₁ ω₂ // l ≠ 0},
        (1 / (z - (l.1 : ℂ)) ^ 2 - 1 / (l.1 : ℂ) ^ 2)

def series_locallyUniform_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    HasSumLocallyUniformlyOn
      (fun (l : lattice ω₁ ω₂) (z : ℂ) =>
        1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)
      (weierstrassP ω₁ ω₂) (lattice ω₁ ω₂ : Set ℂ)ᶜ

/-- A summable majorant on every compact set away from the lattice. -/
def series_normal_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ K : Set ℂ, IsCompact K → K ⊆ (lattice ω₁ ω₂ : Set ℂ)ᶜ →
      ∃ u : lattice ω₁ ω₂ → ℝ, Summable u ∧
        ∀ l : lattice ω₁ ω₂, ∀ z ∈ K, ‖1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2‖ ≤ u l

def holomorphic_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    _root_.D12Complex.HolomorphicOn (lattice ω₁ ω₂ : Set ℂ)ᶜ (weierstrassP ω₁ ω₂)

def meromorphic_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → Meromorphic (weierstrassP ω₁ ω₂)

/-- The exact principal part, including the absence of a simple-pole term. -/
def principal_part_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ a ∈ lattice ω₁ ω₂, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      (weierstrassP ω₁ ω₂) =ᶠ[𝓝[≠] a] (fun z => 1 / (z - a) ^ 2 + g z)

def pole_order_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ a ∈ lattice ω₁ ω₂, meromorphicOrderAt (weierstrassP ω₁ ω₂) a = -2

def derivative_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ z ∉ lattice ω₁ ω₂,
      HasDerivAt (weierstrassP ω₁ ω₂)
        (-2 * ∑' l : lattice ω₁ ω₂, 1 / (z - (l : ℂ)) ^ 3) z

def derivative_locallyUniform_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    HasSumLocallyUniformlyOn
      (fun (l : lattice ω₁ ω₂) (z : ℂ) => -2 / (z - (l : ℂ)) ^ 3)
      (deriv (weierstrassP ω₁ ω₂)) (lattice ω₁ ω₂ : Set ℂ)ᶜ

/-- Normal absolute convergence of the unscaled inverse-cube series. -/
def derivative_normal_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ K : Set ℂ, IsCompact K → K ⊆ (lattice ω₁ ω₂ : Set ℂ)ᶜ →
      ∃ u : lattice ω₁ ω₂ → ℝ, Summable u ∧
        ∀ l : lattice ω₁ ω₂, ∀ z ∈ K, ‖1 / (z - (l : ℂ)) ^ 3‖ ≤ u l

/-- Pointwise absolute convergence, with zero omitted in the inverse-square sum. -/
def absolute_convergence_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ z ∉ lattice ω₁ ω₂,
      Summable (fun l : {l : lattice ω₁ ω₂ // l ≠ 0} =>
        ‖1 / (z - (l.1 : ℂ)) ^ 2 - 1 / (l.1 : ℂ) ^ 2‖) ∧
      Summable (fun l : lattice ω₁ ω₂ => ‖1 / (z - (l : ℂ)) ^ 3‖)

/-- Derivatives of the finite regularized partial sums converge to the actual
complex derivative of the sum, locally uniformly off the lattice. -/
def termwise_differentiation_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    TendstoLocallyUniformlyOn
      (fun s : Finset (lattice ω₁ ω₂) =>
        deriv (fun z : ℂ => ∑ l ∈ s,
          (1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)))
      (deriv (weierstrassP ω₁ ω₂)) atTop (lattice ω₁ ω₂ : Set ℂ)ᶜ

end Specs.D12Complex.Ch22.WeierstrassSeries
