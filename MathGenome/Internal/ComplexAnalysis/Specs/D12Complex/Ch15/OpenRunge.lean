import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.RationalInfinity
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DiskCauchyFormula
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The complete approximation corollary d12:15-05, paper.tex:2743–2748.
The rational functions are filled spherical quotients: cancelled denominator
zeros are not poles. Convergence is ordinary uniform convergence on every
compact subset, including the empty set and disconnected open sets. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch15.OpenRunge
open _root_.D12Complex
open Specs.D12Complex.Ch07.RationalInfinity.Objects

/-- Every holomorphic function admits a sequence with the prescribed global
spherical pole restriction; each finite coordinate is holomorphic on all Ω. -/
def open_runge_type : Prop :=
  ∀ (Ω : Set ℂ) (A : Set RiemannSphere) (f : ℂ → ℂ),
    IsOpen Ω → A ⊆ (sphereFinite '' Ω)ᶜ →
    (∀ p ∈ (sphereFinite '' Ω)ᶜ,
      (connectedComponentIn (sphereFinite '' Ω)ᶜ p ∩ A).Nonempty) →
    HolomorphicOn Ω f →
    ∃ P Q : ℕ → Polynomial ℂ,
      (∀ n, Q n ≠ 0) ∧
      (∀ n p, extension (P n) (Q n) p = sphereInfty → p ∈ A) ∧
      (∀ n, ∀ z ∈ Ω, extension (P n) (Q n) (sphereFinite z) =
        sphereFinite (finiteCoordinate (extension (P n) (Q n) (sphereFinite z)))) ∧
      (∀ n, HolomorphicOn Ω
        (fun z => finiteCoordinate (extension (P n) (Q n) (sphereFinite z)))) ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        TendstoUniformlyOn
          (fun n z => finiteCoordinate (extension (P n) (Q n) (sphereFinite z)))
          f atTop K

/-- The polynomial specialization has no connectedness, boundedness, or
nonemptiness hypothesis on the open set itself. -/
def polynomial_runge_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsOpen Ω →
    IsConnected (sphereFinite '' Ω)ᶜ → HolomorphicOn Ω f →
    ∃ P : ℕ → Polynomial ℂ,
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        TendstoUniformlyOn (fun n z => (P n).eval z) f atTop K

/-- The contour obstruction on every circle enclosing zero. -/
def circle_integrals_type : Prop :=
  ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → ‖c‖ < ρ →
    (Ch04.DiskCauchyFormula.circlePath_value c ρ).integral
        (fun z : ℂ => z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I ∧
    ∀ P : Polynomial ℂ,
      (Ch04.DiskCauchyFormula.circlePath_value c ρ).integral (fun z => P.eval z) = 0

/-- This rules out uniform polynomial approximation on any circle enclosing
zero, and hence on every such circle contained in an annulus. -/
def circle_obstruction_type : Prop :=
  ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → ‖c‖ < ρ →
    ¬ ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z => (P n).eval z)
        (fun z : ℂ => z⁻¹) atTop (Metric.sphere c ρ)

/-- Any circle strictly inside a centered annulus is an obstruction to
polynomial approximation of 1/z, in the ordinary uniform topology. -/
def annulus_obstruction_type : Prop :=
  ∀ (r R ρ : ℝ), 0 ≤ r → r < ρ → ρ < R →
    Metric.sphere (0 : ℂ) ρ ⊆ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} ∧
    ¬ ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z => (P n).eval z)
        (fun z : ℂ => z⁻¹) atTop (Metric.sphere 0 ρ)

end Specs.D12Complex.Ch15.OpenRunge
