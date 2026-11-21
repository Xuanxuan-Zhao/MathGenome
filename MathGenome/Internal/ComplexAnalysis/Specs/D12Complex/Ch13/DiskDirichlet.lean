import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.PoissonHarmonic

/-! The boundary, uniqueness, and translated representation assertions of
paper.tex:2557–2570. No boundary smoothness or approach restriction is imposed. -/
noncomputable section
open Complex Metric Filter Set
open scoped Topology

namespace Specs.D12Complex.Ch13.DiskDirichlet
open _root_.D12Complex
open Specs.D12Complex.Ch13.PoissonHarmonic

def closedPoissonIntegral_type := ℝ → (ℂ → ℝ) → ℂ → ℝ

def closedPoissonIntegral_value : closedPoissonIntegral_type := fun R φ z =>
  if ‖z‖ < R then poissonIntegral_value R φ z else φ z

def poissonIntegral_boundary_limit_type : Prop :=
  ∀ (R : ℝ) (φ : ℂ → ℝ), 0 < R → ContinuousOn φ (sphere 0 R) →
    ∀ ξ ∈ sphere (0 : ℂ) R,
      Tendsto (poissonIntegral_value R φ) (𝓝[ball 0 R] ξ) (𝓝 (φ ξ))

def closedPoissonIntegral_solution_type : Prop :=
  ∀ (R : ℝ) (φ : ℂ → ℝ), 0 < R → ContinuousOn φ (sphere 0 R) →
    ContinuousOn (closedPoissonIntegral_value R φ) (closedBall 0 R) ∧
    HarmonicOn (ball 0 R) (closedPoissonIntegral_value R φ) ∧
    EqOn (closedPoissonIntegral_value R φ) φ (sphere 0 R) ∧
    EqOn (closedPoissonIntegral_value R φ) (poissonIntegral_value R φ) (ball 0 R)

def disk_dirichlet_unique_type : Prop :=
  ∀ (R : ℝ) (φ u : ℂ → ℝ), 0 < R → ContinuousOn φ (sphere 0 R) →
    ContinuousOn u (closedBall 0 R) → HarmonicOn (ball 0 R) u →
    EqOn u φ (sphere 0 R) →
    EqOn u (closedPoissonIntegral_value R φ) (closedBall 0 R)

def harmonic_poisson_representation_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ) (a : ℂ) (R : ℝ),
    HarmonicOn U u → 0 < R → closedBall a R ⊆ U →
    ∀ z ∈ ball a R,
      u z = (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi,
        ((R ^ 2 - ‖z - a‖ ^ 2) / ‖circleMap a R t - z‖ ^ 2) *
          u (circleMap a R t)

end Specs.D12Complex.Ch13.DiskDirichlet
