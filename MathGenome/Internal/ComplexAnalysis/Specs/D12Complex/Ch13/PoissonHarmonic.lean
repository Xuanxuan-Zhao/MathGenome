import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicFoundation
import Mathlib.Analysis.Complex.Poisson

/-! The kernel and interior construction from paper.tex:2557–2570.
Boundary data are total functions restricted by `ContinuousOn` only on the circle.
`circleMap 0 R t = R * exp (t * I)`, so these are the source angular integrals.
There is no assumption of a harmonic extension or a mean-value characterization. -/
noncomputable section
open Complex Metric

namespace Specs.D12Complex.Ch13.PoissonHarmonic
open _root_.D12Complex

def kernel_type := ℝ → ℂ → ℂ → ℝ
def kernel_value : kernel_type := fun R z ζ => (R ^ 2 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2

def complexKernel_type := ℂ → ℂ → ℂ
def complexKernel_value : complexKernel_type := fun z ζ => (ζ + z) / (ζ - z)

def poissonIntegral_type := ℝ → (ℂ → ℝ) → ℂ → ℝ
def poissonIntegral_value : poissonIntegral_type := fun R φ z =>
  (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi,
    kernel_value R z (circleMap 0 R t) * φ (circleMap 0 R t)

def schwarzIntegral_type := ℝ → (ℂ → ℝ) → ℂ → ℂ
def schwarzIntegral_value : schwarzIntegral_type := fun R φ z =>
  (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..2 * Real.pi,
    complexKernel_value z (circleMap 0 R t) * (φ (circleMap 0 R t) : ℂ)

def kernel_positive_type : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (z ζ : ℂ), ‖z‖ < R → ‖ζ‖ = R →
    0 < kernel_value R z ζ

def kernel_eq_re_type : Prop :=
  ∀ (R : ℝ) (z ζ : ℂ), ‖ζ‖ = R → kernel_value R z ζ = (complexKernel_value z ζ).re

def kernel_normalized_type : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (z : ℂ), ‖z‖ < R →
    (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi,
      kernel_value R z (circleMap 0 R t) = 1

/-- Integrals defining both constructions exist as ordinary angular integrals. -/
def integrands_integrable_type : Prop :=
  ∀ (R : ℝ) (φ : ℂ → ℝ), 0 < R → ContinuousOn φ (sphere 0 R) →
    ∀ (z : ℂ), ‖z‖ < R →
      IntervalIntegrable (fun t => kernel_value R z (circleMap 0 R t) *
        φ (circleMap 0 R t)) MeasureTheory.volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (fun t => complexKernel_value z (circleMap 0 R t) *
        (φ (circleMap 0 R t) : ℂ)) MeasureTheory.volume 0 (2 * Real.pi)

def schwarzIntegral_holomorphic_type : Prop :=
  ∀ (R : ℝ) (φ : ℂ → ℝ), 0 < R → ContinuousOn φ (sphere 0 R) →
    HolomorphicOn (ball 0 R) (schwarzIntegral_value R φ)

def schwarzIntegral_re_type : Prop :=
  ∀ (R : ℝ) (φ : ℂ → ℝ), 0 < R → ContinuousOn φ (sphere 0 R) →
    ∀ (z : ℂ), ‖z‖ < R → (schwarzIntegral_value R φ z).re = poissonIntegral_value R φ z

def poissonIntegral_harmonic_type : Prop :=
  ∀ (R : ℝ) (φ : ℂ → ℝ), 0 < R → ContinuousOn φ (sphere 0 R) →
    HarmonicOn (ball 0 R) (poissonIntegral_value R φ)

end Specs.D12Complex.Ch13.PoissonHarmonic
