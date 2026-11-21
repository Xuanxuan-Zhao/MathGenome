import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveContentIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveFunctionalBound

/-!
Independent statements for paper.tex:5542–5552, positive Riesz–Markov.
The domain is precisely the Borel sigma-algebra of an arbitrary LCH Hausdorff
space. `Represents` includes the Chapter 18 Radon predicate and actual scalar
measurability and absolute integrability, before asserting the integral identity.
No second countability, sigma-finiteness, total-mass bound, nonemptiness, or
continuity of the functional is assumed. The complex pairing is scalar-linear.
-/

open MeasureTheory

namespace Specs.D11.Ch19.PositiveRieszMarkov
universe u

open Specs.D11.Ch19.PositiveContentOuterMeasure
open Specs.D11.Ch06.ScalarIntegral

/-- The nonnegative real cone in the complex compact-support space. -/
abbrev ComplexPositive {X : Type u} [TopologicalSpace X]
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ) : Prop :=
  ∀ f, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
    0 ≤ (I f).re ∧ (I f).im = 0

/-- A positive Borel Radon representing measure, including finite absolute integrals. -/
def Represents {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (I : CompactlySupportedContinuousMap X 𝕜 →ₗ[𝕜] 𝕜)
    (μ : @Measure X (borel X)) : Prop :=
  Specs.D11.Ch18.RadonPredicates.isRadonValue μ ∧
    letI : MeasurableSpace X := borel X
    ∀ f : CompactlySupportedContinuousMap X 𝕜,
      ∃ hf : scalarIntegrable_value μ f, I f = scalarIntegral_value μ f hf

def real_representation : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ), Positive I →
    ∃! μ : @Measure X (borel X), Represents I μ

def radon_induces_real_functional : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), Specs.D11.Ch18.RadonPredicates.isRadonValue μ →
    ∃ I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ, Positive I ∧ Represents I μ

def complex_representation : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ), ComplexPositive I →
    ∃! μ : @Measure X (borel X), Represents I μ

def radon_induces_complex_functional : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), Specs.D11.Ch18.RadonPredicates.isRadonValue μ →
    ∃ I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ,
      ComplexPositive I ∧ Represents I μ

/-- The real restriction and the complex functional have exactly the same
representing positive measures. The pointwise relation expresses the ordinary
real-to-complex inclusion without introducing another compact-support space. -/
def real_complex_compatibility : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℂ →ₗ[ℂ] ℂ), ComplexPositive I →
    ∃ J : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ,
      Positive J ∧
      (∀ (f : CompactlySupportedContinuousMap X ℝ)
        (g : CompactlySupportedContinuousMap X ℂ),
        (∀ x, g x = (f x : ℂ)) → I g = (J f : ℂ)) ∧
      ∀ μ : @Measure X (borel X), Represents J μ ↔ Represents I μ

end Specs.D11.Ch19.PositiveRieszMarkov
