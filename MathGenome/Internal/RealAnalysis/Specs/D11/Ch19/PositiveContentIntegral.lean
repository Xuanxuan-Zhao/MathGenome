import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveContentRadon
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-!
Independent statements for paper.tex:5532–5540. The measure is the previously
constructed Borel measure on the same arbitrary LCH Hausdorff space. No global
finiteness, sigma-finiteness, second countability, or nonemptiness is assumed.

All level masses below are finite, so their real values are exactly their
nonnegative extended-real values embedded in ℝ. `range N` with successor index
is the sum over j = 1,...,N in the source; the upper sum uses j-1 = 0,...,N-1.
The norm of the native bounded continuous function is the uniform norm of f.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch19.PositiveContentIntegral
universe u

open Specs.D11.Ch19.PositiveContentOuterMeasure
open Specs.D11.Ch06.ScalarIntegral

/-- The zero level is the closed support, not the possibly noncompact set {f ≥ 0}. -/
def levelSet {X : Type u} [TopologicalSpace X]
    (f : CompactlySupportedContinuousMap X ℝ) (η : ℝ) : ℕ → Set X
  | 0 => closure {x | f x ≠ 0}
  | j + 1 => {x | (j + 1 : ℕ) * η ≤ f x}

noncomputable def lowerSum {X : Type u} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ)
    (hI : Positive I) (f : CompactlySupportedContinuousMap X ℝ) (η : ℝ) (N : ℕ) : ℝ :=
  η * ∑ j ∈ Finset.range N, (borelMeasure_value I hI).real (levelSet f η (j + 1))

noncomputable def upperSum {X : Type u} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ)
    (hI : Positive I) (f : CompactlySupportedContinuousMap X ℝ) (η : ℝ) (N : ℕ) : ℝ :=
  η * ∑ j ∈ Finset.range N, (borelMeasure_value I hI).real (levelSet f η j)

/-- Actual Borel measurability and absolute integrability, for real or complex Cc. -/
def scalar_integrable : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : CompactlySupportedContinuousMap X 𝕜),
    letI : MeasurableSpace X := borel X
    scalarIntegrable_value (borelMeasure_value I hI) f

/-- The real scalar integral is the given functional, with integrability explicit. -/
def integral_eq : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (f : CompactlySupportedContinuousMap X ℝ),
    letI : MeasurableSpace X := borel X
    ∃ hf : scalarIntegrable_value (borelMeasure_value I hI) f,
      I f = scalarIntegral_value (borelMeasure_value I hI) f hf

/-- Both quantities lie in the same interval, whose finite width is at most η μ(supp f).
N = 0 is admitted whenever the specified norm condition holds (hence f = 0). -/
def level_sums : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (f : CompactlySupportedContinuousMap X ℝ), (∀ x, 0 ≤ f x) →
    ∀ (η : ℝ), 0 < η → ∀ N : ℕ, ‖f.toBoundedContinuousFunction‖ ≤ (N : ℝ) * η →
    letI : MeasurableSpace X := borel X
    (∀ j, IsCompact (levelSet f η j)) ∧
    (∀ j, borelMeasure_value I hI (levelSet f η j) < ∞) ∧
    lowerSum I hI f η N ≤ I f ∧ I f ≤ upperSum I hI f η N ∧
    lowerSum I hI f η N ≤ ∫ x, f x ∂(borelMeasure_value I hI) ∧
    (∫ x, f x ∂(borelMeasure_value I hI)) ≤ upperSum I hI f η N ∧
    0 ≤ upperSum I hI f η N - lowerSum I hI f η N ∧
    upperSum I hI f η N - lowerSum I hI f η N ≤
      η * (borelMeasure_value I hI).real (closure {x | f x ≠ 0})

/-- Splitting into f⁺ and f⁻ takes place within the canonical real Cc space;
both parts are scalar integrable, and both the functional and integral split. -/
def real_parts : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (f : CompactlySupportedContinuousMap X ℝ),
    letI : MeasurableSpace X := borel X
    let p := f ⊔ 0
    let n := (-f) ⊔ 0
    (∀ x, p x = max (f x) 0 ∧ n x = max (-f x) 0) ∧
    f = p - n ∧
    scalarIntegrable_value (borelMeasure_value I hI) p ∧
    scalarIntegrable_value (borelMeasure_value I hI) n ∧
    I f = I p - I n ∧
    (∫ x, f x ∂(borelMeasure_value I hI)) =
      (∫ x, p x ∂(borelMeasure_value I hI)) - ∫ x, n x ∂(borelMeasure_value I hI)

end Specs.D11.Ch19.PositiveContentIntegral
