import MathGenome.RealAnalysis

/-! Independent downstream propositions. Suggested installed module name:
`Examples.RealAnalysisRadonReuseSpecs`. These state the expected mathematics
directly, without importing the candidate proof module. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
universe u v

namespace RealAnalysisRadonReuseSpecs

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

/-- Arbitrary Radon factors: coordinate interchange on the full product
topology's Borel domain, with the resulting measure still Radon. -/
def arbitrary_radon_swap : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : @Measure X (borel X)) (ν : @Measure Y (borel Y)),
    D11.Ch18.isRadon μ → D11.Ch18.isRadon ν →
    letI : MeasurableSpace (X × Y) := borel (X × Y)
    letI : MeasurableSpace (Y × X) := borel (Y × X)
    D11.Ch18.isRadon (D11.Ch18.RadonProduct.radonProduct μ ν) ∧
      ∀ E : Set (X × Y), MeasurableSet[borel (X × Y)] E →
        D11.Ch18.RadonProduct.radonProduct μ ν E =
          D11.Ch18.RadonProduct.radonProduct ν μ (Prod.swap ⁻¹' E)

/-- Positive Cc representation followed by integration recovers the original
linear functional, with actual absolute integrability at both interfaces. -/
def positive_riesz_roundtrip : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ),
    (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f) →
    ∃ μ : @Measure X (borel X),
      D11.Ch18.isRadon μ ∧
      (∀ f : CompactlySupportedContinuousMap X ℝ,
        Integrable f μ ∧ I f = ∫ x, f x ∂μ) ∧
      ∃ J : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ,
        (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ J f) ∧
        (∀ f : CompactlySupportedContinuousMap X ℝ,
          Integrable f μ ∧ J f = ∫ x, f x ∂μ) ∧
        J = I

/-- Normalizing any compact-group left Haar measure gives the unique left
Haar probability, without an extra choice of a preferred Haar measure. -/
def compact_haar_normalization_unique : Prop :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] (μ : @Measure G (borel G)),
    D11.Ch21.isLeftHaarMeasure μ →
      D11.Ch21.isLeftHaarMeasure ((μ univ)⁻¹ • μ) ∧
      ((μ univ)⁻¹ • μ) univ = 1 ∧
      ∀ ν : @Measure G (borel G),
        D11.Ch21.isLeftHaarMeasure ν → ν univ = 1 →
          ν = (μ univ)⁻¹ • μ

end RealAnalysisRadonReuseSpecs
