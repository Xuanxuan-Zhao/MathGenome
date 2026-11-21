import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.CcTensorApproximation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates
import Mathlib.MeasureTheory.Integral.CompactlySupported

/-! Independent statements for the compact-support integral stage of
paper.tex:5444–5455. Factor measures are on their Borel sigma-algebras.
The joint measurability assertion uses the factor product sigma-algebra,
which is not identified with the Borel sigma-algebra of the product topology.
All scalar integrals below are accompanied by actual integrability assertions.
No countability, sigma-finiteness, nonempty-space or nonzero-mass assumption
is imposed. The Radon product measure itself is a separate obligation. -/

namespace Specs.D11.Ch18.CcIteratedIntegrals

open Set MeasureTheory
open scoped ENNReal
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z

/-- Product measurability and a compact Borel rectangle with finite factor masses. -/
def measurable_finite_rectangle : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y],
  ∀ (𝕜 : Type) [RCLike 𝕜] (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∀ f : CompactlySupportedContinuousMap (X × Y) 𝕜,
      @Measurable (X × Y) 𝕜 ((borel X).prod (borel Y)) (borel 𝕜) f ∧
      ∃ K : Set X, ∃ L : Set Y,
        IsCompact K ∧ IsCompact L ∧ MeasurableSet K ∧ MeasurableSet L ∧
        μ K < ∞ ∧ ν L < ∞ ∧ tsupport f ⊆ K ×ˢ L

/-- Every section, including parameters outside the support projections, is
Borel measurable and absolutely integrable. -/
def sections_integrable : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y],
  ∀ (𝕜 : Type) [RCLike 𝕜] (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∀ f : CompactlySupportedContinuousMap (X × Y) 𝕜,
      (∀ x, Measurable (fun y => f (x,y)) ∧ Integrable (fun y => f (x,y)) ν) ∧
      (∀ y, Measurable (fun x => f (x,y)) ∧ Integrable (fun x => f (x,y)) μ)

/-- The two section-integral maps are actual Cc functions, supported in the
compact projections of the original closed support, and absolutely integrable. -/
def section_integrals_cc : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y],
  ∀ (𝕜 : Type) [RCLike 𝕜] (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∀ f : CompactlySupportedContinuousMap (X × Y) 𝕜,
      ∃ g : CompactlySupportedContinuousMap X 𝕜,
      ∃ h : CompactlySupportedContinuousMap Y 𝕜,
        (∀ x, g x = ∫ y, f (x,y) ∂ν) ∧
        (∀ y, h y = ∫ x, f (x,y) ∂μ) ∧
        tsupport g ⊆ Prod.fst '' tsupport f ∧
        tsupport h ⊆ Prod.snd '' tsupport f ∧
        Measurable g ∧ Measurable h ∧ Integrable g μ ∧ Integrable h ν

/-- The scalar Fubini equality and absolute integrability of the two
outer integrals of section norms. -/
def iterated_integrals : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y],
  ∀ (𝕜 : Type) [RCLike 𝕜] (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∀ f : CompactlySupportedContinuousMap (X × Y) 𝕜,
      Integrable (fun x => ∫ y, ‖f (x,y)‖ ∂ν) μ ∧
      Integrable (fun y => ∫ x, ‖f (x,y)‖ ∂μ) ν ∧
      (∫ x, (∫ y, f (x,y) ∂ν) ∂μ) = ∫ y, (∫ x, f (x,y) ∂μ) ∂ν

/-- The real iterated integral is a positive real-linear functional on Cc. -/
def positive_linear_functional : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y],
  ∀ (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∃ I : CompactlySupportedContinuousMap (X × Y) ℝ →ₚ[ℝ] ℝ,
      ∀ f, I f = ∫ x, (∫ y, f (x,y) ∂ν) ∂μ

end Specs.D11.Ch18.CcIteratedIntegrals
