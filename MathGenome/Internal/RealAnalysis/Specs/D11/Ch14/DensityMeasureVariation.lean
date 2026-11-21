import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.TotalVariation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.Jordan
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-! Independent interface for paper.tex:4723–4747. Densities are genuinely
measurable and absolutely integrable on the original sigma-algebra. The
reference measure is arbitrary; no sigma-finiteness or completeness is assumed.
The variation below is the canonical finite-partition variation, not a new
object defined to have the desired density. -/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch14.DensityMeasureVariation

open Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch14.TotalVariation Specs.D11.Ch14.Jordan
open Specs.D11.Ch14.ScalarInterfaces

abbrev densityMeasure_type :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (h : X → 𝕜),
    scalarIntegrable_value μ h → VectorMeasure X 𝕜

noncomputable def densityMeasure_value : densityMeasure_type.{u} :=
  fun μ h _ => μ.withDensityᵥ h

def densityMeasure_apply : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable_value μ h) (E : Set X), MeasurableSet E →
    densityMeasure_value μ h hh E = ∫ x in E, h x ∂μ

def densityMeasure_finite : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable_value μ h),
    IsFiniteMeasure (totalVariation_value (densityMeasure_value μ h hh))

def densityMeasure_countable_additivity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable_value μ h) (E : ℕ → Set X),
    (∀ n, MeasurableSet (E n)) → Pairwise (fun i j => Disjoint (E i) (E j)) →
    HasSum (fun n => densityMeasure_value μ h hh (E n))
      (densityMeasure_value μ h hh (⋃ n, E n))

def densityMeasure_variation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable_value μ h),
    totalVariation_value (densityMeasure_value μ h hh) =
      μ.withDensity (fun x => ENNReal.ofReal ‖h x‖)

def densityMeasure_variation_apply : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable_value μ h) (E : Set X), MeasurableSet E →
    totalVariation_value (densityMeasure_value μ h hh) E =
      ∫⁻ x in E, ENNReal.ofReal ‖h x‖ ∂μ

/-- Retain the explicit original finite-partition supremum on every measurable E. -/
def densityMeasure_partition_variation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (h : X → 𝕜)
    (hh : scalarIntegrable_value μ h) (E : Set X) (hE : MeasurableSet E),
    (⨆ (P : Finpartition (⟨E, hE⟩ : Subtype MeasurableSet)),
      ∑ A ∈ P.parts, ENNReal.ofReal ‖densityMeasure_value μ h hh A‖) =
        ∫⁻ x in E, ENNReal.ofReal ‖h x‖ ∂μ

def densityMeasure_jordan : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (h : X → ℝ)
    (hh : scalarIntegrable_value μ h),
    Specs.D11.Ch14.Jordan.positivePart_value (densityMeasure_value μ h hh) =
      μ.withDensity (fun x => ENNReal.ofReal (Specs.D11.Ch06.ScalarIntegral.positivePart_value h x)) ∧
    Specs.D11.Ch14.Jordan.negativePart_value (densityMeasure_value μ h hh) =
      μ.withDensity (fun x => ENNReal.ofReal (Specs.D11.Ch06.ScalarIntegral.negativePart_value h x))

def densityMeasure_jordan_apply : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (h : X → ℝ)
    (hh : scalarIntegrable_value μ h) (E : Set X), MeasurableSet E →
    Specs.D11.Ch14.Jordan.positivePart_value (densityMeasure_value μ h hh) E =
      (∫⁻ x in E, ENNReal.ofReal (Specs.D11.Ch06.ScalarIntegral.positivePart_value h x) ∂μ) ∧
    Specs.D11.Ch14.Jordan.negativePart_value (densityMeasure_value μ h hh) E =
      (∫⁻ x in E, ENNReal.ofReal (Specs.D11.Ch06.ScalarIntegral.negativePart_value h x) ∂μ)

end Specs.D11.Ch14.DensityMeasureVariation
