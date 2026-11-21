import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.CompletedProduct
import MathGenome.Internal.RealAnalysis.D11.Ch04.AeCommonException
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
Tonelli and scalar Fubini after completion (paper.tex:2684–2751).

Completion preserves the original measure's values and a.e. filter. Its trim
to the original sigma-algebra is therefore the original measure, giving the
explicit integral bridges below. Countably generated scalar Borel structures
provide original a.e. measurable representatives. Product-null exceptions
have null sections almost everywhere, so the actual sections are measurable
on the completed factors almost everywhere.

The specified section maps, with zero at each nonmeasurable/nonintegrable
section, agree a.e. with the native original section maps. This proves actual
measurability on completed factors, and transfers both integral identities.
Scalar integrability always retains actual completed measurability and finite
absolute integral. No original completeness, nonempty-space or positive-mass
hypothesis is added, and the product is completed only after its construction.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Specs.D11.Ch02.Completion (completedSpace_value completedMeasure_value)
open Specs.D11.Ch08.CompletedProduct
open Specs.D11.Ch06.ScalarIntegral (scalarIntegrable_value scalarIntegral_value)
open Specs.D11.Ch05.NonnegativeIntegral (nonnegativeIntegral_value)

universe u v
noncomputable section
namespace D11.Ch08.CompletedProduct

def nonnegativeSectionLeft : nonnegativeSectionLeft_type.{u,v} := nonnegativeSectionLeft_value
def nonnegativeSectionRight : nonnegativeSectionRight_type.{u,v} := nonnegativeSectionRight_value
def scalarSectionLeft : scalarSectionLeft_type.{u,v} := scalarSectionLeft_value
def scalarSectionRight : scalarSectionRight_type.{u,v} := scalarSectionRight_value

variable {X : Type u} [m : MeasurableSpace X]

lemma original_le_completion (μ : Measure X) : m ≤ completedSpace_value μ :=
  fun _ hs => hs.nullMeasurableSet

lemma completion_trim (μ : Measure X) :
    (completedMeasure_value μ).trim (original_le_completion μ) = μ := by
  apply Measure.ext
  intro s hs
  rw [trim_measurableSet_eq _ hs]
  rfl

lemma lintegral_completion (μ : Measure X) (f : X → ℝ≥0∞) (hf : AEMeasurable f μ) :
    @lintegral X (completedSpace_value μ) (completedMeasure_value μ) f =
      ∫⁻ x, f x ∂μ := by
  have h := @lintegral_trim_ae X m (completedSpace_value μ)
    (completedMeasure_value μ) (original_le_completion μ) f
  rw [completion_trim μ] at h
  exact (h hf).symm

/-- Integration against the completion agrees on every original a.e. measurable
nonnegative function. The trim is the original measure by setwise agreement. -/
lemma completedNNIntegral_eq (μ : Measure X) (f : X → ℝ≥0∞)
    (hf : completedMeasurable μ f) :
    completedNNIntegral μ f = ∫⁻ x, f x ∂μ := by
  exact (@D11.Ch05.NonnegativeIntegral.eq_lintegral X (completedSpace_value μ)
    (completedMeasure_value μ) f hf).trans
    (lintegral_completion μ f (show NullMeasurable f μ from hf).aemeasurable)

theorem nonnegative_completion : Specs.D11.Ch08.CompletedProduct.nonnegative_completion.{u} := by
  intro X m μ f hf
  have hc : completedMeasurable μ f := hf.nullMeasurable
  exact ⟨hc, (completedNNIntegral_eq μ f hc).trans
    (D11.Ch05.NonnegativeIntegral.eq_lintegral μ f hf).symm⟩

variable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

lemma integral_completion (μ : Measure X) (f : X → 𝕜) (hf : AEMeasurable f μ) :
    @integral X 𝕜 _ _ (completedSpace_value μ) (completedMeasure_value μ) f =
      ∫ x, f x ∂μ := by
  have h := @integral_trim_ae 𝕜 _ _ X m (completedSpace_value μ)
    (completedMeasure_value μ) (original_le_completion μ) f
  rw [completion_trim μ] at h
  exact h hf.aestronglyMeasurable

lemma completedIntegrable_iff (μ : Measure X) (f : X → 𝕜) :
    completedIntegrable μ f ↔ completedMeasurable μ f ∧ Integrable f μ := by
  constructor
  · intro hf
    have hn := (@D11.Ch06.ScalarIntegral.scalarIntegrable_iff X 𝕜 (completedSpace_value μ)
      _ _ _ (completedMeasure_value μ) f).mp hf
    have ha := (show NullMeasurable f μ from hn.1).aemeasurable
    refine ⟨hn.1, ha.aestronglyMeasurable, ?_⟩
    change (∫⁻ x, ‖f x‖ₑ ∂μ) < ∞
    rw [← lintegral_completion μ _ ha.enorm]
    exact hn.2.2
  · rintro ⟨hm, hi⟩
    apply (@D11.Ch06.ScalarIntegral.scalarIntegrable_iff X 𝕜 (completedSpace_value μ)
      _ _ _ (completedMeasure_value μ) f).mpr
    refine ⟨hm, integrable_of_integrable_trim (original_le_completion μ) ?_⟩
    rwa [completion_trim μ]

theorem scalar_completion : Specs.D11.Ch08.CompletedProduct.scalar_completion.{u} := by
  intro X m 𝕜 _ _ _ μ f hf
  have hn := (D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ f).mp hf
  have hc := (completedIntegrable_iff μ f).mpr ⟨hn.1.nullMeasurable, hn.2⟩
  exact ⟨hc, integral_completion μ f hn.1.aemeasurable⟩

variable {Y : Type v} [n : MeasurableSpace Y]

lemma ae_completed_sections_left {E : Type*} [MeasurableSpace E]
    (μ : Measure X) (ν : Measure Y) [SFinite ν] (f : X × Y → E)
    (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, completedMeasurable ν (fun y => f (x, y)) := by
  filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with x hx
  exact ((hf.measurable_mk.comp measurable_prodMk_left).aemeasurable.congr
    (Filter.EventuallyEq.symm hx)).nullMeasurable

lemma ae_completed_sections_right {E : Type*} [MeasurableSpace E]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (f : X × Y → E)
    (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, completedMeasurable μ (fun x => f (x, y)) :=
  ae_completed_sections_left ν μ (fun p => f p.swap) hf.prod_swap

lemma nonnegativeSectionLeft_ae_eq (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (f : X × Y → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    nonnegativeSectionLeft_value ν f =ᵐ[μ] (fun x => ∫⁻ y, f (x, y) ∂ν) := by
  classical
  filter_upwards [ae_completed_sections_left μ ν f hf] with x hx
  change (if completedMeasurable ν (fun y => f (x, y)) then _ else 0) = _
  rw [ite_eq_left hx]
  exact completedNNIntegral_eq ν _ hx

lemma nonnegativeSectionRight_ae_eq (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (f : X × Y → ℝ≥0∞)
    (hf : AEMeasurable f (μ.prod ν)) :
    nonnegativeSectionRight_value μ f =ᵐ[ν] (fun y => ∫⁻ x, f (x, y) ∂μ) :=
  nonnegativeSectionLeft_ae_eq ν μ (fun p => f p.swap) hf.prod_swap

theorem tonelli : Specs.D11.Ch08.CompletedProduct.tonelli.{u,v} := by
  intro X Y m n μ ν hμ hν f hf
  let : SigmaFinite μ := hμ
  let : SigmaFinite ν := hν
  have ha : AEMeasurable f (μ.prod ν) := (show NullMeasurable f (μ.prod ν) from hf).aemeasurable
  have hsl := ae_completed_sections_left μ ν f ha
  have hsr := ae_completed_sections_right μ ν f ha
  have hel := nonnegativeSectionLeft_ae_eq μ ν f ha
  have her := nonnegativeSectionRight_ae_eq μ ν f ha
  have hml : completedMeasurable μ (nonnegativeSectionLeft_value ν f) :=
    (ha.lintegral_prod_right'.congr hel.symm).nullMeasurable
  have hmr : completedMeasurable ν (nonnegativeSectionRight_value μ f) :=
    (ha.lintegral_prod_left'.congr her.symm).nullMeasurable
  have hl : completedNNIntegral (μ.prod ν) f =
      completedNNIntegral μ (nonnegativeSectionLeft_value ν f) := by
    exact (completedNNIntegral_eq (μ.prod ν) f hf).trans
      ((lintegral_prod f ha).trans ((lintegral_congr_ae hel).symm.trans
        (completedNNIntegral_eq μ _ hml).symm))
  have hr : completedNNIntegral (μ.prod ν) f =
      completedNNIntegral ν (nonnegativeSectionRight_value μ f) := by
    exact (completedNNIntegral_eq (μ.prod ν) f hf).trans
      ((lintegral_prod_symm f ha).trans ((lintegral_congr_ae her).symm.trans
        (completedNNIntegral_eq ν _ hmr).symm))
  refine ⟨?_, ?_, hml, hmr, hl, hl.symm.trans hr⟩
  · apply (@D11.Ch04.AeCommonException.almostEverywhere_iff_native X
      (completedSpace_value μ) (completedMeasure_value μ) _).mpr
    exact hsl
  · apply (@D11.Ch04.AeCommonException.almostEverywhere_iff_native Y
      (completedSpace_value ν) (completedMeasure_value ν) _).mpr
    exact hsr

lemma completedIntegral_eq (μ : Measure X) (f : X → 𝕜) (hf : completedIntegrable μ f) :
    completedIntegral μ f hf = ∫ x, f x ∂μ :=
  integral_completion μ f ((completedIntegrable_iff μ f).mp hf).2.aemeasurable

lemma ae_completed_integrable_left (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X × Y → 𝕜) (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, completedIntegrable ν (fun y => f (x, y)) := by
  filter_upwards [ae_completed_sections_left μ ν f hf.aemeasurable, hf.prod_right_ae] with x hm hi
  exact (completedIntegrable_iff ν _).mpr ⟨hm, hi⟩

lemma ae_completed_integrable_right (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X × Y → 𝕜) (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, completedIntegrable μ (fun x => f (x, y)) :=
  ae_completed_integrable_left ν μ (fun p => f p.swap) hf.swap

lemma scalarSectionLeft_ae_eq (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X × Y → 𝕜) (hf : Integrable f (μ.prod ν)) :
    scalarSectionLeft_value ν f =ᵐ[μ] (fun x => ∫ y, f (x, y) ∂ν) := by
  classical
  filter_upwards [ae_completed_integrable_left μ ν f hf] with x hx
  change (if h : completedIntegrable ν (fun y => f (x, y)) then _ else 0) = _
  rw [dite_eq_left hx]
  exact completedIntegral_eq ν _ hx

lemma scalarSectionRight_ae_eq (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X × Y → 𝕜) (hf : Integrable f (μ.prod ν)) :
    scalarSectionRight_value μ f =ᵐ[ν] (fun y => ∫ x, f (x, y) ∂μ) :=
  scalarSectionLeft_ae_eq ν μ (fun p => f p.swap) hf.swap

theorem fubini : Specs.D11.Ch08.CompletedProduct.fubini.{u,v} := by
  intro X Y 𝕜 m n _ _ _ μ ν hμ hν f hf
  let : SigmaFinite μ := hμ
  let : SigmaFinite ν := hν
  have hi : Integrable f (μ.prod ν) :=
    ((completedIntegrable_iff (μ.prod ν) f).mp hf).2
  have hsl := ae_completed_integrable_left μ ν f hi
  have hsr := ae_completed_integrable_right μ ν f hi
  have hel := scalarSectionLeft_ae_eq μ ν f hi
  have her := scalarSectionRight_ae_eq μ ν f hi
  have hml : completedMeasurable μ (scalarSectionLeft_value ν f) :=
    (hi.aestronglyMeasurable.integral_prod_right'.aemeasurable.congr hel.symm).nullMeasurable
  have hmr : completedMeasurable ν (scalarSectionRight_value μ f) :=
    (hi.swap.aestronglyMeasurable.integral_prod_right'.aemeasurable.congr her.symm).nullMeasurable
  have hil : completedIntegrable μ (scalarSectionLeft_value ν f) :=
    (completedIntegrable_iff μ _).mpr ⟨hml, hi.integral_prod_left.congr hel.symm⟩
  have hir : completedIntegrable ν (scalarSectionRight_value μ f) :=
    (completedIntegrable_iff ν _).mpr ⟨hmr, hi.integral_prod_right.congr her.symm⟩
  have hl : completedIntegral (μ.prod ν) f hf =
      completedIntegral μ (scalarSectionLeft_value ν f) hil :=
    (completedIntegral_eq (μ.prod ν) f hf).trans
      ((integral_prod f hi).trans ((integral_congr_ae hel).symm.trans
        (completedIntegral_eq μ _ hil).symm))
  have hr : completedIntegral (μ.prod ν) f hf =
      completedIntegral ν (scalarSectionRight_value μ f) hir :=
    (completedIntegral_eq (μ.prod ν) f hf).trans
      ((integral_prod_symm f hi).trans ((integral_congr_ae her).symm.trans
        (completedIntegral_eq ν _ hir).symm))
  refine ⟨?_, ?_, hml, hmr, hil, hir, hl, hl.symm.trans hr⟩
  · apply (@D11.Ch04.AeCommonException.almostEverywhere_iff_native X
      (completedSpace_value μ) (completedMeasure_value μ) _).mpr
    exact hsl
  · apply (@D11.Ch04.AeCommonException.almostEverywhere_iff_native Y
      (completedSpace_value ν) (completedMeasure_value ν) _).mpr
    exact hsr

end D11.Ch08.CompletedProduct
