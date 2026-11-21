import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
Radon–Nikodym (`fa2:p4:radon-nikodym`). The library's positive theorem is
applied to the Jordan parts of a signed measure. The complex construction
combines the real and imaginary signed densities. The variation formula for
an integral vector measure gives the exact absolute integral, and equality
of all measurable set integrals gives ordinary a.e. uniqueness. This proof
uses no Lᵖ duality theorem.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u

namespace ExpandedFA.FunctionSpaces

/-- The variation identity for a density, before specializing to scalars. -/
theorem variation_mass_withDensity {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) {g : X → E} (hg : Integrable g μ) :
    (∫⁻ x, ‖g x‖ₑ ∂μ) = (μ.withDensityᵥ g).variation Set.univ := by
  rw [Measure.variation_withDensityᵥ hg, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem signed_radon_nikodym : RadonNikodymSpec.SignedRepresentation.{u} := by
  intro X _ μ _ ν hν
  let g := ν.rnDeriv μ
  have hg : Integrable g μ := ν.integrable_rnDeriv μ
  have hrep : μ.withDensityᵥ g = ν := ν.withDensityᵥ_rnDeriv_eq μ hν
  have hsets (A : Set X) (hA : MeasurableSet A) :
      ν A = ∫ x in A, g x ∂μ := by
    rw [← hrep, withDensityᵥ_apply hg hA]
  have hmass : (∫⁻ x, ‖g x‖ₑ ∂μ) = ν.totalVariation Set.univ := by
    rw [ν.totalVariation_eq_variation, ← hrep]
    exact variation_mass_withDensity μ hg
  refine ⟨g, ν.measurable_rnDeriv μ, hg, hsets, hmass, ?_, ?_⟩
  · rw [integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable, hmass]
    rfl
  · intro f hf hfsets
    exact Integrable.ae_eq_of_forall_setIntegral_eq f g hf hg
      (fun A hA _ => (hfsets A hA).symm.trans (hsets A hA))

/-- The missing complex bridge is obtained by applying the signed theorem
separately to the real and imaginary parts and commuting these projections
with each set integral. -/
theorem complex_withDensity_rnDeriv {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (ν : ComplexMeasure X)
    (hν : ν ≪ᵥ μ.toENNRealVectorMeasure) : μ.withDensityᵥ (ν.rnDeriv μ) = ν := by
  have hparts := (ComplexMeasure.absolutelyContinuous_ennreal_iff ν _).mp hν
  have hre := ν.re.withDensityᵥ_rnDeriv_eq μ hparts.1
  have him := ν.im.withDensityᵥ_rnDeriv_eq μ hparts.2
  have hg := ν.integrable_rnDeriv μ
  apply VectorMeasure.ext
  intro A hA
  rw [withDensityᵥ_apply hg hA]
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re hg.integrableOn,
      RCLike.re_eq_complex_re]
    change (∫ x in A, ν.re.rnDeriv μ x ∂μ) = ν.re A
    rw [← withDensityᵥ_apply (ν.re.integrable_rnDeriv μ) hA, hre]
  · rw [← RCLike.im_eq_complex_im, ← integral_im hg.integrableOn,
      RCLike.im_eq_complex_im]
    change (∫ x in A, ν.im.rnDeriv μ x ∂μ) = ν.im A
    rw [← withDensityᵥ_apply (ν.im.integrable_rnDeriv μ) hA, him]

theorem complex_radon_nikodym : RadonNikodymSpec.ComplexRepresentation.{u} := by
  intro X _ μ _ ν hν
  let g := ν.rnDeriv μ
  have hg : Integrable g μ := ν.integrable_rnDeriv μ
  have hrep : μ.withDensityᵥ g = ν := complex_withDensity_rnDeriv μ ν hν
  have hsets (A : Set X) (hA : MeasurableSet A) :
      ν A = ∫ x in A, g x ∂μ := by
    rw [← hrep, withDensityᵥ_apply hg hA]
  have hmass : (∫⁻ x, ‖g x‖ₑ ∂μ) = ν.variation Set.univ := by
    rw [← hrep]
    exact variation_mass_withDensity μ hg
  refine ⟨g, ?_, hg, hsets, hmass, ?_, ?_⟩
  · have hr := Complex.continuous_ofReal.measurable.comp (ν.re.measurable_rnDeriv μ)
    have hi := Complex.continuous_ofReal.measurable.comp (ν.im.measurable_rnDeriv μ)
    have hm := hr.add (hi.mul_const Complex.I)
    convert hm using 1
    funext x
    exact (Complex.re_add_im (g x)).symm
  · rw [integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable, hmass]
    rfl
  · intro f hf hfsets
    exact Integrable.ae_eq_of_forall_setIntegral_eq f g hf hg
      (fun A hA _ => (hfsets A hA).symm.trans (hsets A hA))

theorem positive_radon_nikodym : RadonNikodymSpec.PositiveRepresentation.{u} := by
  intro X _ μ _ ν _ hν
  let g : X → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hfinite := Measure.rnDeriv_ne_top ν μ
  have hconvert : (fun x => ENNReal.ofReal (g x)) =ᵐ[μ] ν.rnDeriv μ := by
    filter_upwards [hfinite] with x hx
    exact ENNReal.ofReal_toReal hx
  have hrep : μ.withDensity (fun x => ENNReal.ofReal (g x)) = ν := by
    rw [withDensity_congr_ae hconvert, Measure.withDensity_rnDeriv_eq ν μ hν]
  refine ⟨g, (Measure.measurable_rnDeriv ν μ).ennreal_toReal,
    (fun _ => ENNReal.toReal_nonneg), hrep.symm, ?_⟩
  intro A hA
  rw [← hrep, withDensity_apply _ hA]

end ExpandedFA.FunctionSpaces
