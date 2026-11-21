import MathGenome.Internal.RealAnalysis.D11.Ch21.ModularFunction
import MathGenome.Internal.RealAnalysis.D11.Ch21.CompactTranslateIntegralContinuity
import MathGenome.Internal.RealAnalysis.D11.Ch09.TransportNonnegative
import MathGenome.Internal.RealAnalysis.D11.Ch09.TransportIntegrable
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.ModularProperties
import Batteries.Tactic.OpenPrivate

/-!
The modular function on arbitrary Hausdorff locally compact groups, using
the right-set convention μ(Ea) = Δ(a) μ(E). Uniqueness of the positive real
factor gives the algebraic laws. Pushforward transport gives both integral
formulas, including integrability of the scalar translate. A fixed nonzero
nonnegative Cc test expresses Δ as a quotient of a continuous translate
integral by a positive constant, proving continuity in the full topology.
-/
namespace D11.Ch21.ModularProperties

open Set MeasureTheory
open scoped ENNReal
open D11.Ch21.ModularFunction
open D11.Ch06.ScalarIntegral
open D11.Ch05.NonnegativeIntegral
universe u
noncomputable section

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G
local instance {G : Type u} [TopologicalSpace G] : BorelSpace G := ⟨rfl⟩

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

theorem positive (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) (a : G) :
    0 < modularFunction μ a := (modularFunction_spec μ hμ a).1

theorem map_one (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) :
    modularFunction μ 1 = 1 := by
  symm
  apply modularFunction_unique μ hμ
  refine ⟨zero_lt_one, ?_⟩
  intro E hE
  simp

theorem map_mul (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) (a b : G) :
    modularFunction μ (a * b) = modularFunction μ a * modularFunction μ b := by
  symm
  apply modularFunction_unique μ hμ
  refine ⟨mul_pos (positive μ hμ a) (positive μ hμ b), ?_⟩
  intro E hE
  have hEa : MeasurableSet ((fun x => x * a) '' E) :=
    (Homeomorph.mulRight a).toMeasurableEquiv.measurableSet_image.mpr hE
  have he : (fun x => x * (a * b)) '' E =
      (fun x => x * b) '' ((fun x => x * a) '' E) := by
    simp only [image_image, mul_assoc]
  rw [he, (modularFunction_spec μ hμ b).2 _ hEa,
    (modularFunction_spec μ hμ a).2 E hE,
    ENNReal.ofReal_mul (positive μ hμ a).le]
  ac_rfl

theorem map_inv (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) (a : G) :
    modularFunction μ a⁻¹ = (modularFunction μ a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul μ hμ, inv_mul_cancel, map_one μ hμ]

theorem nonnegative_translation (μ : @Measure G (borel G))
    (hμ : isLeftHaarMeasure μ) (a : G) (f : G → ℝ≥0∞) (hf : Measurable f) :
    nonnegativeIntegral μ (fun x => f (x * a⁻¹)) =
      ENNReal.ofReal (modularFunction μ a) * nonnegativeIntegral μ f := by
  have hm : Measurable (fun x : G => x * a⁻¹) :=
    (continuous_id.mul_const _).measurable
  have he := ((factor_iff_measure_eq μ a _).mp (modularFunction_spec μ hμ a)).2
  simp only [integral_eq_lintegral]
  rw [← lintegral_map hf hm]
  change (∫⁻ x, f x ∂rightTranslatedMeasure μ a) = _
  rw [he, lintegral_smul_measure, smul_eq_mul]

theorem scalar_translation {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) (a : G) (f : G → 𝕜)
    (hf : scalarIntegrable μ f) :
    ∃ ht : scalarIntegrable μ (fun x => f (x * a⁻¹)),
      scalarIntegral μ (fun x => f (x * a⁻¹)) ht =
        modularFunction μ a • scalarIntegral μ f hf := by
  have hm : Measurable (fun x : G => x * a⁻¹) :=
    (continuous_id.mul_const _).measurable
  have he := ((factor_iff_measure_eq μ a _).mp (modularFunction_spec μ hμ a)).2
  have hfi := ((scalarIntegrable_iff μ f).mp hf).2
  have hmap : Integrable f (rightTranslatedMeasure μ a) := by
    rw [he]
    exact hfi.smul_measure ENNReal.ofReal_ne_top
  refine ⟨(scalarIntegrable_iff μ _).mpr ⟨hf.1.comp hm, hmap.comp_measurable hm⟩, ?_⟩
  change (∫ x, f (x * a⁻¹) ∂μ) = modularFunction μ a • ∫ x, f x ∂μ
  rw [← integral_map hm.aemeasurable hf.1.aestronglyMeasurable]
  change (∫ x, f x ∂rightTranslatedMeasure μ a) = _
  rw [he, integral_smul_measure, ENNReal.toReal_ofReal (positive μ hμ a).le]

open private positive_test from MathGenome.Internal.RealAnalysis.D11.Ch21.HaarUniqueness

theorem continuous (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) :
    Continuous (modularFunction μ) := by
  obtain ⟨g, hg, hne⟩ := positive_test (G := G)
  obtain ⟨hgi, hpos⟩ := HaarPositiveOpen.integral_pos μ (Or.inl hμ) g hg hne
  have he (a : G) : modularFunction μ a =
      (∫ x, g (x * a⁻¹) ∂μ) / (∫ x, g x ∂μ) := by
    have h := (scalar_translation μ hμ a (fun x => g x) hgi).choose_spec
    change (∫ x, g (x * a⁻¹) ∂μ) = modularFunction μ a * (∫ x, g x ∂μ) at h
    exact (eq_div_iff hpos.ne').mpr h.symm
  have hfun : modularFunction μ =
      (fun a => (∫ x, g (x * a⁻¹) ∂μ) / (∫ x, g x ∂μ)) := funext he
  rw [hfun]
  exact ((CompactTranslateIntegralContinuity.continuous_translate_integral μ hμ.2.1 g).comp
    continuous_inv).div_const _

end
end D11.Ch21.ModularProperties
