import MathGenome.Internal.RealAnalysis.D11.Ch21.ModularWeightRadon
import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarUniqueness
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.LeftRightDensity
import Mathlib.Tactic.Linarith

/-!
The weighted measure and the inversion pushforward are right Haar, hence
proportional. Inversion twice, and w(x)w(x⁻¹) = 1, force the positive scalar
c to satisfy c² = 1. This establishes the exact normalization without a
countable exhaustion, a product-measurability assumption or sigma-finiteness.
-/
namespace D11.Ch21.LeftRightDensity
open Set MeasureTheory
open scoped ENNReal Pointwise
open ModularWeightRadon HaarInversion
universe u
noncomputable section
local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G
local instance {G : Type u} [TopologicalSpace G] : BorelSpace G := ⟨rfl⟩

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- Inversion transports a density by composition with inversion. -/
lemma inversion_withDensity (μ : @Measure G (borel G)) (f : G → ℝ≥0∞) :
    (μ.withDensity f).inv = μ.inv.withDensity (fun x => f x⁻¹) := by
  ext E hE
  rw [Measure.inv_apply, withDensity_apply _ hE.inv,
    withDensity_apply _ hE, ← lintegral_indicator hE]
  change (∫⁻ x in E⁻¹, f x ∂μ) =
    ∫⁻ x, E.indicator (fun y => f y⁻¹) x ∂Measure.map (MeasurableEquiv.inv G) μ
  rw [lintegral_map_equiv, ← lintegral_indicator hE.inv]
  apply lintegral_congr
  intro x
  change (E⁻¹).indicator f x = E.indicator (fun y => f y⁻¹) x⁻¹
  by_cases hx : x⁻¹ ∈ E <;> simp [hx]

variable [T2Space G] [LocallyCompactSpace G]

lemma weight_inv (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) (x : G) :
    ENNReal.ofReal (weight μ x⁻¹) = (ENNReal.ofReal (weight μ x))⁻¹ := by
  change ENNReal.ofReal (ModularFunction.modularFunction μ (x⁻¹)⁻¹) = _
  rw [ModularProperties.map_inv μ hμ,
    ENNReal.ofReal_inv_of_pos (ModularProperties.positive μ hμ x⁻¹)]
  rfl

/-- Inverting the weighted measure cancels its reciprocal density. -/
lemma inversion_weightedMeasure (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ)
    (c : ℝ≥0∞) (hc : inversionMeasure μ = c • weightedMeasure μ) :
    inversionMeasure (weightedMeasure μ) = c • μ := by
  let f : G → ℝ≥0∞ := fun x => ENNReal.ofReal (weight μ x)
  have hf : Measurable f := (weight_properties μ hμ).1.measurable.ennreal_ofReal
  have hinv : (fun x => f x⁻¹) = fun x => (f x)⁻¹ :=
    funext (weight_inv μ hμ)
  change (μ.withDensity f).inv = c • μ
  rw [inversion_withDensity, hinv]
  change (inversionMeasure μ).withDensity (fun x => (f x)⁻¹) = _
  rw [hc, withDensity_smul_measure]
  change c • (μ.withDensity f).withDensity (fun x => (f x)⁻¹) = _
  rw [withDensity_inv_same hf
    (Filter.Eventually.of_forall (fun x =>
      (ENNReal.ofReal_pos.mpr ((weight_properties μ hμ).2 x)).ne'))
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top))]

theorem inversion_eq_weightedMeasure :
    Specs.D11.Ch21.LeftRightDensity.inversion_eq_weightedMeasure := by
  intro G _ _ _ _ _ μ hμ
  change inversionMeasure μ = weightedMeasure μ
  obtain ⟨c, ⟨hc, heq⟩, _⟩ := HaarUniqueness.right_uniqueness
    (weightedMeasure μ) (inversionMeasure μ)
    (weightedMeasure_rightHaar μ hμ) (rightHaar_inversionMeasure μ hμ)
  have hdouble := congrArg inversionMeasure heq
  rw [inversionMeasure_involutive, HaarUniqueness.inversionMeasure_smul,
    inversion_weightedMeasure μ hμ _ heq, smul_smul,
    ← ENNReal.ofReal_mul hc.le] at hdouble
  obtain ⟨d, _, hd⟩ := HaarUniqueness.left_uniqueness μ μ hμ hμ
  have hsq : c * c = 1 :=
    (hd (c * c) ⟨mul_pos hc hc, hdouble⟩).trans
      (hd 1 ⟨zero_lt_one, by simp⟩).symm
  have hc1 : c = 1 := by nlinarith
  simpa only [hc1, ENNReal.ofReal_one, one_smul] using heq

theorem density_formula : Specs.D11.Ch21.LeftRightDensity.density_formula := by
  intro G _ _ _ _ _ μ hμ E hE
  change inversionMeasure μ E =
    D11.Ch05.NonnegativeIntegral.nonnegativeIntegral
      (D11.Ch01.ExhaustionRestriction.restrictOnSpace μ E)
      (fun x => ENNReal.ofReal (weight μ x))
  have he : inversionMeasure μ = weightedMeasure μ := inversion_eq_weightedMeasure μ hμ
  rw [he, weightedMeasure_apply μ E hE]

theorem inversion_null_iff : Specs.D11.Ch21.LeftRightDensity.inversion_null_iff := by
  intro G _ _ _ _ _ μ hμ E _hE
  change inversionMeasure μ E = 0 ↔ μ E = 0
  have he : inversionMeasure μ = weightedMeasure μ := inversion_eq_weightedMeasure μ hμ
  rw [he]
  have hac : μ ≪ weightedMeasure μ :=
    withDensity_absolutelyContinuous'
      (weight_properties μ hμ).1.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall (fun x =>
        (ENNReal.ofReal_pos.mpr ((weight_properties μ hμ).2 x)).ne'))
  exact ⟨fun h => hac h, fun h => withDensity_absolutelyContinuous μ _ h⟩

theorem rightHaar_null_iff : Specs.D11.Ch21.LeftRightDensity.rightHaar_null_iff := by
  intro G _ _ _ _ _ μ ν hμ hν E hE
  obtain ⟨c, ⟨hc, heq⟩, _⟩ := HaarUniqueness.right_uniqueness
    (inversionMeasure μ) ν (rightHaar_inversionMeasure μ hμ) hν
  rw [heq, Measure.smul_apply, smul_eq_mul,
    mul_eq_zero, or_iff_right (ENNReal.ofReal_pos.mpr hc).ne']
  exact inversion_null_iff μ hμ E hE

theorem normalized_inversion_null_iff :
    Specs.D11.Ch21.LeftRightDensity.normalized_inversion_null_iff := by
  intro G _ _ _ _ _ μ hμ c hc E hE
  rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero,
    or_iff_right (ENNReal.ofReal_pos.mpr hc).ne']
  exact inversion_null_iff μ hμ E hE

end
end D11.Ch21.LeftRightDensity
