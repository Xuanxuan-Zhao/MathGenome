import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarUniqueness
import MathGenome.Internal.RealAnalysis.D11.Ch21.LchGroupInterface
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.ModularFunction

/-!
The modular function for the right-set convention on arbitrary LCH groups.
Right translation by a in the set argument is the pushforward by a⁻¹.
That pushforward is again left Haar, so the already proved uniqueness theorem
provides its unique finite positive real scalar. No countability assumptions
or right invariance of the original measure enter this argument.
-/
namespace D11.Ch21.ModularFunction

open Set MeasureTheory
open Specs.D11.Ch21.ModularFunction (IsModularFactor)
universe u
noncomputable section

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G
local instance {G : Type u} [TopologicalSpace G] : BorelSpace G := ⟨rfl⟩

/-- The Borel measure E ↦ μ(Ea). -/
def rightTranslatedMeasure {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (μ : @Measure G (borel G)) (a : G) :
    @Measure G (borel G) :=
  Specs.D11.Ch21.ModularFunction.rightTranslatedMeasure_value μ a

/-- The real modular function, with the source's right translation of sets. -/
def modularFunction {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (μ : @Measure G (borel G)) (a : G) : ℝ :=
  Specs.D11.Ch21.ModularFunction.modularFunction_value μ a

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

theorem rightTranslatedMeasure_apply (μ : @Measure G (borel G)) (a : G)
    (E : Set G) (hE : MeasurableSet E) :
    rightTranslatedMeasure μ a E = μ ((fun x => x * a) '' E) := by
  have hm : Measurable (fun x : G => x * a⁻¹) :=
    (continuous_id.mul_const _).measurable
  rw [rightTranslatedMeasure, Specs.D11.Ch21.ModularFunction.rightTranslatedMeasure_value,
    Measure.map_apply hm hE]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨x * a⁻¹, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

variable [T2Space G] [LocallyCompactSpace G]

theorem rightTranslatedMeasure_leftHaar (μ : @Measure G (borel G))
    (hμ : D11.Ch21.isLeftHaarMeasure μ) (a : G) :
    D11.Ch21.isLeftHaarMeasure (rightTranslatedMeasure μ a) := by
  have hm : Measurable (fun x : G => x * a⁻¹) :=
    (continuous_id.mul_const _).measurable
  refine ⟨?_, ?_, ?_⟩
  · exact (Measure.map_ne_zero_iff hm.aemeasurable).mpr hμ.1
  · let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ.2.1
    exact (D11.Ch18.isRadon_iff_regular _).mpr
      (Measure.Regular.map (Homeomorph.mulRight a⁻¹))
  · intro b E hE
    have hleft : MeasurableSet ((fun x => b * x) '' E) :=
      (Homeomorph.mulLeft b).toMeasurableEquiv.measurableSet_image.mpr hE
    rw [rightTranslatedMeasure_apply μ a _ hleft,
      rightTranslatedMeasure_apply μ a E hE]
    have he : (fun x => x * a) '' ((fun x => b * x) '' E) =
        (fun x => b * x) '' ((fun x => x * a) '' E) := by
      simp only [image_image, mul_assoc]
    rw [he]
    exact hμ.2.2 b _
      ((Homeomorph.mulRight a).toMeasurableEquiv.measurableSet_image.mpr hE)

/-- Setwise scalar equality is equality of the corresponding Borel measures. -/
lemma factor_iff_measure_eq (μ : @Measure G (borel G)) (a : G) (c : ℝ) :
    IsModularFactor μ a c ↔
      0 < c ∧ rightTranslatedMeasure μ a = ENNReal.ofReal c • μ := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, ?_⟩
    ext E hE
    rw [rightTranslatedMeasure_apply μ a E hE, Measure.smul_apply, smul_eq_mul]
    exact h E hE
  · rintro ⟨hc, h⟩
    refine ⟨hc, ?_⟩
    intro E hE
    rw [← rightTranslatedMeasure_apply μ a E hE, h, Measure.smul_apply, smul_eq_mul]

theorem scalar_exists_unique (μ : @Measure G (borel G))
    (hμ : D11.Ch21.isLeftHaarMeasure μ) (a : G) :
    ∃! c : ℝ, IsModularFactor μ a c := by
  obtain ⟨c, hc, hu⟩ := HaarUniqueness.left_uniqueness μ
    (rightTranslatedMeasure μ a) hμ (rightTranslatedMeasure_leftHaar μ hμ a)
  exact ⟨c, (factor_iff_measure_eq μ a c).mpr hc,
    fun d hd => hu d ((factor_iff_measure_eq μ a d).mp hd)⟩

/-- The infimum definition selects the unique factor, because its defining set
is exactly a singleton. -/
theorem modularFunction_spec (μ : @Measure G (borel G))
    (hμ : D11.Ch21.isLeftHaarMeasure μ) (a : G) :
    IsModularFactor μ a (modularFunction μ a) := by
  obtain ⟨c, hc, hu⟩ := scalar_exists_unique μ hμ a
  have hs : {d : ℝ | IsModularFactor μ a d} = {c} := by
    ext d
    change IsModularFactor μ a d ↔ d = c
    exact ⟨fun hd => hu d hd, fun hd => hd.symm ▸ hc⟩
  simpa only [modularFunction, Specs.D11.Ch21.ModularFunction.modularFunction_value,
    hs, csInf_singleton] using hc

theorem modularFunction_unique (μ : @Measure G (borel G))
    (hμ : D11.Ch21.isLeftHaarMeasure μ) (a : G) (c : ℝ)
    (hc : IsModularFactor μ a c) : c = modularFunction μ a :=
  (scalar_exists_unique μ hμ a).unique hc (modularFunction_spec μ hμ a)

/-- All left Haar measures, and therefore all their normalizations, give the
same modular scalar. Commuting scalar multiplication avoids infinite division. -/
theorem modularFunction_independent (μ ν : @Measure G (borel G))
    (hμ : D11.Ch21.isLeftHaarMeasure μ) (hν : D11.Ch21.isLeftHaarMeasure ν)
    (a : G) : modularFunction μ a = modularFunction ν a := by
  obtain ⟨d, ⟨hd, heq⟩, _⟩ := HaarUniqueness.left_uniqueness μ ν hμ hν
  apply modularFunction_unique ν hν a
  apply (factor_iff_measure_eq ν a _).mpr
  refine ⟨(modularFunction_spec μ hμ a).1, ?_⟩
  have hfactor := (factor_iff_measure_eq μ a _).mp (modularFunction_spec μ hμ a)
  rw [heq]
  change (ENNReal.ofReal d • μ).map (fun x => x * a⁻¹) = _
  have hm : Measurable (fun x : G => x * a⁻¹) :=
    (continuous_id.mul_const _).measurable
  rw [Measure.map_smul _ hm.aemeasurable]
  change ENNReal.ofReal d • rightTranslatedMeasure μ a = _
  rw [hfactor.2, smul_comm]

/-- Positive finite rescaling preserves the exact source Haar class. -/
lemma positive_smul_leftHaar (μ : @Measure G (borel G))
    (hμ : D11.Ch21.isLeftHaarMeasure μ) (c : ℝ) (hc : 0 < c) :
    D11.Ch21.isLeftHaarMeasure (ENNReal.ofReal c • μ) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ne_eq, Measure.ennreal_smul_eq_zero, not_or] using
      And.intro (ENNReal.ofReal_pos.mpr hc).ne' hμ.1
  · let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ.2.1
    exact (D11.Ch18.isRadon_iff_regular _).mpr
      (Measure.Regular.smul ENNReal.ofReal_ne_top)
  · intro b E hE
    simp only [Measure.smul_apply, hμ.2.2 b E hE]

theorem modularFunction_smul (μ : @Measure G (borel G))
    (hμ : D11.Ch21.isLeftHaarMeasure μ) (c : ℝ) (hc : 0 < c) (a : G) :
    modularFunction (ENNReal.ofReal c • μ) a = modularFunction μ a :=
  modularFunction_independent _ μ (positive_smul_leftHaar μ hμ c hc) hμ a

end
end D11.Ch21.ModularFunction
