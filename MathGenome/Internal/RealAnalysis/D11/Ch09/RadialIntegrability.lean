import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.RadialIntegrability
import MathGenome.Internal.RealAnalysis.D11.Ch09.PolarMeasure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace D11.Ch09.RadialIntegrability
open D11.Ch03 D11.Ch03.LebesgueMeasures
open Specs.D11.Ch03.LebesgueMeasures

/-- Completing Lebesgue measure does not change integrability of Borel functions,
also after restriction to a Borel set. -/
lemma integrableOn_lebesgue_iff_volume {n : ℕ} [NeZero n]
    {f : Point n → ℝ} (hf : Measurable f) {s : Set (Point n)} (hs : MeasurableSet s) :
    @IntegrableOn (Point n) ℝ (lebesgueSpace_value n) _ _ f s (lebesgue_value n) ↔
      IntegrableOn f s volume := by
  have hm := native_borel_le n
  have ht : ((lebesgue n).restrict s).trim hm = (volume : Measure (Point n)).restrict s := by
    rw [← restrict_trim hm _ hs, PolarMeasure.source_trim n]
  constructor
  · intro h
    have h' := h.trim hm hf.stronglyMeasurable
    change Integrable f (((lebesgue n).restrict s).trim hm) at h'
    rwa [ht] at h'
  · intro h
    change Integrable f (volume.restrict s) at h
    rw [← ht] at h
    exact integrable_of_integrable_trim hm h

lemma weighted_power (n : ℕ) [NeZero n] (α r : ℝ) (hr : 0 < r) :
    r ^ (Module.finrank ℝ (Point n) - 1) • r ^ (-α) = r ^ ((n : ℝ) - 1 - α) := by
  rw [smul_eq_mul, ← Real.rpow_natCast, ← Real.rpow_add hr]
  congr 1
  simp only [PolarMeasure.finrank_point, Nat.cast_pred (Nat.pos_of_ne_zero (NeZero.ne n))]
  ring

lemma near_native (n : ℕ) [NeZero n] (R α : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x : Point n => ‖x‖ ^ (-α)) {x | 0 < ‖x‖ ∧ ‖x‖ < R}
      volume ↔ α < (n : ℝ) := by
  have hs : {x : Point n | 0 < ‖x‖ ∧ ‖x‖ < R} =ᵐ[volume] ball 0 R := by
    filter_upwards [(volume : Measure (Point n)).ae_ne 0] with x hx
    simp [mem_ball, dist_zero_right, norm_pos_iff, hx]
  rw [integrableOn_congr_set_ae hs]
  rw [integrableOn_fun_norm_addHaar (E := Point n) volume (f := fun r : ℝ => r ^ (-α))]
  have heq : IntegrableOn (fun r : ℝ => r ^ (Module.finrank ℝ (Point n) - 1) • r ^ (-α))
      (Ioo 0 R) ↔ IntegrableOn (fun r : ℝ => r ^ ((n : ℝ) - 1 - α)) (Ioo 0 R) := by
    apply integrableOn_congr_fun _ measurableSet_Ioo
    intro r hr
    exact weighted_power n α r hr.1
  rw [heq, intervalIntegral.integrableOn_Ioo_rpow_iff hR]
  constructor <;> intro h <;> linarith

lemma exterior_native (n : ℕ) [NeZero n] (R α : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x : Point n => ‖x‖ ^ (-α)) {x | R < ‖x‖} volume ↔
      (n : ℝ) < α := by
  rw [← integrable_indicator_iff (measurableSet_lt measurable_const measurable_norm)]
  have hi : (fun x : Point n => {x | R < ‖x‖}.indicator (fun x => ‖x‖ ^ (-α)) x) =
      (fun x : Point n => (Ioi R).indicator (fun r : ℝ => r ^ (-α)) ‖x‖) := by
    funext x
    simp [indicator]
  change Integrable (fun x : Point n => {x | R < ‖x‖}.indicator (fun x => ‖x‖ ^ (-α)) x) volume ↔ _
  rw [hi, integrable_fun_norm_addHaar volume]
  have heq : IntegrableOn
      (fun r : ℝ => r ^ (Module.finrank ℝ (Point n) - 1) •
        (Ioi R).indicator (fun r : ℝ => r ^ (-α)) r) (Ioi 0) ↔
      IntegrableOn ((Ioi R).indicator (fun r : ℝ => r ^ ((n : ℝ) - 1 - α))) (Ioi 0) := by
    apply integrableOn_congr_fun _ measurableSet_Ioi
    intro r hr
    by_cases h : R < r
    · simp only [indicator_of_mem (show r ∈ Ioi R from h)]
      exact weighted_power n α r hr
    · simp [h]
  rw [heq, integrableOn_iff_integrable_of_support_subset]
  · rw [integrable_indicator_iff measurableSet_Ioi, integrableOn_Ioi_rpow_iff hR]
    constructor <;> intro h <;> linarith
  · intro r hr
    exact hR.trans (support_indicator_subset hr)

theorem near_integrable : Specs.D11.Ch09.RadialIntegrability.near_integrable := by
  intro n _ R α hR
  rw [integrableOn_lebesgue_iff_volume (measurable_norm.pow_const _) (by measurability)]
  exact near_native n R α hR

theorem exterior_integrable : Specs.D11.Ch09.RadialIntegrability.exterior_integrable := by
  intro n _ R α hR
  rw [integrableOn_lebesgue_iff_volume (measurable_norm.pow_const _) (by measurability)]
  exact exterior_native n R α hR

lemma power_measurable (n : ℕ) [NeZero n] (α : ℝ) :
    @Measurable (Point n) ℝ (lebesgueSpace_value n) inferInstance
      (fun x => ‖x‖ ^ (-α)) :=
  (measurable_norm.pow_const (-α)).mono (native_borel_le n) le_rfl

theorem near_threshold_infinite : Specs.D11.Ch09.RadialIntegrability.near_threshold_infinite := by
  intro n _ R hR
  let := lebesgueSpace_value n
  have hm := power_measurable n (n : ℝ)
  by_contra h
  have hi := (lintegral_ofReal_ne_top_iff_integrable
    hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x : Point n => Real.rpow_nonneg (norm_nonneg x) (-(n : ℝ))))).mp h
  exact (lt_irrefl (n : ℝ)) ((near_integrable n R (n : ℝ) hR).mp hi)

theorem exterior_threshold_infinite : Specs.D11.Ch09.RadialIntegrability.exterior_threshold_infinite := by
  intro n _ R hR
  let := lebesgueSpace_value n
  have hm := power_measurable n (n : ℝ)
  by_contra h
  have hi := (lintegral_ofReal_ne_top_iff_integrable
    hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x : Point n => Real.rpow_nonneg (norm_nonneg x) (-(n : ℝ))))).mp h
  exact (lt_irrefl (n : ℝ)) ((exterior_integrable n R (n : ℝ) hR).mp hi)

theorem angular_mass_pos_finite : Specs.D11.Ch09.RadialIntegrability.angular_mass_pos_finite := by
  intro n _
  change 0 < (volume : Measure (Point n)).toSphere univ ∧
    (volume : Measure (Point n)).toSphere univ < ∞
  exact ⟨(Measure.measure_univ_pos.mpr (Measure.toSphere_ne_zero volume)), measure_lt_top _ _⟩

end D11.Ch09.RadialIntegrability
