import MathGenome.Internal.RealAnalysis.D11.Ch13.AveragesMaximalDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.MaximalNotL1
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
open Set MeasureTheory
open scoped ENNReal
namespace D11.Ch13.MaximalNotL1
open D11.Ch03 D11.Ch06 AveragesMaximalDefinition

private theorem native_coord_measurable : Measurable (fun y : Point 1 => y 0) :=
  (EuclideanSpace.proj 0).continuous.measurable

private theorem native_coord_preserving :
    MeasurePreserving (fun y : Point 1 => y 0) volume volume := by
  exact (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).comp
    (PiLp.volume_preserving_ofLp (Fin 1))

private theorem native_coord_lintegral (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y : Point 1, g (y 0)) = ∫⁻ x, g x :=
  native_coord_preserving.lintegral_comp hg

private theorem native_interval_measurable :
    MeasurableSet (closedBox (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1)) := by
  have h0 := measurableSet_le (measurable_const (a := (0 : ℝ))) native_coord_measurable
  have h1 := measurableSet_le native_coord_measurable (measurable_const (a := (1 : ℝ)))
  convert h0.inter h1 using 1
  ext y
  simp [closedBox]

local instance : MeasurableSpace (Point 1) := LebesgueMeasures.lebesgueSpace 1
local notation "μ" => LebesgueMeasures.lebesgue 1
local notation "I" => closedBox (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1)

def indicator : Point 1 → ℝ := (I).indicator 1

private theorem interval_measurable : MeasurableSet I :=
  LebesgueMeasures.native_borel_le 1 _ native_interval_measurable

private theorem indicator_measurable : Measurable indicator :=
  measurable_const.indicator interval_measurable

private theorem interval_measure : μ I = 1 := by
  change Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1 I = 1
  simpa [endpointBox, closedBox, boxContent] using
    LebesgueMeasures.lebesgue_box 1 (fun _ => 0) (fun _ => 1)
      (fun _ => true) (fun _ => true)

private theorem norm_indicator (y : Point 1) : ‖indicator y‖ = indicator y := by
  by_cases hy : y ∈ I <;> simp [indicator, hy]

private theorem indicator_integrable : Integrable indicator μ := by
  apply (integrable_indicator_iff interval_measurable).mpr
  exact integrableOn_const (C := (1 : ℝ)) (by rw [interval_measure]; exact ENNReal.one_ne_top)

theorem indicator_integrable_norm_one :
    D11.Ch06.ScalarIntegral.scalarIntegrable μ indicator ∧
    (∫ y, ‖indicator y‖ ∂μ) = 1 := by
  constructor
  · exact (ScalarIntegral.scalarIntegrable_iff _ _).mpr
      ⟨indicator_measurable, indicator_integrable⟩
  · simp_rw [norm_indicator]
    rw [indicator, integral_indicator_one interval_measurable]
    simp [Measure.real, interval_measure]

theorem indicator_locallyIntegrable : locallyIntegrable indicator := by
  apply (locallyIntegrable_iff _).mpr
  exact ⟨indicator_measurable, fun _ _ => indicator_integrable.integrableOn⟩

private theorem coord_dist (y z : Point 1) : dist y z = dist (y 0) (z 0) := by
  simp [EuclideanSpace.dist_eq]

private theorem ball_box (x r : ℝ) :
    Metric.ball (WithLp.toLp 2 (fun _ : Fin 1 => x)) r =
      openBox (fun _ => x - r) (fun _ => x + r) := by
  ext y
  simp only [Metric.mem_ball, coord_dist, Real.dist_eq,
    openBox, mem_ofPred_eq, Fin.forall_fin_one, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

private theorem ball_measure (x : ℝ) :
    μ (Metric.ball (WithLp.toLp 2 (fun _ : Fin 1 => x)) x) = ENNReal.ofReal (2 * x) := by
  rw [ball_box]
  change Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1 _ = _
  simpa [endpointBox, openBox, boxContent, sub_self, two_mul] using
    LebesgueMeasures.lebesgue_box 1 (fun _ => x - x) (fun _ => x + x)
      (fun _ => false) (fun _ => false)

private theorem interval_inter_ball (x : ℝ) (hx : 2 ≤ x) :
    I ∩ Metric.ball (WithLp.toLp 2 (fun _ : Fin 1 => x)) x =
      endpointBox (fun _ => 0) (fun _ => 1) (fun _ => false) (fun _ => true) := by
  rw [ball_box]
  ext y
  simp only [mem_inter_iff, closedBox, openBox, endpointBox, mem_ofPred_eq,
    Fin.forall_fin_one, Bool.false_eq_true, ite_false, ite_true, sub_self]
  constructor
  · rintro ⟨hI, hB⟩
    exact ⟨hB.1, hI.2⟩
  · intro h
    exact ⟨⟨h.1.le, h.2⟩, ⟨h.1, by linarith [h.2]⟩⟩

private theorem integral_ball (x : ℝ) (hx : 2 ≤ x) :
    (∫ y in Metric.ball (WithLp.toLp 2 (fun _ : Fin 1 => x)) x,
      ‖indicator y‖ ∂μ) = 1 := by
  simp_rw [norm_indicator]
  rw [indicator, integral_indicator_one interval_measurable, Measure.real,
    Measure.restrict_apply interval_measurable]
  rw [interval_inter_ball x hx]
  have h := LebesgueMeasures.lebesgue_box 1 (fun _ => 0) (fun _ => 1)
    (fun _ => false) (fun _ => true)
  simp only [boxContent, Fin.prod_univ_one, sub_zero, ENNReal.ofReal_one] at h
  have h' : μ (endpointBox (fun _ => 0) (fun _ => 1) (fun _ => false) (fun _ => true)) = 1 := h
  rw [h']
  simp

private theorem average_at_radius (hf : locallyIntegrable indicator) (x : ℝ) (hx : 2 ≤ x) :
    absoluteAverage indicator hf x (WithLp.toLp 2 (fun _ : Fin 1 => x)) = 1 / (2 * x) := by
  change (μ (Metric.ball (WithLp.toLp 2 (fun _ : Fin 1 => x)) x)).toReal⁻¹ *
    (∫ y in Metric.ball (WithLp.toLp 2 (fun _ : Fin 1 => x)) x, ‖indicator y‖ ∂μ) = _
  rw [ball_measure x, integral_ball x hx, ENNReal.toReal_ofReal (by linarith)]
  simp

theorem maximal_lower_bound (hf : locallyIntegrable indicator) (x : ℝ) (hx : 2 ≤ x) :
    ENNReal.ofReal (1 / (2 * x)) ≤
      maximal indicator hf (WithLp.toLp 2 (fun _ : Fin 1 => x)) := by
  rw [← average_at_radius hf x hx]
  exact le_iSup_of_le x (le_iSup_of_le (show 0 < x by linarith) le_rfl)

private theorem coord_lintegral (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g (y 0) ∂μ) = ∫⁻ x, g x := by
  calc
    _ = ∫⁻ y, g (y 0) ∂((μ).trim (LebesgueMeasures.native_borel_le 1)) :=
      (lintegral_trim (LebesgueMeasures.native_borel_le 1)
        (hg.comp native_coord_measurable)).symm
    _ = _ := by
      have ht : (μ).trim (LebesgueMeasures.native_borel_le 1) =
          LebesgueMeasures.borelMeasure 1 :=
        LebesgueMeasures.borel_restriction 1 (LebesgueMeasures.native_borel_le 1)
      rw [ht]
      exact native_coord_lintegral g hg

/-- A reciprocal tail whose integral diverges logarithmically. -/
private def reciprocalTail (x : ℝ) : ℝ :=
  (Ici (2 : ℝ)).indicator (fun t => 1 / (2 * t)) x

private theorem reciprocalTail_measurable : Measurable reciprocalTail :=
  (measurable_const.div (measurable_const.mul measurable_id)).indicator measurableSet_Ici

private theorem reciprocalTail_nonneg (x : ℝ) : 0 ≤ reciprocalTail x := by
  by_cases hx : x ∈ Ici (2 : ℝ)
  · simp only [reciprocalTail, indicator_of_mem hx]
    exact le_of_lt (by apply one_div_pos.mpr; have := hx; change 2 ≤ x at this; linarith)
  · simp [reciprocalTail, hx]

private theorem reciprocalTail_not_integrable : ¬ Integrable reciprocalTail := by
  intro h
  have htail : IntegrableOn (fun t : ℝ => 1 / (2 * t)) (Ici (2 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Ici).mp h
  apply not_integrableOn_Ici_inv (a := 2)
  have heq : (fun t : ℝ => 2 * (1 / (2 * t))) = fun t => t⁻¹ := by
    funext t
    simp [one_div, mul_inv_rev, mul_left_comm]
  exact heq ▸ htail.const_mul 2

private theorem reciprocalTail_integral_top :
    (∫⁻ x, ENNReal.ofReal (reciprocalTail x)) = ∞ := by
  by_contra h
  exact reciprocalTail_not_integrable
    ((lintegral_ofReal_ne_top_iff_integrable
      reciprocalTail_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall reciprocalTail_nonneg)).mp h)

theorem maximal_integral_top (hf : locallyIntegrable indicator) :
    (∫⁻ y, maximal indicator hf y ∂μ) = ∞ := by
  apply top_unique
  calc
    ∞ = ∫⁻ y, ENNReal.ofReal (reciprocalTail (y 0)) ∂μ := by
      exact ((coord_lintegral (fun x => ENNReal.ofReal (reciprocalTail x))
        (ENNReal.measurable_ofReal.comp reciprocalTail_measurable)).trans
          reciprocalTail_integral_top).symm
    _ ≤ _ := lintegral_mono fun y => by
      by_cases hy : 2 ≤ y 0
      · have h := maximal_lower_bound hf (y 0) hy
        have heq : WithLp.toLp 2 (fun _ : Fin 1 => y 0) = y := by
          ext i
          fin_cases i
          rfl
        simpa [reciprocalTail, hy, heq] using h
      · simp [reciprocalTail, hy]

end D11.Ch13.MaximalNotL1
