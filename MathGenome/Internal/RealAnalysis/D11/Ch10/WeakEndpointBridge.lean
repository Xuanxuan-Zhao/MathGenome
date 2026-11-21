import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.WeakEndpointBridge
import MathGenome.Internal.RealAnalysis.D11.Ch10.Chebyshev
import MathGenome.Internal.RealAnalysis.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch13.MaximalNotL1
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set MeasureTheory
open scoped ENNReal
universe u v
namespace D11.Ch10.WeakEndpointBridge

def weakNorm {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ) (g : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (α : ℝ) (_ : 0 < α), ENNReal.ofReal α * μ {x | ENNReal.ofReal α < g x} ^ (1 / p)

def scalarWeakNorm {X : Type u} {E : Type v} [MeasurableSpace X]
    [NormedAddCommGroup E] (μ : Measure X) (p : ℝ) (f : X → E) : ℝ≥0∞ :=
  weakNorm μ p (fun x => ENNReal.ofReal ‖f x‖)

theorem scalarWeakNorm_formula : Specs.D11.Ch10.WeakEndpointBridge.scalarWeakNorm_formula := by
  intro X E _ _ μ p f
  change (⨆ (α : ℝ) (_ : 0 < α), _) = _
  congr 1
  funext α
  congr 1
  funext hα
  have hlevel : {x | ENNReal.ofReal α < ENNReal.ofReal ‖f x‖} = {x | α < ‖f x‖} := by
    ext x
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα.le
  rw [hlevel]

theorem weak_le_powerNorm : Specs.D11.Ch10.WeakEndpointBridge.weak_le_powerNorm := by
  intro X E _ _ _ _ μ p f hp hf
  change Specs.D11.Ch10.WeakEndpointBridge.scalarWeakNorm_value μ p f ≤
    LpDefinition.powerNorm μ p f
  rw [scalarWeakNorm_formula]
  apply iSup₂_le
  intro α hα
  have hc := Chebyshev.chebyshev μ f p α hf hp hα
  have hr := ENNReal.rpow_le_rpow hc (one_div_pos.mpr hp).le
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hp).le,
    ← ENNReal.ofReal_rpow_of_nonneg hα.le hp.le, ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one] at hr
  exact hr

theorem weak_one_iff : Specs.D11.Ch10.WeakEndpointBridge.weak_one_iff := by
  intro X _ μ g C
  change (⨆ (α : ℝ) (_ : 0 < α), _) ≤ C ↔ _
  simp only [one_div_one, ENNReal.rpow_one, iSup_le_iff]
  apply forall_congr'
  intro α
  apply forall_congr'
  intro hα
  rw [mul_comm]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hα))
    (Or.inl ENNReal.ofReal_ne_top)).symm

open D11.Ch03 D11.Ch13 D11.Ch13.AveragesMaximalDefinition
open private norm_indicator interval_measure interval_measurable coord_dist ball_box
  from MathGenome.Internal.RealAnalysis.D11.Ch13.MaximalNotL1

local instance : MeasurableSpace (Point 1) := LebesgueMeasures.lebesgueSpace 1
local notation "μ" => LebesgueMeasures.lebesgue 1
local notation "I" => closedBox (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1)
local notation "f₀" => MaximalNotL1.indicator

private theorem line_ball_measure (y : Point 1) (r : ℝ) :
    μ (Metric.ball y r) = ENNReal.ofReal (2 * r) := by
  have hy : WithLp.toLp 2 (fun _ : Fin 1 => y 0) = y := by
    ext i
    fin_cases i
    rfl
  calc
    μ (Metric.ball y r) = boxContent (fun _ => y 0 - r) (fun _ => y 0 + r) := by
      rw [← hy, ball_box]
      exact LebesgueMeasures.lebesgue_box 1 _ _ (fun _ => false) (fun _ => false)
    _ = ENNReal.ofReal (2 * r) := by
      simp only [boxContent, Fin.prod_univ_one]
      congr 1
      ring

private theorem indicator_average (hf : locallyIntegrable f₀) (y : Point 1)
    (r : ℝ) (hr : 0 < r) :
    absoluteAverage f₀ hf r y = (μ (I ∩ Metric.ball y r)).toReal / (2 * r) := by
  change (μ (Metric.ball y r)).toReal⁻¹ * (∫ z in Metric.ball y r, ‖f₀ z‖ ∂μ) = _
  simp_rw [norm_indicator]
  rw [MaximalNotL1.indicator, integral_indicator_one interval_measurable,
    Measure.real, Measure.restrict_apply interval_measurable,
    line_ball_measure, ENNReal.toReal_ofReal (by positivity)]
  ring

private theorem indicator_average_le_one (hf : locallyIntegrable f₀) (y : Point 1)
    (r : ℝ) (hr : 0 < r) : absoluteAverage f₀ hf r y ≤ 1 := by
  rw [indicator_average hf y r hr, div_le_one (by positivity)]
  have h := ENNReal.toReal_mono ((ball_measure y r hr).2.1.ne)
    (measure_mono (inter_subset_right : I ∩ Metric.ball y r ⊆ Metric.ball y r))
  rwa [line_ball_measure, ENNReal.toReal_ofReal (by positivity)] at h

private theorem indicator_average_le_reciprocal (hf : locallyIntegrable f₀)
    (y : Point 1) (r : ℝ) (hr : 0 < r) :
    absoluteAverage f₀ hf r y ≤ 1 / (2 * r) := by
  rw [indicator_average hf y r hr]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h : μ (I ∩ Metric.ball y r) ≤ 1 := by
    rw [← interval_measure]
    exact measure_mono inter_subset_left
  simpa using ENNReal.toReal_mono (by simp) h

/-- Outside an enlarged unit interval, a small ball misses the indicator;
a large ball has small average because the total input integral is one. -/
private theorem maximal_le_outside (hf : locallyIntegrable f₀) (α : ℝ) (hα : 0 < α)
    (y : Point 1) (hy : y ∉ closedBox (fun _ => -(1 / α)) (fun _ => 1 + 1 / α)) :
    maximal f₀ hf y ≤ ENNReal.ofReal α := by
  apply iSup₂_le
  intro r hr
  apply ENNReal.ofReal_le_ofReal
  by_cases hrad : 1 / α ≤ r
  · apply (indicator_average_le_reciprocal hf y r hr).trans
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
    have hprod : 1 ≤ α * r := (div_le_iff₀ hα).mp hrad |>.trans_eq (mul_comm r α)
    nlinarith
  · have hrad' : r < 1 / α := lt_of_not_ge hrad
    have hempty : I ∩ Metric.ball y r = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hzI : 0 ≤ z 0 ∧ z 0 ≤ 1 := by
        simpa [closedBox] using hz.1
      have hdist : |z 0 - y 0| < r := by
        simpa only [Metric.mem_ball, coord_dist, Real.dist_eq] using hz.2
      have hy' : ¬ (-(1 / α) ≤ y 0 ∧ y 0 ≤ 1 + 1 / α) := by
        simpa [closedBox] using hy
      have ha := (abs_lt.mp hdist)
      exact hy' ⟨by linarith, by linarith⟩
    rw [indicator_average hf y r hr, hempty, measure_empty, ENNReal.toReal_zero, zero_div]
    exact hα.le

private theorem maximal_indicator_weak_bound (hf : locallyIntegrable f₀) :
    weakNorm μ 1 (maximal f₀ hf) ≤ 3 := by
  apply iSup₂_le
  intro α hα
  simp only [one_div_one, ENNReal.rpow_one]
  by_cases ha1 : α < 1
  · have hsub : {y | ENNReal.ofReal α < maximal f₀ hf y} ⊆
        closedBox (fun _ => -(1 / α)) (fun _ => 1 + 1 / α) := by
      intro y hy
      by_contra hy'
      exact (not_lt.mpr (maximal_le_outside hf α hα y hy')) hy
    have hmeasure : μ (closedBox (fun _ : Fin 1 => -(1 / α)) (fun _ => 1 + 1 / α)) =
        ENNReal.ofReal (1 + 2 / α) := by
      calc
        _ = boxContent (fun _ : Fin 1 => -(1 / α)) (fun _ => 1 + 1 / α) :=
          LebesgueMeasures.lebesgue_box 1 _ _ (fun _ => true) (fun _ => true)
        _ = _ := by
          simp only [boxContent, Fin.prod_univ_one]
          congr 1
          ring
    calc
      _ ≤ ENNReal.ofReal α * μ (closedBox (fun _ : Fin 1 => -(1 / α)) (fun _ => 1 + 1 / α))  := by
        have hm : μ {y | ENNReal.ofReal α < maximal f₀ hf y} ≤
            μ (closedBox (fun _ => -(1 / α)) (fun _ => 1 + 1 / α)) := measure_mono hsub
        exact mul_le_mul_of_nonneg_left hm (by positivity)
      _ = ENNReal.ofReal (α + 2) := by
        rw [hmeasure, ← ENNReal.ofReal_mul hα.le]
        congr 1
        field_simp
      _ ≤ 3 := by
        exact_mod_cast ENNReal.ofReal_le_ofReal (show α + 2 ≤ (3 : ℝ) by linarith)
  · have hempty : {y | ENNReal.ofReal α < maximal f₀ hf y} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hb : maximal f₀ hf y ≤ 1 := by
        apply iSup₂_le
        intro r hr
        exact (ENNReal.ofReal_le_ofReal (indicator_average_le_one hf y r hr)).trans_eq
          ENNReal.ofReal_one
      have ha : (1 : ℝ≥0∞) ≤ ENNReal.ofReal α := by
        simpa using ENNReal.ofReal_le_ofReal (le_of_not_gt ha1)
      exact (not_lt.mpr (hb.trans ha)) hy
    simp [hempty]

theorem maximal_endpoint_witness : Specs.D11.Ch10.WeakEndpointBridge.maximal_endpoint_witness := by
  obtain ⟨hint, hnorm⟩ := MaximalNotL1.indicator_integrable_norm_one
  refine ⟨hint, hnorm, MaximalNotL1.indicator_locallyIntegrable, ?_, ?_⟩
  · exact maximal_indicator_weak_bound MaximalNotL1.indicator_locallyIntegrable
  · exact MaximalNotL1.maximal_integral_top MaximalNotL1.indicator_locallyIntegrable

end D11.Ch10.WeakEndpointBridge
