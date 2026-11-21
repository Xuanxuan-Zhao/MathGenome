import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.SpikesCounterexample
import MathGenome.Internal.RealAnalysis.D11.Ch17.UniformControls
import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace D11.Ch17.SpikesCounterexample
open D11.Ch17.UniformControls D11.Ch07.ConvergenceDefinitions D11.Ch03
local instance : MeasurableSpace Line :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1

lemma measurable_support (n : ℕ) : MeasurableSet (support n) := by
  apply D11.Ch03.LebesgueMeasures.borel_le_lebesgue 1
  simpa [support, openBox, endpointBox] using
    (D11.Ch03.LebesgueMeasures.endpointBox_borel 1 (fun _ => 0)
      (fun _ => 1 / ((n : ℝ) + 1)) (fun _ => false) (fun _ => false))

lemma support_subset_interval (n : ℕ) :
    support n ⊆ openBox (fun _ => 0) (fun _ => 1) := by
  intro x hx j
  refine ⟨(hx j).1, (hx j).2.trans_le ?_⟩
  exact (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr (by norm_cast; omega)

theorem support_measure (n : ℕ) :
    intervalMeasure (support n) = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  rw [intervalMeasure, Measure.restrict_apply (measurable_support n),
    inter_eq_left.mpr (support_subset_interval n)]
  change Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1
    (endpointBox (fun _ => 0) (fun _ => 1 / ((n : ℝ) + 1))
      (fun _ => false) (fun _ => false)) = _
  rw [D11.Ch03.LebesgueMeasures.lebesgue_box]
  simp [boxContent]

theorem support_measure_tendsto :
    Tendsto (fun n => intervalMeasure (support n)) atTop (𝓝 0) := by
  simp_rw [support_measure]
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using (ENNReal.tendsto_ofReal hlim)

theorem measurable_spike (n : ℕ) : Measurable (spike n) :=
  measurable_const.indicator (measurable_support n)

lemma norm_integrand (n : ℕ) :
    (fun x => ENNReal.ofReal ‖spike n x‖) =
      (support n).indicator (fun _ => ENNReal.ofReal ((n : ℝ) + 1)) := by
  funext x
  by_cases hx : x ∈ support n
  · simp [spike, hx, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  · simp [spike, hx]

lemma absolute_integral_one (n : ℕ) :
    absoluteIntegral intervalMeasure (spike n) univ = 1 := by
  rw [absoluteIntegral_formula, Measure.restrict_univ, norm_integrand,
    lintegral_indicator_const (measurable_support n), support_measure,
    ← ENNReal.ofReal_mul (by positivity)]
  simp [ne_of_gt (by positivity : (0 : ℝ) < n + 1)]

theorem integrable_spike (n : ℕ) :
    D11.Ch06.ScalarIntegral.scalarIntegrable intervalMeasure (spike n) := by
  refine ⟨measurable_spike n, ?_⟩
  have h : absoluteIntegral intervalMeasure (spike n) univ < ∞ := by
    rw [absolute_integral_one]
    exact ENNReal.one_lt_top
  simpa only [absoluteIntegral, Measure.restrict_univ] using h

theorem norm_one (n : ℕ) :
    D11.Ch10.LpDefinition.powerNorm intervalMeasure 1 (spike n) = 1 := by
  rw [← absoluteIntegral_eq_L1Norm]
  exact absolute_integral_one n

theorem support_integral_one (n : ℕ) :
    absoluteIntegral intervalMeasure (spike n) (support n) = 1 := by
  rw [absoluteIntegral_formula, norm_integrand,
    setLIntegral_indicator (measurable_support n), inter_self, setLIntegral_const,
    support_measure, ← ENNReal.ofReal_mul (by positivity)]
  simp [ne_of_gt (by positivity : (0 : ℝ) < n + 1)]

theorem uniformly_bounded : uniformL1Bound intervalMeasure spike := by
  refine ⟨integrable_spike, ?_⟩
  simp [integralSup, absolute_integral_one]

/-- Every positive point eventually lies to the right of the shrinking interval;
nonpositive points are outside every support from the start. -/
theorem pointwise_zero : pointwiseConverges spike (fun _ => 0) := by
  intro x
  apply tendsto_const_nhds.congr'
  by_cases hx : (0 : ℝ) < x 0
  · have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hlim.eventually_lt_const hx] with n hn
    have hout : x ∉ support n := fun h => ((h 0).2.trans hn).false
    simp [spike, hout]
  · exact Filter.Eventually.of_forall fun n => by
      have hout : x ∉ support n := fun h => hx (h 0).1
      simp [spike, hout]

theorem ae_zero : aeConverges intervalMeasure spike (fun _ => 0) :=
  D11.Ch04.AeCommonException.almostEverywhere_of_forall _ _ pointwise_zero

/-- Global deviation measures are bounded by the exact support measures. -/
theorem in_measure_zero : inMeasureConverges intervalMeasure spike (fun _ => 0) := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    support_measure_tendsto (fun _ => bot_le)
  intro n
  apply measure_mono
  intro x hx
  by_contra hout
  have hz : spike n x = 0 := by simp [spike, hout]
  have : ε < 0 := by simpa [deviationSet, hz] using hx
  exact (hε.trans this).false

theorem not_uiSmall : ¬ uiSmall intervalMeasure spike := by
  intro h
  obtain ⟨δ, hδ, hsmall⟩ := h.2 (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := (support_measure_tendsto.eventually_lt_const
    (ENNReal.ofReal_pos.mpr hδ)).exists
  have hlt := hsmall (support n) (measurable_support n) hn
  have hge : (1 : ℝ≥0∞) ≤ integralSup intervalMeasure spike (support n) := by
    rw [← support_integral_one n]
    exact le_iSup (fun i => absoluteIntegral intervalMeasure (spike i) (support n)) n
  have : (1 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) := hge.trans_lt hlt
  norm_num at this

theorem not_L1_zero : ¬ lpConverges intervalMeasure 1 spike (fun _ => 0) := by
  intro h
  have hlim := h.2.2.2
  have heq : (fun n => powerIntegral intervalMeasure 1
      (fun x => spike n x - (0 : ℝ))) = fun _ : ℕ => (1 : ℝ≥0∞) := by
    funext n
    simpa [powerIntegral, absoluteIntegral, Real.rpow_one] using absolute_integral_one n
  rw [heq] at hlim
  have : (1 : ℝ≥0∞) = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  exact one_ne_zero this

/-- Any proposed L1 limit must vanish a.e., since a subsequence converges a.e.
and the full sequence converges pointwise to zero. Its L1 error is then one. -/
theorem not_L1_converges (g : Line → ℝ) : ¬ lpConverges intervalMeasure 1 spike g := by
  intro h
  have hn : Tendsto (fun n => eLpNorm (spike n - g) 1 intervalMeasure) atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm (spike n - g) 1 intervalMeasure) =
        fun n => powerIntegral intervalMeasure 1 (fun x => spike n x - g x) := by
      funext n
      rw [eLpNorm_one_eq_lintegral_enorm
        ((measurable_spike n).sub h.2.1.1).aestronglyMeasurable,
        powerIntegral_eq_lintegral]
      simp only [Pi.sub_apply, Real.rpow_one, ofReal_norm]

    rw [heq]
    exact h.2.2.2
  obtain ⟨ns, hns, hsub⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) hn).exists_seq_tendsto_ae
  have hg : g =ᵐ[intervalMeasure] (fun _ => 0) := by
    filter_upwards [hsub] with x hx
    exact tendsto_nhds_unique hx ((pointwise_zero x).comp hns.tendsto_atTop)
  have heq : (fun n => powerIntegral intervalMeasure 1 (fun x => spike n x - g x)) =
      fun _ : ℕ => (1 : ℝ≥0∞) := by
    funext n
    calc
      powerIntegral intervalMeasure 1 (fun x => spike n x - g x) =
          absoluteIntegral intervalMeasure (spike n) univ := by
        rw [powerIntegral_eq_lintegral, absoluteIntegral_formula, Measure.restrict_univ]
        apply lintegral_congr_ae
        filter_upwards [hg] with x hx
        simp [hx]
      _ = 1 := absolute_integral_one n
  have hlim := h.2.2.2
  rw [heq] at hlim
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

end D11.Ch17.SpikesCounterexample
