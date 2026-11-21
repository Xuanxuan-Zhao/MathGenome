import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.SpikingPaths
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ContinuousPathConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open MeasureTheory Filter Topology Set

namespace ProbabilityFoundations.Ch06
noncomputable section
open SpikeSpec

/-- The triangular paths of the example (with the source's positive indices). -/
def triangularSpike : SpikeSpec.spikeType := SpikeSpec.spikeValue

private theorem width_pos (n : ℕ) : 0 < width n := by
  unfold width
  positivity

private theorem width_le_half {n : ℕ} (hn : 1 ≤ n) : width n ≤ 1 / 2 := by
  simpa [width] using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hn

private theorem tent_bounds (n : ℕ) (t : ℝ) : 0 ≤ tent n t ∧ tent n t ≤ 1 := by
  change 0 ≤ max 0 _ ∧ max 0 _ ≤ 1
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  by_cases h : t / width n ≤ 3 / 2
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

private theorem tent_outside (n : ℕ) (t : ℝ)
    (ht : t ≤ width n ∨ 2 * width n ≤ t) : tent n t = 0 := by
  change max 0 _ = 0
  apply max_eq_left
  rcases ht with ht | ht
  · exact (min_le_left _ _).trans (by
      have := (div_le_one (width_pos n)).mpr ht
      linarith)
  · exact (min_le_right _ _).trans (by
      have := (le_div_iff₀ (width_pos n)).mpr ht
      linarith)

private theorem tent_left (n : ℕ) (t : ℝ)
    (h₁ : width n ≤ t) (h₂ : t ≤ 3 * width n / 2) :
    tent n t = 2 * (t / width n - 1) := by
  have ha := width_pos n
  have hlow : 1 ≤ t / width n := (le_div_iff₀ ha).mpr (by simpa using h₁)
  have hhigh : t / width n ≤ 3 / 2 := (div_le_iff₀ ha).mpr (by linarith)
  change max 0 _ = _
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

private theorem tent_right (n : ℕ) (t : ℝ)
    (h₁ : 3 * width n / 2 ≤ t) (h₂ : t ≤ 2 * width n) :
    tent n t = 2 * (2 - t / width n) := by
  have ha := width_pos n
  have hlow : 3 / 2 ≤ t / width n := (le_div_iff₀ ha).mpr (by linarith)
  have hhigh : t / width n ≤ 2 := (div_le_iff₀ ha).mpr (by linarith)
  change max 0 _ = _
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

private theorem tent_peak (n : ℕ) : tent n (3 * width n / 2) = 1 := by
  rw [tent_left n _ (by have := width_pos n; linarith) le_rfl]
  field_simp [ne_of_gt (width_pos n)]
  norm_num

theorem triangularSpike_shape : SpikeSpec.shapeType := by
  intro n _hn
  refine ⟨tent_bounds n, tent_outside n, tent_left n, tent_right n,
    tent_outside n _ (Or.inl le_rfl), tent_outside n _ (Or.inr le_rfl), tent_peak n⟩

private theorem widths_tendsto_zero : Tendsto width atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- At each positive time the moving support eventually lies to its left;
at zero every spike vanishes. -/
theorem triangularSpike_pointwise : SpikeSpec.pointwiseType := by
  intro t
  by_cases ht : (t : ℝ) = 0
  · have hz (n : ℕ) : spikeValue (n + 1) t = 0 := by
      exact tent_outside _ _ (Or.inl (by rw [ht]; exact (width_pos _).le))
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have hw : Tendsto (fun n : ℕ => 2 * width (n + 1)) atTop (𝓝 0) := by
      simpa using (widths_tendsto_zero.comp (tendsto_add_atTop_nat 1)).const_mul 2
    apply tendsto_congr' _ |>.mpr tendsto_const_nhds
    filter_upwards [hw.eventually (gt_mem_nhds htpos)] with n hn
    exact tent_outside _ _ (Or.inr hn.le)

private def peakTime (n : ℕ) (hn : 1 ≤ n) : UnitTime :=
  ⟨3 * width n / 2, by
    have ha := width_pos n
    have hb := width_le_half hn
    constructor <;> linarith⟩

private def leftTime (n : ℕ) (hn : 1 ≤ n) : UnitTime :=
  ⟨width n, (width_pos n).le, (width_le_half hn).trans (by norm_num)⟩

theorem triangularSpike_norm : SpikeSpec.normType := by
  intro n hn
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro t
    change ‖tent n (t : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (tent_bounds n t).1]
    exact (tent_bounds n t).2
  · have h := (spikeValue n).norm_coe_le_norm (peakTime n hn)
    change ‖tent n (3 * width n / 2)‖ ≤ _ at h
    simpa only [tent_peak, norm_one] using h

private theorem diracLaw_tendsto {S : Type*} [TopologicalSpace S] [T1Space S]
    [MeasurableSpace S] [BorelSpace S] {x : ℕ → S} {y : S}
    (h : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => diracLaw (x n)) atTop (𝓝 (diracLaw y)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simpa [diracLaw, Function.comp_def] using f.continuous.continuousAt.tendsto.comp h

private theorem diracLaw_map {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]
    (x : S) (f : S → V) (hf : Measurable f) :
    (diracLaw x).map f = diracLaw (f x) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.map_dirac' hf x

theorem triangularSpike_finiteDimensional : SpikeSpec.finiteDimensionalType := by
  intro k t
  change Tendsto (fun n : ℕ => (diracLaw (spikeValue (n + 1))).map
    (fun x : RealPath => fun i : Fin k => x (t i))) atTop
    (𝓝 (diracLaw (fun _ : Fin k => (0 : ℝ))))
  have hc : Continuous (fun x : RealPath => fun i : Fin k => x (t i)) :=
    continuous_pi fun i => continuous_eval_const (t i)
  have hx : Tendsto (fun n : ℕ => fun i : Fin k => spikeValue (n + 1) (t i))
      atTop (𝓝 (fun _ : Fin k => (0 : ℝ))) :=
    tendsto_pi_nhds.mpr fun i => triangularSpike_pointwise (t i)
  simpa only [← diracLaw_map _ _ hc.measurable] using diracLaw_tendsto hx

private theorem increment_le_one (n : ℕ) (s t : UnitTime) :
    ‖spikeValue n s - spikeValue n t‖ ≤ 1 := by
  have hs := tent_bounds n s
  have ht := tent_bounds n t
  change |tent n (s : ℝ) - tent n (t : ℝ)| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem modulus_eq_one {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : width n / 2 ≤ δ) : realModulus (spikeValue n) δ = 1 := by
  have hbound : BddAbove (realIncrements (spikeValue n) δ) := by
    refine ⟨1, ?_⟩
    rintro r ⟨s, t, _, rfl⟩
    exact increment_le_one n s t
  have hone : 1 ∈ realIncrements (spikeValue n) δ := by
    refine ⟨peakTime n hn, leftTime n hn, ?_, ?_⟩
    · change |3 * width n / 2 - width n| ≤ δ
      rw [abs_of_nonneg (by have := width_pos n; linarith)]
      linarith
    · change 1 = ‖tent n (3 * width n / 2) - tent n (width n)‖
      rw [tent_peak, tent_outside n _ (Or.inl le_rfl)]
      norm_num
  apply le_antisymm
  · apply csSup_le ⟨1, hone⟩
    rintro r ⟨s, t, _, rfl⟩
    exact increment_le_one n s t
  · exact le_csSup hbound hone

theorem triangularSpike_modulus : SpikeSpec.modulusType := by
  intro δ hδ
  have hw : Tendsto (fun n : ℕ => width (n + 1) / 2) atTop (𝓝 0) := by
    simpa using (widths_tendsto_zero.comp (tendsto_add_atTop_nat 1)).div_const 2
  filter_upwards [hw.eventually (gt_mem_nhds hδ)] with n hn
  exact modulus_eq_one (Nat.succ_le_succ (Nat.zero_le n)) hn.le

/-- No compact subset of the uniform path space contains every spike. -/
private theorem spikes_not_in_compact (K : Set RealPath) (hK : IsCompact K)
    (hmem : ∀ n : ℕ, spikeValue (n + 1) ∈ K) : False := by
  obtain ⟨x, hx, φ, hφ, hconv⟩ := hK.tendsto_subseq hmem
  have hxzero : x = 0 := by
    ext t
    have h₁ := (continuous_eval_const t).continuousAt.tendsto.comp hconv
    have h₂ := (triangularSpike_pointwise t).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h₁ h₂
  have hnorm := continuous_norm.continuousAt.tendsto.comp hconv
  change Tendsto (fun n => ‖spikeValue (φ n + 1)‖) atTop (𝓝 ‖x‖) at hnorm
  have hnorms (n : ℕ) : ‖spikeValue (φ n + 1)‖ = 1 :=
    triangularSpike_norm _ (Nat.succ_le_succ (Nat.zero_le _))
  have hlim : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, hnorms, hxzero, norm_zero] using hnorm
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  norm_num at this

theorem triangularSpike_not_uniformlyTight : SpikeSpec.notTightType := by
  intro ht
  change UniformlyTight (range (fun n : ℕ => diracLaw (spikeValue (n + 1)))) at ht
  obtain ⟨K, hK, hbound⟩ := (uniformlyTight_iff _).mp ht 1 zero_lt_one
  apply spikes_not_in_compact K hK
  intro n
  by_contra hn
  have h := hbound (diracLaw (spikeValue (n + 1))) (mem_range_self n)
  have hmass : (diracLaw (spikeValue (n + 1)) : Measure RealPath) Kᶜ = 1 :=
    Measure.dirac_apply_of_mem hn
  rw [hmass] at h
  simp at h

/-- A weakly convergent sequence of laws on this Polish path space is
uniformly tight, which the explicit spikes contradict. -/
theorem triangularSpike_noWeakLimit : SpikeSpec.noWeakLimitType := by
  intro μ h
  exact triangularSpike_not_uniformlyTight (uniformlyTight_range_of_converges _ μ h)

end
end ProbabilityFoundations.Ch06
