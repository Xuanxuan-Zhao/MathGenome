import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.CantorDimension
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.CantorGeometry
import MathGenome.Internal.ODEDynamics.D13Unified.Ch18.CantorMeasureEstimate
import MathGenome.Internal.ODEDynamics.D13Unified.Ch18.MassDistribution
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.SplitIfs

/-! The dimension and critical Hausdorff measure of the canonical separated
Cantor set, paper.tex, Theorem d13:18:cantor-dimension. All Hausdorff quantities
are the upstream diameter-power quantities, without a normalization factor. -/

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace D13Unified.Ch18.CantorDimension
open D13Unified.Ch17.CantorGeometry
open D13Unified.Ch17.ShiftSpaces
open D13Unified.Ch18.CantorMeasureEstimate
open D13Unified.Ch18.HausdorffDefinitions

lemma critical_measure_lower (r : ℝ) (hr : 0 < r) (hrh : r < 1/2) :
    ENNReal.ofReal ((intervalConstant r)⁻¹) ≤
      hausdorffMeasure (exponent r) (cantorSet r) := by
  obtain ⟨hd, hC, hbound⟩ := interval_bound r hr hrh
  apply D13Unified.Ch18.MassDistribution.mass_distribution_supported
    (cantorSet r) (exponent r) (intervalConstant r) hd hC
    (cantorMeasure r) (probability r hr hrh) (supported r hr hrh)
  refine ⟨1, zero_lt_one, fun a b hab hlen => ?_⟩
  simpa only [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_rpow_of_nonneg
    (sub_nonneg.mpr hab) hd.le] using hbound a b hab hlen.le

/-- Pad a finite cover with empty sets to obtain an admissible countable cover. -/
lemma content_le_finite_cover {E : Set ℝ} {s δ : ℝ} (hs : 0 < s)
    {m : ℕ} (U : Fin m → Set ℝ) (hcover : E ⊆ ⋃ i, U i)
    (hdiam : ∀ i, ediam (U i) ≤ ENNReal.ofReal δ) :
    hausdorffContent s δ E ≤ ∑ i, (ediam (U i)) ^ s := by
  classical
  let V : ℕ → Set ℝ := fun j => if hj : j < m then U ⟨j, hj⟩ else ∅
  have hcover' : E ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i, by simpa [V, i.isLt] using hi⟩
  have hdiam' : ∀ j, ediam (V j) ≤ ENNReal.ofReal δ := by
    intro j
    dsimp [V]
    split_ifs with hj
    · exact hdiam ⟨j, hj⟩
    · simp
  change (⨅ (W : ℕ → Set ℝ) (_ : E ⊆ ⋃ i, W i)
    (_ : ∀ i, ediam (W i) ≤ ENNReal.ofReal δ), ∑' i, ediam (W i) ^ s) ≤ _
  refine iInf_le_of_le V (iInf_le_of_le hcover' (iInf_le_of_le hdiam' ?_))
  rw [tsum_eq_sum (s := Finset.range m) (fun j hj => by
    have hj' : ¬ j < m := by simpa using hj
    simp [V, hj', ENNReal.zero_rpow_of_pos hs])]
  have he : ∑ j ∈ Finset.range m, ediam (V j) ^ s = ∑ i : Fin m, ediam (U i) ^ s := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [V, i.isLt]
  exact he.le

lemma level_intervalCover (r : ℝ) (hr : 0 < r) (hrh : r < 1/2) (n : ℕ) :
    intervalCover (cantorSet r) (r^n) (2^n) := by
  classical
  have hc : Fintype.card (Fin n → Binary) = 2^n := by
    simp [Binary, Specs.D13Unified.Ch17.ShiftSpaces.Binary]
  let e : Fin (2^n) ≃ (Fin n → Binary) :=
    (finCongr hc).symm.trans (Fintype.equivFin _).symm
  refine ⟨fun i => wordMap r (e i) 0, fun i => wordMap r (e i) 1, ?_, ?_⟩
  · intro i
    have hl := levelInterval_length r hr hrh n (e i)
    constructor <;> linarith [pow_pos hr n]
  · intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp (level_cover r hr hrh n hx)
    exact mem_iUnion.mpr ⟨e.symm w, by simpa [levelInterval, Specs.D13Unified.Ch17.CantorGeometry.levelInterval] using hw⟩

lemma content_le_level (r : ℝ) (hr : 0 < r) (hrh : r < 1/2)
    (s : ℝ) (hs : 0 < s) (δ : ℝ) (n : ℕ) (hδ : r^n ≤ δ) :
    hausdorffContent s δ (cantorSet r) ≤ ENNReal.ofReal ((2 * r^s)^n) := by
  obtain ⟨a, b, hab, hcover⟩ := level_intervalCover r hr hrh n
  have h := content_le_finite_cover hs (fun i => Icc (a i) (b i)) hcover
    (fun i => by rw [Real.ediam_Icc]; exact ENNReal.ofReal_le_ofReal ((hab i).2.trans hδ))
  apply h.trans
  calc
    (∑ i : Fin (2^n), ediam (Icc (a i) (b i)) ^ s) ≤
        ∑ _i : Fin (2^n), (ENNReal.ofReal (r^n)) ^ s := by
      apply Finset.sum_le_sum
      intro i _
      apply ENNReal.rpow_le_rpow _ hs.le
      rw [Real.ediam_Icc]
      exact ENNReal.ofReal_le_ofReal (hab i).2
    _ = ENNReal.ofReal ((2 * r^s)^n) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hr.le _) hs.le]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← Real.rpow_natCast_mul hr.le, mul_comm (n : ℝ), Real.rpow_mul_natCast hr.le, mul_pow]
      norm_cast

lemma critical_measure_upper (r : ℝ) (hr : 0 < r) (hrh : r < 1/2) :
    hausdorffMeasure (exponent r) (cantorSet r) ≤ 1 := by
  have hd := exponent_pos hr hrh
  have hscale : r ^ exponent r = (1/2 : ℝ) := by
    simpa using scale_identity hr hrh 1
  change (⨆ (δ : ℝ) (_ : 0 < δ), hausdorffContent (exponent r) δ (cantorSet r)) ≤ 1
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (show r < 1 by linarith)
  simpa [hscale] using content_le_level r hr hrh (exponent r) hd δ n hn.le

lemma measure_zero_above (r : ℝ) (hr : 0 < r) (hrh : r < 1/2)
    (s : ℝ) (hs : exponent r < s) :
    hausdorffMeasure s (cantorSet r) = 0 := by
  have hd := exponent_pos hr hrh
  have hscale : r ^ exponent r = (1/2 : ℝ) := by
    simpa using scale_identity hr hrh 1
  have hq : 2 * r^s < 1 := by
    have := Real.rpow_lt_rpow_of_exponent_gt hr (show r < 1 by linarith) hs
    rw [hscale] at this
    linarith
  have ht := ENNReal.tendsto_ofReal
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show 0 ≤ 2 * r^s by positivity) hq)
  have hrpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le (show r < 1 by linarith)
  apply le_antisymm _ bot_le
  change (⨆ (δ : ℝ) (_ : 0 < δ), hausdorffContent s δ (cantorSet r)) ≤ 0
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  have hsmall : ∀ᶠ n : ℕ in atTop, r^n ≤ δ :=
    (hrpow.eventually (gt_mem_nhds hδ)).mono fun _ h => h.le
  have hb := hsmall.mono fun n hn => content_le_level r hr hrh s (hd.trans hs) δ n hn
  simpa using ge_of_tendsto ht hb

/-- The same probability also supplies a positive lower bound at every
positive exponent no larger than the critical exponent. -/
lemma measure_lower_below (r : ℝ) (hr : 0 < r) (hrh : r < 1/2)
    (s : ℝ) (hs : 0 < s) (hsd : s ≤ exponent r) :
    ENNReal.ofReal ((intervalConstant r)⁻¹) ≤ hausdorffMeasure s (cantorSet r) := by
  obtain ⟨hd, hC, hbound⟩ := interval_bound r hr hrh
  apply D13Unified.Ch18.MassDistribution.mass_distribution_supported
    (cantorSet r) s (intervalConstant r) hs hC
    (cantorMeasure r) (probability r hr hrh) (supported r hr hrh)
  refine ⟨1, zero_lt_one, fun a b hab hlen => ?_⟩
  have hp : (b-a)^exponent r ≤ (b-a)^s :=
    Real.rpow_le_rpow_of_exponent_ge' (sub_nonneg.mpr hab) hlen.le hs.le hsd
  calc
    _ ≤ ENNReal.ofReal (intervalConstant r * (b-a)^exponent r) := hbound a b hab hlen.le
    _ ≤ ENNReal.ofReal (intervalConstant r * (b-a)^s) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp hC.le)
    _ = _ := by rw [ENNReal.ofReal_mul hC.le,
      ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hab) hs.le]

lemma hausdorff_dimension (r : ℝ) (hr : 0 < r) (hrh : r < 1/2) :
    hausdorffDimension (cantorSet r) = ENNReal.ofReal (exponent r) := by
  have hd := exponent_pos hr hrh
  have hC := (interval_bound r hr hrh).2.1
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have hzero := measure_zero_above r hr hrh (exponent r + ε) (by linarith)
    have hb : hausdorffDimension (cantorSet r) ≤ ENNReal.ofReal (exponent r + ε) :=
      iInf_le_of_le (exponent r + ε) (iInf_le_of_le (by positivity)
        (iInf_le_of_le hzero le_rfl))
    simpa [ENNReal.ofReal_add hd.le (show 0 ≤ (ε : ℝ) by positivity)] using hb
  · change ENNReal.ofReal (exponent r) ≤
      ⨅ (s : ℝ) (_ : 0 < s) (_ : hausdorffMeasure s (cantorSet r) = 0), ENNReal.ofReal s
    refine le_iInf fun s => le_iInf fun hs => le_iInf fun hzero => ?_
    apply ENNReal.ofReal_le_ofReal
    by_contra h
    have hl := measure_lower_below r hr hrh s hs (le_of_not_ge h)
    rw [hzero] at hl
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hC))) hl

lemma cantor_nonempty (r : ℝ) : (cantorSet r).Nonempty :=
  range_nonempty (coding r)

lemma measure_cantor (r : ℝ) (hr : 0 < r) (hrh : r < 1/2) :
    cantorMeasure r (cantorSet r) = 1 := by
  let : IsProbabilityMeasure (cantorMeasure r) := probability r hr hrh
  apply le_antisymm prob_le_one
  simpa only [measure_univ, supported r hr hrh, add_zero] using
    (measure_univ_le_add_compl (μ := cantorMeasure r) (cantorSet r))

/-- Multiplicative covering-number bounds, valid through all positive meshes.
Using a product with `ε^d` avoids any convention about negative powers at zero. -/
lemma covering_number_bounds (r : ℝ) (hr : 0 < r) (hrh : r < 1/2)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let N : ℝ := ((intervalCoveringNumber (cantorSet r) ε).toNat : ℝ)
    0 < N ∧ 1 ≤ intervalConstant r * N * ε^exponent r ∧
      N * ε^exponent r ≤ 2 := by
  classical
  obtain ⟨n, hn, a, hmin⟩ :=
    intervalCoveringNumber_minimum (cantorSet r) (cantor_compact r hr hrh) ε hε
  change intervalCoveringNumber (cantorSet r) ε = (n : ℕ∞) at hn
  have hn0 : 0 < n := by
    have hp := (intervalCoveringNumber_positive (cantorSet r) (cantor_compact r hr hrh)
      (cantor_nonempty r) ε hε).1
    change 0 < intervalCoveringNumber (cantorSet r) ε at hp
    rw [hn] at hp
    exact_mod_cast hp
  change 0 < ((intervalCoveringNumber (cantorSet r) ε).toNat : ℝ) ∧ _
  rw [hn]
  simp only [ENat.toNat_natCast]
  have hd := exponent_pos hr hrh
  obtain ⟨_, hC, hbound⟩ := interval_bound r hr hrh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  refine ⟨hnR, ?_, ?_⟩
  · obtain ⟨a, b, hab, hcover⟩ := a
    have hmass : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((n : ℝ) *
        (intervalConstant r * ε^exponent r)) := by
      calc
        1 = cantorMeasure r (cantorSet r) := (measure_cantor r hr hrh).symm
        _ ≤ cantorMeasure r (⋃ i, Icc (a i) (b i)) := measure_mono hcover
        _ ≤ ∑ i, cantorMeasure r (Icc (a i) (b i)) := measure_iUnion_fintype_le _ _
        _ ≤ ∑ _i : Fin n, ENNReal.ofReal (intervalConstant r * ε^exponent r) := by
          apply Finset.sum_le_sum
          intro i _
          apply (hbound (a i) (b i) (hab i).1 ((hab i).2.trans hε1)).trans
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (sub_nonneg.mpr (hab i).1) (hab i).2 hd.le) hC.le
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hmass' : (1 : ℝ) ≤ (n : ℝ) * (intervalConstant r * ε^exponent r) := by
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (by simpa using hmass)
    nlinarith [hmass']
  · obtain ⟨k, hklo, hkhi⟩ :=
      exists_nat_pow_near_of_lt_one hε hε1 hr (show r < 1 by linarith)
    have hc : intervalCover (cantorSet r) ε (2^(k+1)) := by
      obtain ⟨a, b, hab, hcover⟩ := level_intervalCover r hr hrh (k+1)
      exact ⟨a, b, fun i => ⟨(hab i).1, (hab i).2.trans hklo.le⟩, hcover⟩
    have hnle : (n : ℝ) ≤ (2 : ℝ)^(k+1) := by exact_mod_cast hmin _ hc
    have hepow : ε^exponent r ≤ (1/2 : ℝ)^k := by
      rw [← scale_identity hr hrh k]
      exact Real.rpow_le_rpow hε.le hkhi hd.le
    calc
      (n : ℝ) * ε^exponent r ≤ 2^(k+1) * (1/2 : ℝ)^k :=
        mul_le_mul hnle hepow (by positivity) (by positivity)
      _ = 2 := by
        rw [pow_succ, mul_right_comm, ← mul_pow]
        norm_num

lemma box_ratio_bounds (r : ℝ) (hr : 0 < r) (hrh : r < 1/2)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    exponent r - Real.log (intervalConstant r) / Real.log (1/ε) ≤
        boxCountingRatio (cantorSet r) ε ∧
    boxCountingRatio (cantorSet r) ε ≤
        exponent r + Real.log 2 / Real.log (1/ε) := by
  obtain ⟨hN, hlo, hhi⟩ := covering_number_bounds r hr hrh ε hε hε1.le
  let N : ℝ := ((intervalCoveringNumber (cantorSet r) ε).toNat : ℝ)
  have hC := (interval_bound r hr hrh).2.1
  have hep : 0 < ε^exponent r := Real.rpow_pos_of_pos hε _
  have hl : 0 < Real.log (1/ε) := Real.log_pos ((one_lt_div hε).mpr hε1)
  have hloglo := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hlo
  have hloghi := Real.log_le_log (mul_pos hN hep) hhi
  have hlogeps : Real.log (1/ε) = -Real.log ε := by rw [one_div, Real.log_inv]
  rw [Real.log_one, Real.log_mul (mul_pos hC hN).ne' hep.ne',
    Real.log_mul hC.ne' hN.ne', Real.log_rpow hε] at hloglo
  rw [Real.log_mul hN.ne' hep.ne', Real.log_rpow hε] at hloghi
  have he : boxCountingRatio (cantorSet r) ε = Real.log N / Real.log (1/ε) := by
    change (if cantorSet r = ∅ then 0 else _) = _
    rw [ite_eq_right_iff.mpr (fun h => ((cantor_nonempty r).ne_empty h).elim)]
    rfl
  rw [he]
  constructor
  · apply (le_div_iff₀ hl).mpr
    rw [sub_mul, div_mul_cancel₀ _ hl.ne', hlogeps]
    linarith
  · apply (div_le_iff₀ hl).mpr
    rw [add_mul, div_mul_cancel₀ _ hl.ne', hlogeps]
    linarith

lemma box_dimension_limit (r : ℝ) (hr : 0 < r) (hrh : r < 1/2) :
    hasBoxDimension (cantorSet r) (exponent r) := by
  have hlog : Tendsto (fun ε : ℝ => Real.log (1/ε)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using
      Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hlo : Tendsto (fun ε : ℝ => exponent r -
      Real.log (intervalConstant r) / Real.log (1/ε)) (𝓝[>] 0) (𝓝 (exponent r)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hlog)
  have hhi : Tendsto (fun ε : ℝ => exponent r +
      Real.log 2 / Real.log (1/ε)) (𝓝[>] 0) (𝓝 (exponent r)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hlog)
  refine ⟨cantor_compact r hr hrh, tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_⟩
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
      with ε hε hε1
    exact (box_ratio_bounds r hr hrh ε hε hε1).1
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
      with ε hε hε1
    exact (box_ratio_bounds r hr hrh ε hε hε1).2

theorem cantor_dimension : Specs.D13Unified.Ch18.CantorDimension.cantor_dimensionStatement := by
  intro r hr hrh
  have hbox := box_dimension_limit r hr hrh
  have hC := (interval_bound r hr hrh).2.1
  refine ⟨hausdorff_dimension r hr hrh, hbox,
    (boxDimension_some_iff (cantorSet r) (exponent r)).mpr hbox, ?_, ?_⟩
  · exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hC)).trans_le (critical_measure_lower r hr hrh)
  · exact (critical_measure_upper r hr hrh).trans_lt (by simp)

theorem middle_thirds_dimension :
    Specs.D13Unified.Ch18.CantorDimension.middle_thirds_dimensionStatement := by
  have h := cantor_dimension (1/3) (by norm_num) (by norm_num)
  norm_num [Specs.D13Unified.Ch18.CantorMeasureEstimate.exponent] at h
  exact h

end D13Unified.Ch18.CantorDimension
