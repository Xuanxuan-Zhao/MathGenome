import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.PairwiseBorelCantelliRatio
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.FirstBorelCantelli
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityObjects
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The second and quantitative assertions of Theorem 2.6 (paper.tex:627–670).
The square-threshold proof is Durrett, Probability: Theory and Examples,
5th edition, Theorem 2.3.9, pp. 71–72. Counts include `0, …, n`.
All sigma algebras and measures are the original canonical Mathlib objects. -/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityFoundations.Ch02
universe u

/-- Number of occurrences among the events with indices `0, …, n`. -/
noncomputable def occurrenceCount {Ω : Type u} (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (A k).indicator (fun _ => (1 : ℝ)) ω

/-- Sum of the event probabilities, represented as finite real numbers. -/
noncomputable def expectedOccurrenceCount {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ℕ → Set Ω) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (P (A k)).toReal

theorem expected_count_tendsto {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (hsum : (∑' n, P (A n)) = ∞) :
    Tendsto (expectedOccurrenceCount P A) atTop atTop := by
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  have h := (ENNReal.tendsto_nat_tsum (fun n => P (A n))).comp
    (tendsto_add_atTop_nat 1)
  rw [hsum] at h
  convert h using 1
  ext n
  simp only [expectedOccurrenceCount]
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
  simp [ENNReal.ofReal_toReal (measure_ne_top P _)]

theorem expected_count_eventually_positive {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (hsum : (∑' n, P (A n)) = ∞) :
    ∀ᶠ n in atTop, 0 < expectedOccurrenceCount P A n :=
  (expected_count_tendsto P A hsum).eventually (eventually_gt_atTop 0)

section Counts
variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))

omit [MeasurableSpace Ω] in
theorem occurrenceCount_nonneg (n : ℕ) (ω : Ω) : 0 ≤ occurrenceCount A n ω :=
  Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

omit [MeasurableSpace Ω] in
theorem occurrenceCount_mono (ω : Ω) : Monotone (fun n => occurrenceCount A n ω) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hij 1))
    (fun _ _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

omit [IsProbabilityMeasure P] in
theorem expectedOccurrenceCount_nonneg (n : ℕ) : 0 ≤ expectedOccurrenceCount P A n :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

omit [IsProbabilityMeasure P] in
theorem expectedOccurrenceCount_mono : Monotone (expectedOccurrenceCount P A) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hij 1))
    (fun _ _ _ => ENNReal.toReal_nonneg)

omit [IsProbabilityMeasure P] in
theorem expectedOccurrenceCount_succ (n : ℕ) :
    expectedOccurrenceCount P A (n + 1) = expectedOccurrenceCount P A n + (P (A (n + 1))).toReal :=
  Finset.sum_range_succ _ _

include hA in
theorem measurable_occurrenceCount (n : ℕ) : Measurable (occurrenceCount A n) := by
  apply Finset.measurable_sum
  intro k _
  exact measurable_const.indicator (hA k)

include hA in
theorem memLp_occurrenceCount (n : ℕ) : MemLp (occurrenceCount A n) 2 P := by
  apply MemLp.of_bound (measurable_occurrenceCount A hA n).aestronglyMeasurable (n + 1)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (occurrenceCount_nonneg A n ω)]
  calc
    occurrenceCount A n ω ≤ ∑ k ∈ Finset.range (n + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
    _ = n + 1 := by simp

include hA in
theorem integral_occurrenceCount (n : ℕ) :
    (∫ ω, occurrenceCount A n ω ∂P) = expectedOccurrenceCount P A n := by
  change (∫ ω, ∑ k ∈ Finset.range (n + 1), (A k).indicator (fun _ => (1 : ℝ)) ω ∂P) = _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    exact integral_indicator_one (hA k)
  · intro k _
    exact (integrable_const (1 : ℝ)).indicator (hA k)

include hA in
theorem variance_occurrenceCount_le (hind : PairwiseIndependentEvents P A) (n : ℕ) :
    variance (occurrenceCount A n) P ≤ expectedOccurrenceCount P A n := by
  have hi : ∀ k, MemLp ((A k).indicator (fun _ => (1 : ℝ))) 2 P := by
    intro k
    apply MemLp.of_bound (measurable_const.indicator (hA k)).aestronglyMeasurable 1
    filter_upwards [] with ω
    by_cases hω : ω ∈ A k <;> simp [hω]
  have hind' : Pairwise (fun i j => IndepFun ((A i).indicator (fun _ => (1 : ℝ)))
      ((A j).indicator (fun _ => (1 : ℝ))) P) := by
    intro i j hij
    apply (IndepFun_iff_Indep _ _ P).mpr
    apply indep_of_indep_of_le ((pairwiseIndependent_iff P _).mp hind hij)
    all_goals exact (measurable_const.indicator (MeasurableSpace.measurableSet_generateFrom
      (by simp))).comap_le
  have heq : occurrenceCount A n = ∑ k ∈ Finset.range (n + 1), (A k).indicator (fun _ => (1 : ℝ)) := by
    ext ω
    simp [occurrenceCount]
  rw [heq]
  rw [IndepFun.variance_sum (fun k _ => hi k) (fun i _ j _ hij => hind' hij)]
  apply Finset.sum_le_sum
  intro k _
  calc
    variance ((A k).indicator (fun _ => (1 : ℝ))) P ≤
        ∫ ω, ((A k).indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂P :=
      variance_le_expectation_sq (hi k).aestronglyMeasurable
    _ = (P (A k)).toReal := by
      convert integral_indicator_one (μ := P) (hA k) using 1
      congr 1
      ext ω
      by_cases hω : ω ∈ A k <;> simp [hω]
      rfl

end Counts

namespace RatioAux

/-- First crossing of the square threshold `(j+1)²`. -/
noncomputable def squareIndex (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (j : ℕ) : ℕ :=
  Nat.find ((ha.eventually (eventually_ge_atTop (((j : ℝ) + 1) ^ 2))).exists)

lemma squareIndex_lower (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (j : ℕ) :
    ((j : ℝ) + 1) ^ 2 ≤ a (squareIndex a ha j) := by
  unfold squareIndex
  exact Nat.find_spec ((ha.eventually (eventually_ge_atTop (((j : ℝ) + 1) ^ 2))).exists)

lemma squareIndex_mono (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    Monotone (squareIndex a ha) := by
  intro i j hij
  apply Nat.find_mono
  intro n hn
  exact le_trans (by gcongr) hn

lemma squareIndex_upper (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (h0 : a 0 ≤ 1) (hstep : ∀ n, a (n + 1) ≤ a n + 1) (j : ℕ) :
    a (squareIndex a ha j) ≤ ((j : ℝ) + 1) ^ 2 + 1 := by
  rcases h : squareIndex a ha j with _ | n
  · have hsq : 0 ≤ ((j : ℝ) + 1) ^ 2 := sq_nonneg _
    linarith
  · have hm : a n < ((j : ℝ) + 1) ^ 2 := by
      have hh : n < squareIndex a ha j := by omega
      exact lt_of_not_ge (Nat.find_min
        ((ha.eventually (eventually_ge_atTop (((j : ℝ) + 1) ^ 2))).exists) hh)
    exact (hstep n).trans (by linarith)

lemma squareIndex_pos (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (j : ℕ) :
    0 < a (squareIndex a ha j) :=
  (sq_pos_of_pos (by positivity)).trans_le (squareIndex_lower a ha j)

lemma squareIndex_tendsto (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (hmono : Monotone a) : Tendsto (squareIndex a ha) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hsq : Tendsto (fun j : ℕ => ((j : ℝ) + 1) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  filter_upwards [hsq.eventually (eventually_gt_atTop (a b))] with j hj
  by_contra! hh
  exact (not_lt_of_ge ((squareIndex_lower a ha j).trans (hmono hh.le))) hj

lemma squareIndex_scaled_tendsto (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (h0 : a 0 ≤ 1) (hstep : ∀ n, a (n + 1) ≤ a n + 1) :
    Tendsto (fun j : ℕ => a (squareIndex a ha j) / ((j : ℝ) + 1) ^ 2)
      atTop (𝓝 1) := by
  have hi : Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun j : ℕ => 1 + 1 / ((j : ℝ) + 1) ^ 2) atTop (𝓝 1) by
      simpa using tendsto_const_nhds.add hi)
  · intro j
    exact (le_div_iff₀ (by positivity)).2 (by simpa using squareIndex_lower a ha j)
  · intro j
    calc
      a (squareIndex a ha j) / ((j : ℝ) + 1) ^ 2 ≤
          (((j : ℝ) + 1) ^ 2 + 1) / ((j : ℝ) + 1) ^ 2 := by
        gcongr
        exact squareIndex_upper a ha h0 hstep j
      _ = 1 + 1 / ((j : ℝ) + 1) ^ 2 := by field_simp

lemma squareIndex_consecutive_ratio (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (h0 : a 0 ≤ 1) (hstep : ∀ n, a (n + 1) ≤ a n + 1) :
    Tendsto (fun j => a (squareIndex a ha (j + 1)) / a (squareIndex a ha j))
      atTop (𝓝 1) := by
  have hs := squareIndex_scaled_tendsto a ha h0 hstep
  have hr : Tendsto (fun j : ℕ => ((j : ℝ) + 2) / ((j : ℝ) + 1)) atTop (𝓝 1) := by
    have h : Tendsto (fun j : ℕ => (1 : ℝ) + 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop (R := ℝ))))
    convert (h : Tendsto (fun j : ℕ => (1 : ℝ) + 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 + 0))) using 1
    · ext j
      field_simp
      ring
    · norm_num
  have h := ((hs.comp (tendsto_add_atTop_nat 1)).mul (hr.pow 2)).div hs (by norm_num : (1 : ℝ) ≠ 0)
  simp only [one_pow, one_mul, div_self one_ne_zero] at h
  convert h using 1
  ext j
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hj' : (j : ℝ) + 2 ≠ 0 := by positivity
  have hp := (squareIndex_pos a ha j).ne'
  dsimp only [Pi.div_apply, Function.comp_apply]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [hj, hj', hp]
  ring

/-- Monotonicity interpolates a ratio limit along a sufficiently dense subsequence.
Repeated subsequence indices are allowed. -/
lemma tendsto_ratio_of_subsequence (a u : ℕ → ℝ) (t : ℕ → ℕ)
    (ha : Monotone a) (hu : Monotone u) (hu0 : ∀ n, 0 ≤ u n)
    (ht : Monotone t) (htop : Tendsto t atTop atTop)
    (hpos : ∀ j, 0 < a (t j))
    (hgrowth : Tendsto (fun j => a (t (j + 1)) / a (t j)) atTop (𝓝 1))
    (hsub : Tendsto (fun j => u (t j) / a (t j)) atTop (𝓝 1)) :
    Tendsto (fun n => u n / a n) atTop (𝓝 1) := by
  classical
  have ex (n : ℕ) : ∃ j, n < t j := (htop.eventually (eventually_gt_atTop n)).exists
  let b (n : ℕ) := Nat.find (ex n)
  have hb (n : ℕ) : n < t (b n) := Nat.find_spec (ex n)
  have hbtop : Tendsto b atTop atTop := by
    apply tendsto_atTop.2
    intro J
    filter_upwards [eventually_ge_atTop (t J)] with n hn
    by_contra! h
    exact (not_lt_of_ge ((ht h.le).trans hn)) (hb n)
  let k (n : ℕ) := b n - 1
  have hktop : Tendsto k atTop atTop := (tendsto_sub_atTop_nat 1).comp hbtop
  have hbounds : ∀ᶠ n in atTop, t (k n) ≤ n ∧ n < t (k n + 1) := by
    filter_upwards [hbtop.eventually (eventually_gt_atTop 0)] with n hn
    have hbk : b n - 1 + 1 = b n := by omega
    constructor
    · apply Nat.le_of_not_gt
      exact Nat.find_min (ex n) (show k n < b n by dsimp [k]; omega)
    · simpa [k, hbk] using hb n
  have hl : Tendsto (fun j => u (t j) / a (t (j + 1))) atTop (𝓝 1) := by
    have h := hsub.div hgrowth (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_self one_ne_zero] at h
    convert h using 1
    ext j
    dsimp only [Pi.div_apply, Function.comp_apply]
    field_simp [(hpos j).ne', (hpos (j + 1)).ne']
  have hr : Tendsto (fun j => u (t (j + 1)) / a (t j)) atTop (𝓝 1) := by
    have h := (hsub.comp (tendsto_add_atTop_nat 1)).mul hgrowth
    simp only [one_mul] at h
    convert h using 1
    ext j
    dsimp only [Pi.div_apply, Function.comp_apply]
    field_simp [(hpos j).ne', (hpos (j + 1)).ne']
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hl.comp hktop) (hr.comp hktop)
  · filter_upwards [hbounds] with n hn
    have hpn := (hpos (k n)).trans_le (ha hn.1)
    exact (div_le_div_of_nonneg_left (hu0 _) hpn (ha hn.2.le)).trans
      (div_le_div_of_nonneg_right (hu hn.1) hpn.le)
  · filter_upwards [hbounds] with n hn
    have hpn := (hpos (k n)).trans_le (ha hn.1)
    exact (div_le_div_of_nonneg_right (hu hn.2.le) hpn.le).trans
      (div_le_div_of_nonneg_left (hu0 _) (hpos _) (ha hn.1))

end RatioAux

section RatioLimit
variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
  (hind : PairwiseIndependentEvents P A)

include hA hind in
lemma normalized_count_deviation_bound (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (ha : 0 < expectedOccurrenceCount P A n) :
    P {ω | ε ≤ |occurrenceCount A n ω / expectedOccurrenceCount P A n - 1|} ≤
      ENNReal.ofReal (1 / (ε ^ 2 * expectedOccurrenceCount P A n)) := by
  have he : {ω | ε ≤ |occurrenceCount A n ω / expectedOccurrenceCount P A n - 1|} =
      {ω | ε * expectedOccurrenceCount P A n ≤
        |occurrenceCount A n ω - expectedOccurrenceCount P A n|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, div_sub_one ha.ne', abs_div, abs_of_pos ha,
      le_div_iff₀ ha]
  rw [he]
  have hc := meas_ge_le_variance_div_sq (memLp_occurrenceCount P A hA n) (mul_pos hε ha)
  rw [integral_occurrenceCount P A hA n] at hc
  refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    variance (occurrenceCount A n) P / (ε * expectedOccurrenceCount P A n) ^ 2 ≤
        expectedOccurrenceCount P A n / (ε * expectedOccurrenceCount P A n) ^ 2 :=
      div_le_div_of_nonneg_right (variance_occurrenceCount_le P A hA hind n) (sq_nonneg _)
    _ = 1 / (ε ^ 2 * expectedOccurrenceCount P A n) := by
      field_simp

include hA hind in
lemma ae_ratio_squareIndex (hsum : (∑' n, P (A n)) = ∞) :
    ∀ᵐ ω ∂P, Tendsto
      (fun j => occurrenceCount A (RatioAux.squareIndex (expectedOccurrenceCount P A)
          (expected_count_tendsto P A hsum) j) ω /
        expectedOccurrenceCount P A (RatioAux.squareIndex (expectedOccurrenceCount P A)
          (expected_count_tendsto P A hsum) j)) atTop (𝓝 1) := by
  let a := expectedOccurrenceCount P A
  have hatop : Tendsto a atTop atTop := expected_count_tendsto P A hsum
  let t := RatioAux.squareIndex a hatop
  have htpos (j : ℕ) : 0 < a (t j) := RatioAux.squareIndex_pos a hatop j
  have hbound (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
      P {ω | ε ≤ |occurrenceCount A (t j) ω / a (t j) - 1|} ≤
        ENNReal.ofReal (1 / (ε ^ 2 * ((j : ℝ) + 1) ^ 2)) := by
    refine (normalized_count_deviation_bound P A hA hind (t j) ε hε (htpos j)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    exact mul_le_mul_of_nonneg_left (RatioAux.squareIndex_lower a hatop j) (sq_nonneg ε)
  have hevent (ε : ℝ) (hε : 0 < ε) :
      ∀ᵐ ω ∂P, ∀ᶠ j in atTop, |occurrenceCount A (t j) ω / a (t j) - 1| < ε := by
    have hs : Summable (fun j : ℕ => 1 / (ε ^ 2 * ((j : ℝ) + 1) ^ 2)) := by
      have hp := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))).comp_injective
        (show Function.Injective (fun j : ℕ => j + 1) from fun _ _ h => Nat.add_right_cancel h)
      convert hp.mul_left (1 / ε ^ 2) using 1
      ext j
      dsimp only [Function.comp_apply]
      simp only [Nat.cast_add, Nat.cast_one]
      simp [div_eq_mul_inv, mul_comm]
    have hsum' : (∑' j, P {ω | ε ≤ |occurrenceCount A (t j) ω / a (t j) - 1|}) < ∞ :=
      (ENNReal.tsum_le_tsum (hbound ε hε)).trans_lt hs.tsum_ofReal_lt_top
    filter_upwards [ae_eventually_notMem hsum'.ne] with ω hω
    exact hω.mono (fun _ h => lt_of_not_ge h)
  obtain ⟨v, _, hvpos, hvlim⟩ :
      ∃ v : ℕ → ℝ, StrictAnti v ∧ (∀ i, 0 < v i) ∧ Tendsto v atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  filter_upwards [ae_all_iff.2 (fun i => hevent (v i) (hvpos i))] with ω hω
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨i, hi⟩ : ∃ i, v i < ε := ((tendsto_order.1 hvlim).2 ε hε).exists
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hω i)
  refine ⟨J, fun j hj => ?_⟩
  simpa only [Real.dist_eq] using (hJ j hj).trans hi

include hA hind in
/-- The source's mandatory quantitative conclusion, under pairwise independence. -/
theorem pairwise_borel_cantelli_ratio (hsum : (∑' n, P (A n)) = ∞) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => occurrenceCount A n ω / expectedOccurrenceCount P A n) atTop (𝓝 1) := by
  let a := expectedOccurrenceCount P A
  have hatop : Tendsto a atTop atTop := expected_count_tendsto P A hsum
  have h0 : a 0 ≤ 1 := by
    simpa only [a, expectedOccurrenceCount, Nat.zero_add, Finset.sum_range_one] using
      (show (P (A 0)).toReal ≤ 1 from measureReal_le_one)
  have hstep : ∀ n, a (n + 1) ≤ a n + 1 := by
    intro n
    change expectedOccurrenceCount P A (n + 1) ≤ expectedOccurrenceCount P A n + 1
    rw [expectedOccurrenceCount_succ]
    exact add_le_add le_rfl (show (P (A (n + 1))).toReal ≤ 1 from measureReal_le_one)
  filter_upwards [ae_ratio_squareIndex P A hA hind hsum] with ω hω
  exact RatioAux.tendsto_ratio_of_subsequence a (fun n => occurrenceCount A n ω)
    (RatioAux.squareIndex a hatop) (expectedOccurrenceCount_mono P A)
    (occurrenceCount_mono A ω) (fun n => occurrenceCount_nonneg A n ω)
    (RatioAux.squareIndex_mono a hatop)
    (RatioAux.squareIndex_tendsto a hatop (expectedOccurrenceCount_mono P A))
    (RatioAux.squareIndex_pos a hatop)
    (RatioAux.squareIndex_consecutive_ratio a hatop h0 hstep) hω

end RatioLimit

/-- Divergence of the normalized counts forces divergence of the counts. -/
lemma occurrenceCount_tendsto_of_ratio {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (hsum : (∑' n, P (A n)) = ∞) (ω : Ω)
    (hr : Tendsto (fun n => occurrenceCount A n ω / expectedOccurrenceCount P A n)
      atTop (𝓝 1)) : Tendsto (fun n => occurrenceCount A n ω) atTop atTop := by
  have h := hr.pos_mul_atTop zero_lt_one (expected_count_tendsto P A hsum)
  apply h.congr'
  filter_upwards [expected_count_eventually_positive P A hsum] with n hn
  exact div_mul_cancel₀ _ hn.ne'

lemma mem_infinitelyOftenEvent_of_count_tendsto {Ω : Type u} (A : ℕ → Set Ω) (ω : Ω)
    (hcount : Tendsto (fun n => occurrenceCount A n ω) atTop atTop) :
    ω ∈ infinitelyOftenEvent A := by
  classical
  by_contra h
  have hf := (not_mem_infinitelyOftenEvent_iff A ω).mp h
  have hb (n : ℕ) : occurrenceCount A n ω ≤ (hf.toFinset.card : ℝ) := by
    calc
      occurrenceCount A n ω =
          (((Finset.range (n + 1)).filter (fun k => ω ∈ A k)).card : ℝ) := by
        simp [occurrenceCount, Set.indicator, Finset.sum_boole]
      _ ≤ (hf.toFinset.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (show
          (Finset.range (n + 1)).filter (fun k => ω ∈ A k) ⊆ hf.toFinset by
            intro k hk
            exact hf.mem_toFinset.mpr (Finset.mem_filter.mp hk).2)
  obtain ⟨n, hn⟩ := (hcount.eventually (eventually_gt_atTop (hf.toFinset.card : ℝ))).exists
  exact (not_lt_of_ge (hb n)) hn

/-- The ratio limit, divergence, and infinitely many occurrences share one
measurable probability-one event, even for an incomplete probability space. -/
theorem common_probability_one_event {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n)) (hind : PairwiseIndependentEvents P A)
    (hsum : (∑' n, P (A n)) = ∞) :
    ∃ E : Set Ω, MeasurableSet E ∧ P E = 1 ∧ ∀ ω ∈ E,
      Tendsto (fun n => occurrenceCount A n ω / expectedOccurrenceCount P A n)
        atTop (𝓝 1) ∧
      Tendsto (fun n => occurrenceCount A n ω) atTop atTop ∧
      ω ∈ infinitelyOftenEvent A := by
  obtain ⟨E, hE, hEP, hEr⟩ :=
    (Ch01.almostSurely_iff_measurable_one P _).mp
      (pairwise_borel_cantelli_ratio P A hA hind hsum)
  refine ⟨E, hE, hEP, ?_⟩
  intro ω hω
  have hr := hEr ω hω
  have hc := occurrenceCount_tendsto_of_ratio P A hsum ω hr
  exact ⟨hr, hc, mem_infinitelyOftenEvent_of_count_tendsto A ω hc⟩

/-- Second Borel–Cantelli under pairwise independence. -/
theorem second_borel_cantelli {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n)) (hind : PairwiseIndependentEvents P A)
    (hsum : (∑' n, P (A n)) = ∞) : P (infinitelyOftenEvent A) = 1 := by
  obtain ⟨E, _, hEP, hE⟩ := common_probability_one_event P A hA hind hsum
  apply le_antisymm prob_le_one
  rw [← hEP]
  exact measure_mono (fun ω hω => (hE ω hω).2.2)

end ProbabilityFoundations.Ch02
