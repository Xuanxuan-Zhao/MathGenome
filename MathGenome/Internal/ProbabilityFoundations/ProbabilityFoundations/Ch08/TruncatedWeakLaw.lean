import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.TruncatedWeakLaw
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.ConvergenceComparisons
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open MeasureTheory Filter ProbabilityTheory Function
open scoped ENNReal Topology

universe u
namespace ProbabilityFoundations.Ch08
open Specs.ProbabilityFoundations.Ch08.TruncatedWeakLaw
open Specs.ProbabilityFoundations.Ch08.VarianceWeakLaw

/-- Reindexing the source's sums by 1, …, n as Mathlib's sums over range n. -/
theorem partialSum_eq_sum_range {Ω : Type u} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum X n ω = ∑ k ∈ Finset.range n, X (k + 1) ω := by
  classical
  unfold partialSum
  refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
  · intro k hk
    have := Finset.mem_Icc.mp hk
    simp only [Finset.mem_range]
    omega
  · intro i hi j hj hij
    have := Finset.mem_Icc.mp hi
    have := Finset.mem_Icc.mp hj
    omega
  · intro k hk
    refine ⟨k + 1, ?_, by omega⟩
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro k hk
    have := (Finset.mem_Icc.mp hk).1
    congr 1
    omega

/-- The finite-first-moment conclusion retains only pairwise independence.
Mathlib's Lp and a.e. strong laws both have precisely this hypothesis. -/
theorem integrable_weak_law : integrableWeakLawType := by
  intro Ω mΩ P hP X hXm hind hid hint
  let Y : ℕ → Ω → ℝ := fun k => X (k + 1)
  have hYind : Pairwise ((· ⟂ᵢ[P] ·) on Y) := by
    intro i j hij
    exact hind (i + 1) (j + 1) (by omega) (by omega) (by omega)
  have hYid (k : ℕ) : IdentDistrib (Y k) (Y 0) P P := hid (k + 1) (by omega)
  have havg (n : ℕ) : sampleAverage X n =
      fun ω => (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Y k ω := by
    ext ω
    rw [sampleAverage, partialSum_eq_sum_range]
    simp [Y, div_eq_inv_mul]
  have havg_apply (n : ℕ) (ω : Ω) : sampleAverage X n ω =
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Y k ω := congrFun (havg n) ω
  have hmeas (n : ℕ) : Measurable (sampleAverage X n) := by
    rw [havg]
    exact (Finset.measurable_sum _ (fun k _ => hXm (k + 1) (by omega))).const_smul ((n : ℝ)⁻¹)
  have hintX (k : ℕ) (hk : 1 ≤ k) : Integrable (X k) P :=
    (hid k hk).integrable_iff.mpr hint
  have hintAvg (n : ℕ) : Integrable (sampleAverage X n) P := by
    exact (integrable_finsetSum _ (fun k hk =>
      hintX k (Finset.mem_Icc.mp hk).1)).div_const _
  refine ⟨hintAvg, integrable_const _, ?_, ?_⟩
  · apply ProbabilityFoundations.Ch02.almostSure_implies_probability P
      (sampleAverage X) _ hmeas measurable_const
    have h := strong_law_ae Y hint hYind hYid
    simpa only [← havg_apply] using h
  · have h := strong_law_Lp (p := 1) le_rfl (by simp) Y
      (memLp_one_iff_integrable.mpr hint) hYind hYid
    simp_rw [← havg_apply] at h
    have hreal := ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞) |>.comp h
    simp only [Function.comp_def, ENNReal.toReal_zero] at hreal
    convert hreal using 1
    ext n
    change (∫ ω, |sampleAverage X n ω - ∫ t, X 1 t ∂P| ∂P) =
      (eLpNorm (sampleAverage X n - fun _ => ∫ t, X 1 t ∂P) 1 P).toReal
    rw [eLpNorm_one_eq_lintegral_enorm
      ((hintAvg n).sub (integrable_const (∫ t, X 1 t ∂P))).aestronglyMeasurable]
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      (integral_norm_eq_lintegral_enorm
        ((hintAvg n).sub (integrable_const (∫ t, X 1 t ∂P))).aestronglyMeasurable)

section Truncation
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma measurable_symmetricTruncation {X : Ω → ℝ} (hX : Measurable X) (a : ℝ) :
    Measurable (symmetricTruncation X a) :=
  hX.indicator (measurableSet_le (by simpa only [Real.norm_eq_abs] using hX.norm) measurable_const)

omit [MeasurableSpace Ω] in
lemma abs_symmetricTruncation_le {X : Ω → ℝ} {a : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    |symmetricTruncation X a ω| ≤ a := by
  classical
  by_cases h : |X ω| ≤ a
  · simp [symmetricTruncation, h]
  · simpa [symmetricTruncation, h] using ha

lemma memLp_symmetricTruncation {X : Ω → ℝ} (hX : Measurable X)
    {a : ℝ} (ha : 0 ≤ a) (p : ℝ≥0∞) : MemLp (symmetricTruncation X a) p P := by
  apply MemLp.of_bound (measurable_symmetricTruncation hX a).aestronglyMeasurable a
  exact ae_of_all P fun ω => by
    simpa only [Real.norm_eq_abs] using abs_symmetricTruncation_le ha ω

omit [MeasurableSpace Ω] in
lemma symmetricTruncation_comp (X : Ω → ℝ) (a : ℝ) :
    symmetricTruncation X a = symmetricTruncation id a ∘ X := rfl

/-- A discrete layer-cake upper bound, valid also at integer atoms. -/
lemma min_sq_le_tail_sum (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (min x (n : ℝ)) ^ 2 ≤
      ∑ k ∈ Finset.range n, if (k : ℝ) < x then 2 * (k : ℝ) + 1 else 0 := by
  induction n with
  | zero => simp [min_eq_right hx]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    by_cases hxn : x ≤ (n : ℝ)
    · rw [min_eq_left hxn, min_eq_left (by linarith : x ≤ (n : ℝ) + 1)] at *
      exact ih.trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
    · have hnx : (n : ℝ) < x := lt_of_not_ge hxn
      rw [min_eq_right hnx.le] at ih
      rw [ite_eq_left hnx]
      have hmin0 : 0 ≤ min x ((n : ℝ) + 1) := le_min hx (by positivity)
      have hmin1 : min x ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := min_le_right _ _
      nlinarith [sq_nonneg (min x ((n : ℝ) + 1) - ((n : ℝ) + 1))]

omit [MeasurableSpace Ω] in
lemma sq_symmetricTruncation_le_tail_sum (X : Ω → ℝ) (n : ℕ) (ω : Ω) :
    symmetricTruncation X (n : ℝ) ω ^ 2 ≤
      ∑ k ∈ Finset.range n,
        {ω | (k : ℝ) < |X ω|}.indicator (fun _ => 2 * (k : ℝ) + 1) ω := by
  classical
  have h := min_sq_le_tail_sum |X ω| (abs_nonneg _) n
  simp only [Set.indicator_apply, Set.mem_ofPred_eq] at *
  refine le_trans ?_ h
  by_cases hx : |X ω| ≤ (n : ℝ)
  · simp [symmetricTruncation, hx, sq_abs]
  · simp [symmetricTruncation, hx]

/-- Integrating the finite discrete layer cake needs no moment assumption on X. -/
lemma integral_sq_symmetricTruncation_le (X : Ω → ℝ) (hX : Measurable X) (n : ℕ) :
    (∫ ω, symmetricTruncation X (n : ℝ) ω ^ 2 ∂P) ≤
      ∑ k ∈ Finset.range n, (2 * (k : ℝ) + 1) * P.real {ω | (k : ℝ) < |X ω|} := by
  have hm (k : ℕ) : MeasurableSet {ω | (k : ℝ) < |X ω|} :=
    measurableSet_lt measurable_const (by simpa only [Real.norm_eq_abs] using hX.norm)
  have hi (k : ℕ) : Integrable
      ({ω | (k : ℝ) < |X ω|}.indicator (fun _ => 2 * (k : ℝ) + 1)) P :=
    (integrable_const _).indicator (hm k)
  calc
    _ ≤ ∫ ω, ∑ k ∈ Finset.range n,
        {ω | (k : ℝ) < |X ω|}.indicator (fun _ => 2 * (k : ℝ) + 1) ω ∂P := by
      apply integral_mono
      · exact (memLp_symmetricTruncation hX (by positivity) 2).integrable_sq
      · exact integrable_finsetSum _ (fun k _ => hi k)
      · exact sq_symmetricTruncation_le_tail_sum X n
    _ = _ := by
      rw [integral_finsetSum _ (fun k _ => hi k)]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_indicator_const _ (hm k), smul_eq_mul, mul_comm]

/-- The integer tail criterion forces the normalized truncated second moment to vanish. -/
lemma truncated_second_moment_tendsto (X : Ω → ℝ) (hX : Measurable X)
    (htail : Tendsto (fun n : ℕ => (n : ℝ) * P.real {ω | (n : ℝ) < |X ω|})
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∫ ω, symmetricTruncation X (n : ℝ) ω ^ 2 ∂P) / (n : ℝ))
      atTop (𝓝 0) := by
  have hterm : Tendsto
      (fun n : ℕ => (2 * (n : ℝ) + 1) * P.real {ω | (n : ℝ) < |X ω|})
      atTop (𝓝 0) := by
    have hu := htail.const_mul 3
    simp only [mul_zero] at hu
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hu
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp := @measureReal_nonneg Ω _ P {ω | (n : ℝ) < |X ω|}
    nlinarith
  have hc := hterm.cesaro
  apply squeeze_zero (fun n => by positivity) ?_ hc
  intro n
  simpa only [div_eq_inv_mul] using
    mul_le_mul_of_nonneg_left (integral_sq_symmetricTruncation_le X hX n)
      (by positivity : 0 ≤ (n : ℝ)⁻¹)

omit [IsProbabilityMeasure P] in
/-- The expectation of an iid sample average uses only equality of marginal laws. -/
lemma integral_sampleAverage_eq (X : ℕ → Ω → ℝ)
    (hX : ∀ k, 1 ≤ k → Integrable (X k) P)
    (hid : ∀ k, 1 ≤ k → IdentDistrib (X k) (X 1) P P)
    (n : ℕ) (hn : 1 ≤ n) :
    (∫ ω, sampleAverage X n ω ∂P) = ∫ ω, X 1 ω ∂P := by
  have hsum : (∫ ω, partialSum X n ω ∂P) = (n : ℝ) * ∫ ω, X 1 ω ∂P := by
    unfold partialSum
    rw [integral_finsetSum _ (fun k hk => hX k (Finset.mem_Icc.mp hk).1)]
    calc
      _ = ∑ k ∈ Finset.Icc 1 n, ∫ ω, X 1 ω ∂P := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hid k (Finset.mem_Icc.mp hk).1).integral_eq
      _ = _ := by simp
  change (∫ ω, partialSum X n ω / (n : ℝ) ∂P) = _
  rw [integral_div, hsum]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

omit [IsProbabilityMeasure P] in
/-- The variance of an iid average requires pairwise independence only. -/
lemma variance_sampleAverage_eq (X : ℕ → Ω → ℝ)
    (hX : ∀ k, 1 ≤ k → MemLp (X k) 2 P)
    (hind : ∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → IndepFun (X i) (X j) P)
    (hid : ∀ k, 1 ≤ k → IdentDistrib (X k) (X 1) P P)
    (n : ℕ) (hn : 1 ≤ n) :
    variance (sampleAverage X n) P = variance (X 1) P / (n : ℝ) := by
  have hsum : variance (partialSum X n) P = (n : ℝ) * variance (X 1) P := by
    have h := IndepFun.variance_sum (s := Finset.Icc 1 n)
      (fun k hk => hX k (Finset.mem_Icc.mp hk).1)
      (fun i hi j hj hij => hind i j
        (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hij)
    have hfun : (∑ i ∈ Finset.Icc 1 n, X i) = partialSum X n := by
      ext ω
      simp only [Finset.sum_apply, partialSum]
    rw [hfun] at h
    rw [h]
    calc
      _ = ∑ k ∈ Finset.Icc 1 n, variance (X 1) P := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hid k (Finset.mem_Icc.mp hk).1).variance_eq
      _ = _ := by simp
  change variance (fun ω => partialSum X n ω / (n : ℝ)) P = _
  simp only [div_eq_inv_mul]
  rw [variance_const_mul, hsum]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

omit [IsProbabilityMeasure P] in
lemma identDistrib_symmetricTruncation {X Y : Ω → ℝ}
    (h : IdentDistrib X Y P P) (a : ℝ) :
    IdentDistrib (symmetricTruncation X a) (symmetricTruncation Y a) P P := by
  simpa only [← symmetricTruncation_comp] using
    h.comp (measurable_symmetricTruncation measurable_id a)

omit [IsProbabilityMeasure P] in
lemma indepFun_symmetricTruncation {X Y : Ω → ℝ}
    (h : IndepFun X Y P) (a : ℝ) :
    IndepFun (symmetricTruncation X a) (symmetricTruncation Y a) P := by
  simpa only [← symmetricTruncation_comp] using
    h.comp (measurable_symmetricTruncation measurable_id a)
      (measurable_symmetricTruncation measurable_id a)

/-- Chebyshev's row estimate, centered at the actual closed-cutoff mean. -/
lemma truncated_deviation_bound (X : ℕ → Ω → ℝ)
    (hX : ∀ k, 1 ≤ k → Measurable (X k))
    (hind : ∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → IndepFun (X i) (X j) P)
    (hid : ∀ k, 1 ≤ k → IdentDistrib (X k) (X 1) P P)
    (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | ε ≤ |sampleAverage (fun k => symmetricTruncation (X k) (n : ℝ)) n ω -
      truncatedMean P (X 1) n|} ≤
      ((∫ ω, symmetricTruncation (X 1) (n : ℝ) ω ^ 2 ∂P) / (n : ℝ)) / ε ^ 2 := by
  let Y : ℕ → Ω → ℝ := fun k => symmetricTruncation (X k) (n : ℝ)
  have hY (k : ℕ) (hk : 1 ≤ k) : MemLp (Y k) 2 P :=
    memLp_symmetricTruncation (hX k hk) (by positivity) 2
  have hYi (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≠ j) :
      IndepFun (Y i) (Y j) P := indepFun_symmetricTruncation (hind i j hi hj hij) _
  have hYd (k : ℕ) (hk : 1 ≤ k) : IdentDistrib (Y k) (Y 1) P P :=
    identDistrib_symmetricTruncation (hid k hk) _
  have hAvg : MemLp (sampleAverage Y n) 2 P := by
    change MemLp (fun ω => partialSum Y n ω / (n : ℝ)) 2 P
    simpa only [div_eq_inv_mul, partialSum] using
      (memLp_finsetSum (Finset.Icc 1 n)
        (fun k hk => hY k (Finset.mem_Icc.mp hk).1)).const_mul ((n : ℝ)⁻¹)
  have hc := meas_ge_le_variance_div_sq hAvg hε
  rw [integral_sampleAverage_eq Y (fun k hk => (hY k hk).integrable (by norm_num)) hYd n hn,
    variance_sampleAverage_eq Y hY hYi hYd n hn] at hc
  have hv : variance (Y 1) P ≤ ∫ ω, Y 1 ω ^ 2 ∂P :=
    variance_le_expectation_sq (hY 1 le_rfl).aestronglyMeasurable
  have hb := ENNReal.toReal_mono (by finiteness) hc
  rw [ENNReal.toReal_ofReal
    (div_nonneg (div_nonneg (variance_nonneg _ _) (by positivity)) (sq_nonneg _))] at hb
  change P.real {ω | ε ≤ |sampleAverage Y n ω - ∫ t, Y 1 t ∂P|} ≤ _
  apply hb.trans
  gcongr

/-- If truncation changes an average, at least one of its n summands exceeds n. -/
lemma average_truncation_change_bound (X : ℕ → Ω → ℝ)
    (hid : ∀ k, 1 ≤ k → IdentDistrib (X k) (X 1) P P) (n : ℕ) :
    P.real {ω | sampleAverage X n ω ≠
      sampleAverage (fun k => symmetricTruncation (X k) (n : ℝ)) n ω} ≤
      (n : ℝ) * P.real {ω | (n : ℝ) < |X 1 ω|} := by
  classical
  have hsub : {ω | sampleAverage X n ω ≠
      sampleAverage (fun k => symmetricTruncation (X k) (n : ℝ)) n ω} ⊆
      ⋃ k ∈ Finset.Icc 1 n, {ω | (n : ℝ) < |X k ω|} := by
    intro ω hω
    by_contra hn
    apply hω
    have hle (k : ℕ) (hk : k ∈ Finset.Icc 1 n) : |X k ω| ≤ (n : ℝ) := by
      by_contra hk'
      apply hn
      exact Set.mem_iUnion₂.mpr ⟨k, hk, lt_of_not_ge hk'⟩
    unfold sampleAverage partialSum
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    simp [symmetricTruncation, hle k hk]
  calc
    _ ≤ P.real (⋃ k ∈ Finset.Icc 1 n, {ω | (n : ℝ) < |X k ω|}) :=
      measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ k ∈ Finset.Icc 1 n, P.real {ω | (n : ℝ) < |X k ω|} :=
      measureReal_biUnion_finset_le _ _
    _ = _ := by
      have hm : MeasurableSet {x : ℝ | (n : ℝ) < |x|} := by
        simpa only [Real.norm_eq_abs] using
          (measurableSet_lt measurable_const measurable_id.norm :
            MeasurableSet {x : ℝ | (n : ℝ) < ‖x‖})
      have heq (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
          P.real {ω | (n : ℝ) < |X k ω|} = P.real {ω | (n : ℝ) < |X 1 ω|} :=
        congrArg ENNReal.toReal ((hid k (Finset.mem_Icc.mp hk).1).measure_mem_eq hm)
      simp_rw [Finset.sum_congr rfl heq]
      simp

end Truncation

/-- The truncated weak law permits an infinite first absolute moment. -/
theorem truncated_weak_law : truncatedWeakLawType := by
  intro Ω mΩ P hP X hX hind hid htail ε hε
  have hmom := truncated_second_moment_tendsto (P := P) (X 1) (hX 1 le_rfl) htail
  have hb : Tendsto (fun n : ℕ =>
      (n : ℝ) * P.real {ω | (n : ℝ) < |X 1 ω|} +
        ((∫ ω, symmetricTruncation (X 1) (n : ℝ) ω ^ 2 ∂P) / (n : ℝ)) / ε ^ 2)
      atTop (𝓝 0) := by
    simpa using htail.add (hmom.div_const (ε ^ 2))
  have hr : Tendsto (fun n : ℕ =>
      P.real {ω | ε < ‖(sampleAverage X n ω - truncatedMean P (X 1) n) - 0‖})
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hb
    filter_upwards [eventually_ge_atTop 1] with n hn
    let Y : ℕ → Ω → ℝ := fun k => symmetricTruncation (X k) (n : ℝ)
    have hsub : {ω | ε < ‖(sampleAverage X n ω - truncatedMean P (X 1) n) - 0‖} ⊆
        {ω | sampleAverage X n ω ≠ sampleAverage Y n ω} ∪
          {ω | ε ≤ |sampleAverage Y n ω - truncatedMean P (X 1) n|} := by
      intro ω hω
      by_cases heq : sampleAverage X n ω = sampleAverage Y n ω
      · right
        have hω' : ε < |sampleAverage X n ω - truncatedMean P (X 1) n| := by
          simpa only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] using hω
        exact (heq ▸ hω').le
      · exact Or.inl heq
    calc
      _ ≤ P.real ({ω | sampleAverage X n ω ≠ sampleAverage Y n ω} ∪
          {ω | ε ≤ |sampleAverage Y n ω - truncatedMean P (X 1) n|}) :=
        measureReal_mono hsub (measure_ne_top P _)
      _ ≤ P.real {ω | sampleAverage X n ω ≠ sampleAverage Y n ω} +
          P.real {ω | ε ≤ |sampleAverage Y n ω - truncatedMean P (X 1) n|} :=
        measureReal_union_le _ _
      _ ≤ _ := add_le_add (average_truncation_change_bound (P := P) X hid n)
        (truncated_deviation_bound (P := P) X hX hind hid n hn ε hε)
  have heq (n : ℕ) : ENNReal.ofReal
      (P.real {ω | ε < ‖(sampleAverage X n ω - truncatedMean P (X 1) n) - 0‖}) =
      P {ω | ε < ‖(sampleAverage X n ω - truncatedMean P (X 1) n) - 0‖} :=
    ofReal_measureReal (measure_ne_top P _)
  simpa only [ENNReal.ofReal_zero, heq] using ENNReal.tendsto_ofReal hr

end ProbabilityFoundations.Ch08
