import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.KolmogorovVarianceCriterion
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.FirstBorelCantelli
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityFoundations.Ch08

namespace MZ
abbrev weight := Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.weight
abbrev truncated := @Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.truncated

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma truncated_measurable (p : ℝ) (X : ℕ → Ω → ℝ) (k : ℕ)
    (hX : Measurable (X k)) : Measurable (truncated p X k) :=
  hX.indicator (measurableSet_le (continuous_abs.measurable.comp hX) measurable_const)

lemma abs_truncated_le (p : ℝ) (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    |truncated p X k ω| ≤ weight p (k + 1) := by
  change |{ω | |X k ω| ≤ weight p (k + 1)}.indicator (X k) ω| ≤ _
  by_cases h : |X k ω| ≤ weight p (k + 1)
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left h]
    exact h
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right h, abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma truncated_memLp (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (X : ℕ → Ω → ℝ) (k : ℕ) (hX : Measurable (X k)) :
    MemLp (truncated p X k) 2 P :=
  MemLp.of_bound (truncated_measurable p X k hX).aestronglyMeasurable
    (weight p (k + 1)) (Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using abs_truncated_le p X k ω)

lemma truncation_event_eq (p : ℝ) (hp : 0 < p) (X : ℕ → Ω → ℝ) (k : ℕ) :
    {ω | X k ω ≠ truncated p X k ω} = {ω | (k + 1 : ℕ) < |X k ω| ^ p} := by
  ext ω
  have hw : 0 ≤ weight p (k + 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hh : |X k ω| ≤ weight p (k + 1) ↔ |X k ω| ^ p ≤ (k + 1 : ℕ) := by
    simpa only [weight, Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.weight,
      one_div] using Real.le_rpow_inv_iff_of_pos (abs_nonneg _) (Nat.cast_nonneg (k+1)) hp
  change (X k ω ≠ {ω | |X k ω| ≤ weight p (k + 1)}.indicator (X k) ω) ↔ _
  by_cases h : |X k ω| ≤ weight p (k + 1)
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left h]
    exact iff_of_false (not_ne_iff.mpr rfl) (not_lt.mpr (hh.mp h))
  · have hx : X k ω ≠ 0 := by
      intro hz
      apply h
      simpa [hz] using hw
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right h]
    exact iff_of_true hx (lt_of_not_ge (mt hh.mpr h))

lemma truncated_eq_comp (p : ℝ) (X : ℕ → Ω → ℝ) (k : ℕ) :
    truncated p X k = ({x : ℝ | |x| ≤ weight p (k + 1)}.indicator id) ∘ X k := by
  ext ω
  simp only [truncated, Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.truncated,
    Set.indicator_apply, Set.mem_ofPred_eq, Function.comp_apply, id_eq]

lemma cutoff_measurable (p : ℝ) (k : ℕ) :
    Measurable ({x : ℝ | |x| ≤ weight p (k + 1)}.indicator id) :=
  measurable_id.indicator (measurableSet_le continuous_abs.measurable measurable_const)

lemma truncated_identDistrib (P : Measure Ω) (p : ℝ) (X : ℕ → Ω → ℝ) (k : ℕ)
    (hd : IdentDistrib (X k) (X 0) P P) :
    IdentDistrib (truncated p X k) (truncated p (fun _ => X 0) k) P P := by
  rw [truncated_eq_comp, truncated_eq_comp]
  exact hd.comp (cutoff_measurable p k)

/-- The square of the cutoff variable written using its p-th absolute power. -/
lemma truncated_sq_div (p : ℝ) (hp : 0 < p) (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    truncated p X k ω ^ 2 / ((k + 1 : ℕ) : ℝ) ^ (2 / p) =
      if |X k ω| ^ p ≤ ((k + 1 : ℕ) : ℝ) then
        (|X k ω| ^ p) ^ (2 / p) / ((k + 1 : ℕ) : ℝ) ^ (2 / p) else 0 := by
  have hh : |X k ω| ≤ weight p (k + 1) ↔ |X k ω| ^ p ≤ (k + 1 : ℕ) := by
    simpa only [weight, Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.weight,
      one_div] using Real.le_rpow_inv_iff_of_pos (abs_nonneg _) (Nat.cast_nonneg (k+1)) hp
  have hpow : (|X k ω| ^ p) ^ (2 / p) = X k ω ^ 2 := by
    rw [← Real.rpow_mul (abs_nonneg _), show p * (2 / p) = 2 by field_simp,
      Real.rpow_two, sq_abs]
  change {ω | |X k ω| ≤ weight p (k + 1)}.indicator (X k) ω ^ 2 / _ = _
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, hh, hpow]
  split_ifs <;> simp

/-- Integral comparison for a finite tail of a p-series. -/
lemma sum_rpow_tail {q : ℝ} (hq : 1 < q) (m N : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico m N, (k : ℝ) ^ (-q) ≤
      (1 + 1 / (q - 1)) * (m : ℝ) ^ (1 - q) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-q)) (Ici (m : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hm0.trans_le hx) hxy (by linarith)
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -q < -1) hm0
  have hbound := (hanti.mono (show Icc (m : ℝ) N ⊆ Ici (m : ℝ) from fun _ h => h.1)).sum_Ico_le_integral
    hi (fun x hx => Real.rpow_nonneg (hm0.le.trans hx.le) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -q < -1) hm0] at hbound
  have hb : ∑ k ∈ Finset.Ico m N, (k : ℝ) ^ (-q) ≤
      (m : ℝ) ^ (-q) + ∑ k ∈ Finset.Ico m N, ((k + 1 : ℕ) : ℝ) ^ (-q) := by
    by_cases hmn : m < N
    · rw [Finset.sum_eq_sum_Ico_succ_bot hmn]
      gcongr
      rw [Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-q)) m N 1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (by intro i hi; simp only [Finset.mem_Ico] at *; omega)
        (by intro i _ _; positivity)
    · rw [Finset.Ico_eq_empty_of_le (Nat.le_of_not_gt hmn)]
      simp only [Finset.sum_empty, add_zero]
      positivity
  have hpow : (m : ℝ) ^ (-q) ≤ (m : ℝ) ^ (1 - q) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  calc
    _ ≤ (m : ℝ) ^ (-q) + -(m : ℝ) ^ (-q + 1) / (-q + 1) := hb.trans (add_le_add le_rfl hbound)
    _ ≤ (1 + 1 / (q - 1)) * (m : ℝ) ^ (1 - q) := by
      rw [show -q + 1 = 1 - q by ring]
      have he : -(m : ℝ) ^ (1 - q) / (1 - q) = (m : ℝ) ^ (1 - q) / (q - 1) := by
        convert neg_div_neg_eq ((m : ℝ) ^ (1 - q)) (q - 1) using 1
        congr 1
        ring
      rw [he]
      calc
        _ ≤ (m : ℝ) ^ (1 - q) + (m : ℝ) ^ (1 - q) / (q - 1) := add_le_add hpow le_rfl
        _ = _ := by ring

/-- The pointwise bound behind the weighted truncated second moments. -/
lemma sum_truncated_powers {z q : ℝ} (hz : 0 ≤ z) (hq : 1 < q) (N : ℕ) :
    ∑ k ∈ Finset.range N,
      (if z ≤ ((k + 1 : ℕ) : ℝ) then z ^ q / ((k + 1 : ℕ) : ℝ) ^ q else 0) ≤
      (1 + 1 / (q - 1)) * z := by
  classical
  rcases eq_or_lt_of_le hz with rfl | hz0
  · simp [Real.zero_rpow (by linarith : q ≠ 0)]
  let m : ℕ := ⌈z⌉₊
  have hm : 1 ≤ m := Nat.one_le_ceil_iff.mpr hz0
  have hzm : z ≤ (m : ℝ) := Nat.le_ceil z
  have hsum : ∑ k ∈ Finset.range N,
      (if z ≤ ((k + 1 : ℕ) : ℝ) then ((k + 1 : ℕ) : ℝ) ^ (-q) else 0) =
      ∑ k ∈ Finset.Ico m (N + 1), (k : ℝ) ^ (-q) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun k _ => k + 1)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      exact Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr hk.2, by omega⟩
    · intro a ha b hb hab
      omega
    · intro k hk
      have hk' := Finset.mem_Ico.mp hk
      have hk1 : 1 ≤ k := hm.trans hk'.1
      refine ⟨k - 1, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by simpa [Nat.sub_add_cancel hk1] using (Nat.ceil_le.mp hk'.1)⟩
    · intros; rfl
  have hzpow : z ^ q * (m : ℝ) ^ (1 - q) ≤ z := by
    calc
      _ ≤ z ^ q * z ^ (1 - q) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hz0 hzm (by linarith)) (Real.rpow_nonneg hz _)
      _ = z := by rw [← Real.rpow_add hz0, show q + (1 - q) = 1 by ring, Real.rpow_one]
  calc
    _ = z ^ q * ∑ k ∈ Finset.range N,
        (if z ≤ ((k + 1 : ℕ) : ℝ) then ((k + 1 : ℕ) : ℝ) ^ (-q) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs
      · rw [Real.rpow_neg (Nat.cast_nonneg _) q]
        rfl
      · simp
    _ = z ^ q * ∑ k ∈ Finset.Ico m (N + 1), (k : ℝ) ^ (-q) := by rw [hsum]
    _ ≤ z ^ q * ((1 + 1 / (q - 1)) * (m : ℝ) ^ (1 - q)) :=
      mul_le_mul_of_nonneg_left (sum_rpow_tail hq m (N + 1) hm) (Real.rpow_nonneg hz _)
    _ ≤ (1 + 1 / (q - 1)) * z := by
      calc
        _ = (1 + 1 / (q - 1)) * (z ^ q * (m : ℝ) ^ (1 - q)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hzpow (by positivity)

end MZ

theorem mz_truncation_probabilities :
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.truncationProbabilitiesType := by
  intro Ω mΩ P hP X p hX hd hp _hm hmom
  let : MeasureSpace Ω := ⟨P⟩
  have htail := ProbabilityTheory.tsum_prob_mem_Ioi_lt_top hmom
    (fun ω => Real.rpow_nonneg (abs_nonneg (X 0 ω)) p)
  have hd' (k : ℕ) : IdentDistrib (fun ω => |X k ω| ^ p) (fun ω => |X 0 ω| ^ p) P P :=
    (hd k).comp (show Measurable (fun x : ℝ => |x| ^ p) by fun_prop)
  have heq (k : ℕ) : P {ω | X k ω ≠ MZ.truncated p X k ω} =
      P {ω | (k + 1 : ℕ) < |X 0 ω| ^ p} := by
    rw [MZ.truncation_event_eq p hp X k]
    exact (hd' k).measure_mem_eq measurableSet_Ioi
  simp_rw [heq]
  exact (ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective _).trans_lt htail

/-- Summability uses only the common p-th moment, not independence. -/
theorem mz_weighted_variances :
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.weightedVariancesType := by
  intro Ω mΩ P hP X p hX hd hp hp2 hmom
  let T : ℕ → Ω → ℝ := MZ.truncated p (fun _ => X 0)
  have hT2 (k : ℕ) : MemLp (T k) 2 P := MZ.truncated_memLp P p _ k (hX 0)
  have hY (k : ℕ) : Measurable (MZ.truncated p X k) := MZ.truncated_measurable p X k (hX k)
  have hsecond (k : ℕ) :
      (∫ ω, MZ.truncated p X k ω ^ 2 ∂P) = ∫ ω, T k ω ^ 2 ∂P :=
    ((MZ.truncated_identDistrib P p X k (hd k)).comp
      (show Measurable (fun x : ℝ => x ^ 2) from measurable_id.pow_const 2)).integral_eq
  have hvarle (k : ℕ) :
      Ch01.realVariance P (MZ.truncated p X k) ≤ ∫ ω, T k ω ^ 2 ∂P := by
    rw [← hsecond k]
    rw [show Ch01.realVariance P (MZ.truncated p X k) =
        variance (MZ.truncated p X k) P from
      (variance_eq_integral (hY k).aemeasurable).symm]
    exact variance_le_expectation_sq (hY k).aestronglyMeasurable
  have hq : 1 < 2 / p := (lt_div_iff₀ hp).mpr (by linarith)
  apply summable_of_sum_range_le (c := (1 + 1 / (2 / p - 1)) * ∫ ω, |X 0 ω| ^ p ∂P)
  · intro k
    apply div_nonneg _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact integral_nonneg (fun ω => sq_nonneg _)  -- centered second moment
  · intro N
    calc
      _ ≤ ∑ k ∈ Finset.range N, (∫ ω, T k ω ^ 2 ∂P) / ((k + 1 : ℕ) : ℝ) ^ (2 / p) := by
        apply Finset.sum_le_sum
        intro k hk
        exact div_le_div_of_nonneg_right (hvarle k) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = ∫ ω, ∑ k ∈ Finset.range N, T k ω ^ 2 / ((k + 1 : ℕ) : ℝ) ^ (2 / p) ∂P := by
        simp_rw [← integral_div]
        rw [integral_finsetSum]
        intro k hk
        exact ((hT2 k).integrable_sq).div_const _
      _ ≤ ∫ ω, (1 + 1 / (2 / p - 1)) * |X 0 ω| ^ p ∂P := by
        apply integral_mono
        · exact integrable_finsetSum _ (fun k hk => ((hT2 k).integrable_sq).div_const _)
        · exact hmom.const_mul _
        · intro ω
          simp_rw [T, MZ.truncated_sq_div p hp]
          exact MZ.sum_truncated_powers (Real.rpow_nonneg (abs_nonneg _) _) hq N
      _ = _ := integral_const_mul _ _

/-- Kolmogorov's criterion applied with the source weights n^(1/p). -/
theorem mz_centered_truncation :
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.centeredTruncationType := by
  intro Ω mΩ P hP X p hX hI hd hp hp2 hmom
  have hY (k : ℕ) : Measurable (MZ.truncated p X k) := MZ.truncated_measurable p X k (hX k)
  have hY2 (k : ℕ) : MemLp (MZ.truncated p X k) 2 P := MZ.truncated_memLp P p X k (hX k)
  have hYI : Ch02.IndependentRandomElements P (MZ.truncated p X) := by
    apply (Ch02.independentRandomElements_iff_iIndepFun P _).mpr
    have hh := ((Ch02.independentRandomElements_iff_iIndepFun P X).mp hI).comp
      (fun k => {x : ℝ | |x| ≤ MZ.weight p (k + 1)}.indicator id)
      (MZ.cutoff_measurable p)
    simpa only [← MZ.truncated_eq_comp] using hh
  have hb (n : ℕ) (hn : 1 ≤ n) : 0 < MZ.weight p n := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) _
  have hmono : MonotoneOn (MZ.weight p) (Ici 1) := by
    intro i hi j hj hij
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hij) (by positivity)
  have ht : Tendsto (MZ.weight p) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 1 / p)).comp tendsto_natCast_atTop_atTop
  have hsq (n : ℕ) : MZ.weight p n ^ 2 = (n : ℝ) ^ (2 / p) := by
    change ((n : ℝ) ^ (1 / p)) ^ 2 = _
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) (1 / p) 2]
    congr 1
    norm_num
    ring
  have hs := mz_weighted_variances P X p hX hd hp hp2 hmom
  apply kolmogorov_variance_criterion P (MZ.truncated p X) (MZ.weight p) hY hYI hY2 hb hmono ht
  simpa only [hsq] using hs

theorem mz_eventually_constant_difference :
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.eventuallyConstantDifferenceType := by
  intro Ω mΩ P hP X p hX hd hp hp2 hmom
  have hs := mz_truncation_probabilities P X p hX hd hp hp2 hmom
  have hf := Ch02.ae_finite_occurrences P
    (fun k => {ω | X k ω ≠ MZ.truncated p X k ω})
    (fun k => (measurableSet_eq_fun (hX k) (MZ.truncated_measurable p X k (hX k))).compl) hs
  filter_upwards [hf] with ω hω
  obtain ⟨N, hN⟩ := hω.bddAbove
  have heq (k : ℕ) (hk : N + 1 ≤ k) : X k ω = MZ.truncated p X k ω := by
    by_contra h
    have := hN (show k ∈ {k | X k ω ≠ MZ.truncated p X k ω} from h)
    omega
  refine ⟨(∑ k ∈ Finset.range (N + 1), X k ω) -
      (∑ k ∈ Finset.range (N + 1), MZ.truncated p X k ω), ?_⟩
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, heq n hn]
    linarith

end ProbabilityFoundations.Ch08
