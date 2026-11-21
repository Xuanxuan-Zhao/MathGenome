import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.BernoulliChernoff
import MathGenome.Internal.ExtremalOptimization.P205.Probability.BernoulliMGF
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory

namespace P205.Probability

/-- Express the exact multiplicative Chernoff factor as a single exponential. -/
private theorem chernoff_factor (a b m : ℝ) (ha : 0 < a) :
    (Real.exp b / a ^ a) ^ m = Real.exp (m * (b - a * Real.log a)) := by
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos b) (Real.rpow_pos_of_pos ha a)),
    Real.log_div (Real.exp_ne_zero b) (ne_of_gt (Real.rpow_pos_of_pos ha a)),
    Real.log_exp, Real.log_rpow ha]
  congr 1
  ring

theorem bernoulli_chernoff_upper : Specs.P205.Probability.BernoulliChernoffUpper := by
  intro Ω ι _ _ ν _ X p hX h01 hp hpLaw hInd δ hδ
  have ha : 0 < 1 + δ := by linarith
  obtain ⟨hInt, hEq, hBound⟩ := bernoulli_mgf ν X p hX h01 hp hpLaw hInd
    (Real.log (1 + δ))
  have hTail := measure_ge_le_exp_mul_mgf ((1 + δ) * ∑ i, p i)
    (Real.log_nonneg (by linarith : 1 ≤ 1 + δ)) hInt
  rw [hEq] at hTail
  calc
    _ ≤ Real.exp (-Real.log (1 + δ) * ((1 + δ) * ∑ i, p i)) *
        Real.exp ((∑ i, p i) * (Real.exp (Real.log (1 + δ)) - 1)) :=
      hTail.trans (mul_le_mul_of_nonneg_left hBound (Real.exp_pos _).le)
    _ = (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (∑ i, p i) := by
      rw [chernoff_factor _ _ _ ha, ← Real.exp_add, Real.exp_log ha]
      congr 1
      ring

theorem bernoulli_chernoff_lower : Specs.P205.Probability.BernoulliChernoffLower := by
  intro Ω ι _ _ ν _ X p hX h01 hp hpLaw hInd δ hδ hδ1
  have ha : 0 < 1 - δ := sub_pos.mpr hδ1
  obtain ⟨hInt, hEq, hBound⟩ := bernoulli_mgf ν X p hX h01 hp hpLaw hInd
    (Real.log (1 - δ))
  have hTail := measure_le_le_exp_mul_mgf ((1 - δ) * ∑ i, p i)
    (Real.log_nonpos ha.le (by linarith : 1 - δ ≤ 1)) hInt
  rw [hEq] at hTail
  calc
    _ ≤ Real.exp (-Real.log (1 - δ) * ((1 - δ) * ∑ i, p i)) *
        Real.exp ((∑ i, p i) * (Real.exp (Real.log (1 - δ)) - 1)) :=
      hTail.trans (mul_le_mul_of_nonneg_left hBound (Real.exp_pos _).le)
    _ = (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (∑ i, p i) := by
      rw [chernoff_factor _ _ _ ha, ← Real.exp_add, Real.exp_log ha]
      congr 1
      ring

/-- Independence gives the exact no-success probability even when Bernoulli
values are specified only almost everywhere. -/
theorem bernoulli_sum_zero_probability {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : ι → Ω → ℝ) (p : ι → ℝ)
    (hX : ∀ i, Measurable (X i))
    (h01 : ∀ i, ∀ᵐ ω ∂ν, X i ω = 0 ∨ X i ω = 1)
    (hpLaw : ∀ i, p i = ν.real {ω | X i ω = 1}) (hInd : iIndepFun X ν) :
    ν.real {ω | (∑ i, X i ω) = 0} = ∏ i, (1 - p i) := by
  classical
  have hEvents : {ω | (∑ i, X i ω) = 0} =ᵐ[ν] ⋂ i, {ω | X i ω ≠ 1} := by
    filter_upwards [ae_all_iff.mpr h01] with ω hω
    apply propext
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    have hn (i : ι) : 0 ≤ X i ω := by
      rcases hω i with h | h <;> simp [h]
    constructor
    · intro hSum i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hSum i
        (Finset.mem_univ i)
      simp [hi]
    · intro hi
      apply Finset.sum_eq_zero
      intro i _
      exact (hω i).resolve_right (hi i)
  have hInter : ν (⋂ i, {ω | X i ω ≠ 1}) = ∏ i, ν {ω | X i ω ≠ 1} := by
    simpa [Set.preimage, Set.compl_ofPred] using hInd.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun _ => ({1} : Set ℝ)ᶜ) (fun _ _ => (measurableSet_singleton 1).compl)
  have hInterReal : ν.real (⋂ i, {ω | X i ω ≠ 1}) =
      ∏ i, ν.real {ω | X i ω ≠ 1} := by
    simp only [measureReal_def, hInter, ENNReal.toReal_prod]
  rw [measureReal_congr hEvents, hInterReal]
  apply Finset.prod_congr rfl
  intro i _
  rw [hpLaw i]
  exact probReal_compl_eq_one_sub (measurableSet_eq_fun (hX i) measurable_const)

theorem bernoulli_chernoff_at_one : Specs.P205.Probability.BernoulliChernoffAtOne := by
  intro Ω ι _ _ ν _ X p hX h01 hp hpLaw hInd
  classical
  rw [bernoulli_sum_zero_probability ν X p hX h01 hpLaw hInd]
  calc
    (∏ i, (1 - p i)) ≤ ∏ i, Real.exp (-p i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact sub_nonneg.mpr (hp i).2
      · intro i _
        linarith [Real.add_one_le_exp (-p i)]
    _ = Real.exp (-(∑ i, p i)) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]

theorem bernoulli_chernoff_zero_mean : Specs.P205.Probability.BernoulliChernoffZeroMean := by
  intro Ω ι _ _ ν _ X p hX h01 hp hpLaw hMean
  refine ⟨bernoulli_sum_zero ν X p hX h01 hp hpLaw hMean, ?_, ?_⟩
  · simp [hMean]
  · intro δ _
    simp [hMean]

end P205.Probability
