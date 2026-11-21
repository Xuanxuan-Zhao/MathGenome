import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.SymmetricInfiniteMeans
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.IntegerHitting
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.MeanHittingTime

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace P207.Walk
noncomputable section

/-- A nonnegative solution of the symmetric Poisson equation on the half-line
cannot be finite at one. Finiteness would propagate and force a negative quadratic. -/
theorem symmetric_poisson_infinite (f : ℕ → ℝ≥0∞) (h0 : f 0 = 0)
    (hs : ∀ n, 0 < n → f n = 1 + ENNReal.ofReal (1 / 2) * f (n + 1) +
      ENNReal.ofReal (1 / 2) * f (n - 1)) : f 1 = ⊤ := by
  by_contra h1
  have hf : ∀ n, f n ≠ ⊤ := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      by_cases hn : n = 0
      · simpa [hn] using h1
      · have he := hs n (by omega)
        have hb : ENNReal.ofReal (1 / 2) * f (n + 1) ≤ f n := by
          rw [he]
          exact (le_add_left le_rfl).trans (le_add_right le_rfl)
        have hm := ne_top_of_le_ne_top ih hb
        intro ht
        simp [ht] at hm
  let u : ℕ → ℝ := fun n => (f n).toReal
  have hu0 : u 0 = 0 := by simp [u, h0]
  have hu (n : ℕ) (hn : 0 < n) :
      u n = 1 + (1 / 2 : ℝ) * u (n + 1) + (1 / 2 : ℝ) * u (n - 1) := by
    have he := congrArg ENNReal.toReal (hs n hn)
    have hm (k : ℕ) : ENNReal.ofReal (1 / 2) * f k ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf k)
    simpa only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hm _⟩) (hm _),
      ENNReal.toReal_add ENNReal.one_ne_top (hm _), ENNReal.toReal_one,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), u] using he
  have hformula : ∀ n : ℕ, u n = (n : ℝ) * u 1 - (n : ℝ) * ((n : ℝ) - 1) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [hu0]
    | one => simp
    | more n ih ih' =>
      have he := hu (n + 1) (by omega)
      simp only [Nat.add_sub_cancel] at he
      rw [ih, ih'] at he
      push_cast at he ⊢
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (u 1 + 1)
  have hnon : 0 ≤ u n := ENNReal.toReal_nonneg
  rw [hformula] at hnon
  have hn0 : (0 : ℝ) < n := lt_trans (by positivity : (0 : ℝ) < u 1 + 1) hn
  nlinarith

/-- Infinite means on both reflected half-lines. -/
theorem symmetric_adjacent_mean_hitting (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (he : p = 1 - p) :
    Markov.meanHittingTime (integerKernel p hp hp1) {0} 1 = ⊤ ∧
      Markov.meanHittingTime (integerKernel p hp hp1) {0} (-1) = ⊤ := by
  have hpHalf : p = 1 / 2 := by linarith
  have hqHalf : 1 - p = 1 / 2 := by linarith
  have h0 : Markov.meanHittingTime (integerKernel p hp hp1) {0} 0 = 0 :=
    Markov.meanHittingTime_boundary _ _ _ (by simp)
  have hs (i : ℤ) (hi : i ≠ 0) :
      Markov.meanHittingTime (integerKernel p hp hp1) {0} i =
      1 + ENNReal.ofReal (1 / 2) * Markov.meanHittingTime (integerKernel p hp hp1) {0} (i + 1) +
        ENNReal.ofReal (1 / 2) * Markov.meanHittingTime (integerKernel p hp hp1) {0} (i - 1) := by
    rw [Markov.meanHittingTime_equation _ _ i hi, integerKernel_action]
    rw [congrArg ENNReal.ofReal hpHalf, congrArg ENNReal.ofReal hqHalf, add_assoc]
  constructor
  · apply symmetric_poisson_infinite (fun n =>
      Markov.meanHittingTime (integerKernel p hp hp1) {0} (n : ℤ)) h0
    intro n hn
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    simpa only [Nat.cast_add, Nat.cast_one, hcast] using hs n (by omega)
  · apply symmetric_poisson_infinite (fun n =>
      Markov.meanHittingTime (integerKernel p hp hp1) {0} (-(n : ℤ))) (by simpa using h0)
    intro n hn
    have hR : -(n : ℤ) + 1 = -((n - 1 : ℕ) : ℤ) := by omega
    have hL : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hs _ (by omega), hR, hL]
    ac_rfl

/-- The time remaining after the first step is bounded by the full positive
return time. This pointwise inequality also includes infinite times. -/
theorem hitting_shift_le_return (ω : ℕ → ℤ) :
    Markov.hittingTime {0} (fun k => ω (1 + k)) ≤ Markov.returnTime 0 ω := by
  by_cases ht : Markov.returnTime 0 ω = ⊤
  · simp [ht]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [← hn]
    have hle : Markov.positiveReturnTime Markov.coordinate 0 ω ≤ n := by
      change Markov.returnTime 0 ω ≤ n
      exact hn.ge
    obtain ⟨k, hk, hkn, hk0⟩ :=
      (Markov.positiveReturnTime_le_iff Markov.coordinate 0 ω n).mp hle
    apply (Markov.hittingTime_le_iff _ _ n).mpr
    refine ⟨k - 1, by omega, ?_⟩
    simpa only [Nat.add_sub_of_le hk, Markov.coordinate, Set.mem_singleton_iff] using hk0

/-- First-step disintegration of the nonnegative entrance duration. Tonelli
allows the value infinity throughout. -/
theorem integer_shift_duration_mean (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : ℤ) :
    (∫⁻ ω, Markov.hittingDuration {0} (fun k => ω (1 + k)) ∂integerLaw p hp hp1 i) =
      Markov.action (integerKernel p hp hp1)
        (Markov.meanHittingTime (integerKernel p hp hp1) {0}) i := by
  have hm : Measurable (fun ω : ℕ → ℤ => fun k => ω (1 + k)) :=
    measurable_pi_iff.mpr fun k => measurable_pi_apply (1 + k)
  have hgt (n : ℕ) : MeasurableSet {ω : ℕ → ℤ |
      (n : WithTop ℕ) < Markov.hittingTime {0} (fun k => ω (1 + k))} :=
    (Markov.measurableSet_hittingTime_gt {0} n).preimage hm
  unfold Markov.hittingDuration
  rw [lintegral_tsum]
  · have hterm (n : ℕ) :
        (∫⁻ ω, (if (n : WithTop ℕ) < Markov.hittingTime {0} (fun k => ω (1 + k))
          then 1 else 0) ∂integerLaw p hp hp1 i) =
        ∑' j, integerKernel p hp hp1 i j * Markov.statePathLaw (integerKernel p hp hp1) j
          {ω | (n : WithTop ℕ) < Markov.hittingTime {0} ω} := by
      rw [← Markov.hitting_first_step _ _ _ (Markov.measurableSet_hittingTime_gt {0} n)]
      simpa [Set.indicator, integerLaw] using lintegral_indicator_one (μ := integerLaw p hp hp1 i) (hgt n)
    simp_rw [hterm]
    rw [ENNReal.tsum_comm]
    unfold Markov.action
    apply tsum_congr
    intro j
    rw [Markov.meanHittingTime_tail_sum, ENNReal.tsum_mul_left]
  · intro n
    exact (Measurable.ite (hgt n) measurable_const measurable_const).aemeasurable

/-- The final assertion of W21, with the extended expectation of the actual
entrance/return times and no finite-mean stopping argument. -/
theorem symmetric_infinite_means : SymmetricInfiniteMeansSpec.infinite_means := by
  intro p hp hp1 he
  obtain ⟨hpos, hneg⟩ := symmetric_adjacent_mean_hitting p hp hp1 he
  have hpos' := hpos
  have hneg' := hneg
  rw [Markov.meanHittingTime_eq_lintegral] at hpos' hneg'
  refine ⟨hpos', hneg', ?_⟩
  apply top_unique
  calc
    ⊤ = ∫⁻ ω, Markov.hittingDuration {0} (fun k => ω (1 + k))
        ∂integerLaw p hp hp1 0 := by
      rw [integer_shift_duration_mean, integerKernel_action]
      simp [hpos, hneg, ENNReal.ofReal_ne_zero_iff.mpr hp,
        ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hp1)]
    _ ≤ ∫⁻ ω, ENat.toENNReal (Markov.returnTime 0 ω) ∂integerLaw p hp hp1 0 := by
      apply lintegral_mono
      intro ω
      exact (Markov.hittingDuration_eq_toENNReal {0} _).le.trans
        (ENat.toENNReal_mono (hitting_shift_le_return ω))

/-- Infinite mean is compatible with almost-sure finiteness of all three times. -/
theorem symmetric_times_almost_sure_finite : SymmetricInfiniteMeansSpec.almost_sure_finite := by
  intro p hp hp1 he
  have hpos := integerHittingProbability_positive p hp hp1 1 (by omega)
  have hneg := integerHittingProbability_negative p hp hp1 (-1) (by omega)
  have hret := integer_positive_return p hp hp1
  rw [ite_eq_right (by linarith)] at hpos hneg
  have hhalf : 2 * min p (1 - p) = 1 := by rw [min_eq_left he.le]; linarith
  rw [hhalf] at hret
  refine ⟨?_, ?_, ?_⟩
  · apply (mem_ae_iff_prob_eq_one (Markov.measurableSet_hittingTime_finite {0})).mpr
    exact (ENNReal.toReal_eq_one_iff _).mp hpos
  · apply (mem_ae_iff_prob_eq_one (Markov.measurableSet_hittingTime_finite {0})).mpr
    exact (ENNReal.toReal_eq_one_iff _).mp hneg
  · apply (mem_ae_iff_prob_eq_one (Markov.measurableSet_returnTime_finite 0)).mpr
    exact (ENNReal.toReal_eq_one_iff _).mp hret

end
end P207.Walk
