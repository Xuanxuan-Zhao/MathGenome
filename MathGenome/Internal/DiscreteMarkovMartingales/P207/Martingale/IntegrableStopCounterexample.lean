import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.IntegrableStopCounterexample
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.DoublingExample
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory

noncomputable section
namespace P207.DoublingStop
open P207.Doubling

namespace Interfaces
noncomputable abbrev firstTail : P207.DoublingStopSpec.firstTailType :=
  P207.DoublingStop.firstTail
noncomputable abbrev duration : P207.DoublingStopSpec.durationType :=
  P207.DoublingStop.duration
noncomputable abbrev stoppedValue : P207.DoublingStopSpec.stoppedValueType :=
  P207.DoublingStop.stoppedValue
end Interfaces

theorem firstTail_gt_iff (k : ℕ) (ω : Ω) :
    (k : WithTop ℕ) < firstTail ω ↔ ω ∈ allHeads k := by
  classical
  unfold firstTail
  split_ifs with h
  · simp only [Nat.cast_withTop, WithTop.coe_lt_coe]
    constructor
    · intro hk i hi
      have hn : i < Nat.find h := by omega
      have hf := Nat.find_min h hn
      cases ht : toss i ω <;> simp_all
    · intro ha
      by_contra hn
      have hf := Nat.find_spec h
      have : Nat.find h < k := by omega
      have := ha _ this
      simp_all
  · simp only [WithTop.natCast_lt_top, true_iff]
    intro i _
    have hf : toss i ω ≠ false := fun hf => h ⟨i, hf⟩
    cases ht : toss i ω <;> simp_all

theorem stoppingTime : P207.IsDiscreteStoppingTime filtration firstTail := by
  intro n
  have heq : {ω | firstTail ω ≤ n} = (allHeads n)ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, ← firstTail_gt_iff, not_lt]
  rw [heq]
  exact (measurableSet_allHeads n).compl

theorem tail_probability (k : ℕ) :
    μ {ω | (k : WithTop ℕ) < firstTail ω} = ((2 : ℝ≥0∞)⁻¹) ^ k := by
  have heq : {ω | (k : WithTop ℕ) < firstTail ω} = allHeads k := by
    ext ω
    exact firstTail_gt_iff k ω
  rw [heq, allHeads_measure]

theorem firstTail_eq_top_iff (ω : Ω) : firstTail ω = ⊤ ↔ ω ∈ ⋂ n, allHeads n := by
  simp only [Set.mem_iInter, ← firstTail_gt_iff]
  constructor
  · intro h n
    simp [h]
  · intro h
    cases ht : firstTail ω with
    | top => rfl
    | coe n => have := h n; simp [ht] at this

theorem finite_ae : ∀ᵐ ω ∂μ, firstTail ω < ⊤ := by
  have hn : μ {ω | firstTail ω = ⊤} = 0 := by
    have heq : {ω | firstTail ω = ⊤} = ⋂ n, allHeads n := by
      ext ω
      exact firstTail_eq_top_iff ω
    rw [heq, allHeads_forever_null]
  simpa only [lt_top_iff_ne_top, ae_iff, not_not] using hn

/-- Tail-sum identity, used only off the null all-heads path. -/
theorem duration_eq_tsum (ω : Ω) (hω : firstTail ω < ⊤) :
    ENNReal.ofReal (duration ω) =
      ∑' k : ℕ, (allHeads k).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hω)
  have hm (k : ℕ) : ω ∈ allHeads k ↔ k < n := by
    rw [← firstTail_gt_iff, ← hn]
    exact ENat.natCast_lt_natCast
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
    apply Set.indicator_of_notMem
    exact fun h => hk (Finset.mem_range.mpr ((hm k).mp h)))]
  simp only [duration, ← hn, WithTop.untopD_coe, ENNReal.ofReal_natCast]
  rw [Finset.sum_congr rfl (fun k hk => Set.indicator_of_mem ((hm k).mpr
    (Finset.mem_range.mp hk)) _)]
  simp

theorem measurable_duration : Measurable duration := by
  exact (measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
    ((MeasureTheory.IsStoppingTime.measurable' stoppingTime).untopD 0)

/-- Tonelli turns the duration into the geometric series of survival probabilities. -/
theorem lintegral_duration : (∫⁻ ω, ENNReal.ofReal (duration ω) ∂μ) = 2 := by
  calc
    (∫⁻ ω, ENNReal.ofReal (duration ω) ∂μ) =
        ∫⁻ ω, ∑' k : ℕ, (allHeads k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [finite_ae] with ω hω using duration_eq_tsum ω hω
    _ = ∑' k : ℕ, ∫⁻ ω, (allHeads k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ :=
      lintegral_tsum (fun k => (measurable_const.indicator
        (filtration.le k _ (measurableSet_allHeads k))).aemeasurable)
    _ = ∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ k := by
      congr 1
      funext k
      rw [lintegral_indicator (filtration.le k _ (measurableSet_allHeads k))]
      simp [allHeads_measure]
    _ = 2 := ENNReal.tsum_geometric_two

theorem integrable_duration : Integrable duration μ := by
  apply (lintegral_ofReal_ne_top_iff_integrable measurable_duration.aestronglyMeasurable
    (Eventually.of_forall fun ω => by simp [duration])).mp
  rw [lintegral_duration]
  norm_num

theorem expected_duration : (∫ ω, duration ω ∂μ) = 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun ω => by simp [duration])
    measurable_duration.aestronglyMeasurable, lintegral_duration]
  norm_num

theorem stoppedValue_zero (ω : Ω) : stoppedValue ω = 0 := by
  classical
  unfold stoppedValue P207.fullStoppedValue
  by_cases ht : firstTail ω = ⊤
  · simp [ht]
  · simp only [ht, ↓reduceIte]
    unfold firstTail at ht ⊢
    split_ifs with h
    · change M (Nat.find h + 1) ω = 0
      apply Set.indicator_of_notMem
      intro ha
      have hh := ha (Nat.find h) (Nat.lt_succ_self _)
      have hf := Nat.find_spec h
      simp_all
    · simp [h] at ht

theorem expectation_failure :
    Integrable stoppedValue μ ∧ (∫ ω, stoppedValue ω ∂μ) = 0 ∧
    (∀ ω, M 0 ω = 1) ∧ (∫ ω, stoppedValue ω ∂μ) ≠ ∫ ω, M 0 ω ∂μ := by
  have hz : stoppedValue = fun _ => 0 := funext stoppedValue_zero
  rw [hz]
  exact ⟨integrable_zero _ _ _, integral_zero _ _, M_zero, by rw [integral_zero, expectation]; norm_num⟩

theorem abs_increment (k : ℕ) (ω : Ω) : |M (k + 1) ω - M k ω| = M k ω := by
  classical
  rw [M_succ]
  by_cases ha : ω ∈ allHeads k <;> by_cases hb : toss k ω = true <;>
    simp [M, headPayoff, ha, hb, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ k)]
  rw [show (2 : ℝ) ^ k * 2 - 2 ^ k = 2 ^ k by ring, abs_of_nonneg (by positivity)]

theorem conditional_abs_increment (k : ℕ) :
    μ[fun ω => |M (k + 1) ω - M k ω| | filtration k] =ᵐ[μ] M k := by
  simp_rw [abs_increment]
  exact (condExp_of_stronglyMeasurable (filtration.le k) (adapted.stronglyAdapted k)
    (integrable k)).eventuallyEq

theorem conditional_abs_increment_on_heads (k : ℕ) :
    μ (allHeads k) > 0 ∧ ∀ᵐ ω ∂μ, ω ∈ allHeads k →
      μ[fun ω => |M (k + 1) ω - M k ω| | filtration k] ω = (2 : ℝ) ^ k := by
  constructor
  · rw [allHeads_measure]
    exact ENNReal.pow_pos (by norm_num) k
  · filter_upwards [conditional_abs_increment k] with ω hω ha
    simpa [M, ha] using hω

theorem no_uniform_increment_bound : ¬ ∃ C : ℝ, ∀ k : ℕ,
    μ[fun ω => |M (k + 1) ω - M k ω| | filtration k] ≤ᵐ[μ] fun _ => C := by
  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  have hle : ∀ᵐ ω ∂μ, ω ∉ allHeads k := by
    filter_upwards [(conditional_abs_increment_on_heads k).2, hC k] with ω he hb ha
    have := he ha
    linarith
  have hz : μ (allHeads k) = 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hle
  exact (ne_of_gt (conditional_abs_increment_on_heads k).1) hz

end P207.DoublingStop
