import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.MeanHittingTime
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.HittingProbability

open MeasureTheory Filter
open scoped ENNReal MeasureTheory Classical

universe u
namespace P207.Markov
noncomputable section

namespace MeanHittingTime
abbrev hittingDuration : MeanHittingTimeSpec.hittingDurationType.{u} := @P207.Markov.hittingDuration
abbrev meanHittingTime : MeanHittingTimeSpec.meanHittingTimeType.{u} := @P207.Markov.meanHittingTime
end MeanHittingTime

theorem hittingDuration_at_finite {S : Type u} (A : Set S) (ω : ℕ → S) (n : ℕ)
    (h : hittingTime A ω = n) : hittingDuration A ω = n := by
  unfold hittingDuration
  rw [tsum_eq_sum (s := Finset.range n)]
  · calc
      _ = ∑ _k ∈ Finset.range n, (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [h, Finset.mem_range.mp hk]
      _ = n := by simp
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [h, not_lt.mpr hk]

theorem hittingDuration_at_top {S : Type u} (A : Set S) (ω : ℕ → S)
    (h : hittingTime A ω = ⊤) : hittingDuration A ω = ⊤ := by
  simp [hittingDuration, h]

theorem hittingDuration_eq_toENNReal {S : Type u} (A : Set S) (ω : ℕ → S) :
    hittingDuration A ω = ENat.toENNReal (hittingTime A ω) := by
  by_cases h : hittingTime A ω = ⊤
  · rw [hittingDuration_at_top A ω h, h]
    rfl
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
    rw [hittingDuration_at_finite A ω n hn.symm, ← hn]
    rfl

theorem meanHittingTime_eq_lintegral {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (i : S) :
    meanHittingTime P A i = ∫⁻ ω, ENat.toENNReal (hittingTime A ω) ∂statePathLaw P i := by
  simp only [meanHittingTime, hittingDuration_eq_toENNReal]

variable {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S]

omit [Nonempty S] in
/-- The survival event is the complement of the finite cutoff event. -/
theorem measurableSet_hittingTime_gt (A : Set S) (n : ℕ) :
    MeasurableSet {ω : ℕ → S | (n : WithTop ℕ) < hittingTime A ω} := by
  simpa only [Set.compl_ofPred, not_le] using (measurableSet_hittingTime_le A n).compl

omit [Nonempty S] in
/-- Tonelli's formula for the expected duration. -/
theorem meanHittingTime_tail_sum (P : StochasticMatrix S) (A : Set S) (i : S) :
    meanHittingTime P A i =
      ∑' n : ℕ, statePathLaw P i {ω | (n : WithTop ℕ) < hittingTime A ω} := by
  unfold meanHittingTime hittingDuration
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    simpa [Set.indicator] using
      (lintegral_indicator_one (μ := statePathLaw P i) (measurableSet_hittingTime_gt A n))
  · intro n
    exact (Measurable.ite (measurableSet_hittingTime_gt A n)
      measurable_const measurable_const).aemeasurable

local instance mean_statePathLaw_probability (P : StochasticMatrix S) (i : S) :
    IsProbabilityMeasure (statePathLaw P i) := pathLaw_probability P (PMF.pure i)

/-- Entrance at time zero kills every survival probability. -/
theorem hitting_survival_boundary (P : StochasticMatrix S) (A : Set S) (i : S)
    (hi : i ∈ A) (n : ℕ) :
    statePathLaw P i {ω | (n : WithTop ℕ) < hittingTime A ω} = 0 := by
  rw [← measure_empty (μ := statePathLaw P i)]
  apply measure_congr
  filter_upwards [coordinate_zero_ae P i] with ω hω
  apply propext
  simp only [Set.mem_empty_iff_false, iff_false, not_lt]
  exact (hittingTime_le_iff A ω n).mpr ⟨0, Nat.zero_le _, hω ▸ hi⟩

theorem hitting_survival_zero (P : StochasticMatrix S) (A : Set S) (i : S)
    (hi : i ∉ A) :
    statePathLaw P i {ω | ((0 : ℕ) : WithTop ℕ) < hittingTime A ω} = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_hittingTime_gt A 0)).mp
  filter_upwards [coordinate_zero_ae P i] with ω hω
  simpa only [← not_le, hittingTime_le_iff, Nat.le_zero, exists_eq_left,
    hω] using hi

/-- First-step recursion for the survival tails, including infinite entrance times. -/
theorem hitting_survival_step (P : StochasticMatrix S) (A : Set S) (i : S)
    (hi : i ∉ A) (n : ℕ) :
    statePathLaw P i {ω | ((n + 1 : ℕ) : WithTop ℕ) < hittingTime A ω} =
      ∑' j, P i j * statePathLaw P j {ω | (n : WithTop ℕ) < hittingTime A ω} := by
  rw [← hitting_first_step P i _ (measurableSet_hittingTime_gt A n)]
  apply measure_congr
  filter_upwards [coordinate_zero_ae P i] with ω hω
  apply propext
  simp only [← not_le, hittingTime_le_iff]
  apply not_congr
  constructor
  · rintro ⟨k, hk, hkA⟩
    cases k with
    | zero => exact (hi (hω ▸ hkA)).elim
    | succ k => exact ⟨k, Nat.le_of_succ_le_succ hk, by simpa [Nat.add_comm] using hkA⟩
  · rintro ⟨k, hk, hkA⟩
    exact ⟨1 + k, by omega, hkA⟩

theorem meanHittingTime_boundary (P : StochasticMatrix S) (A : Set S) (i : S)
    (hi : i ∈ A) : meanHittingTime P A i = 0 := by
  rw [meanHittingTime_tail_sum]
  simp only [hitting_survival_boundary P A i hi, tsum_zero]

theorem meanHittingTime_equation (P : StochasticMatrix S) (A : Set S) (i : S)
    (hi : i ∉ A) : meanHittingTime P A i = 1 + action P (meanHittingTime P A) i := by
  rw [meanHittingTime_tail_sum, tsum_eq_zero_add' ENNReal.summable,
    hitting_survival_zero P A i hi]
  congr 1
  simp_rw [hitting_survival_step P A i hi]
  rw [ENNReal.tsum_comm]
  unfold action
  apply tsum_congr
  intro j
  rw [meanHittingTime_tail_sum, ENNReal.tsum_mul_left]

/-- Finite sums of tails are the expectations of truncated durations. -/
theorem hitting_survival_partial_le (P : StochasticMatrix S) (A : Set S)
    (v : S → ℝ≥0∞) (_hA : ∀ i ∈ A, v i = 0)
    (hv : ∀ i, i ∉ A → v i = 1 + action P v i) (N : ℕ) (i : S) :
    ∑ n ∈ Finset.range N,
      statePathLaw P i {ω | (n : WithTop ℕ) < hittingTime A ω} ≤ v i := by
  induction N generalizing i with
  | zero => simp
  | succ N ih =>
    by_cases hi : i ∈ A
    · simp [hitting_survival_boundary P A i hi]
    · rw [Finset.sum_range_succ', hitting_survival_zero P A i hi, hv i hi]
      simp_rw [hitting_survival_step P A i hi]
      rw [add_comm]
      apply add_le_add_right
      calc
        _ = ∑' j, P i j * ∑ n ∈ Finset.range N,
            statePathLaw P j {ω | (n : WithTop ℕ) < hittingTime A ω} := by
          rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          apply tsum_congr
          intro j
          rw [Finset.mul_sum]
        _ ≤ action P v i :=
          ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (ih j)

theorem meanHittingTime_least (P : StochasticMatrix S) (A : Set S) (v : S → ℝ≥0∞)
    (hA : ∀ i ∈ A, v i = 0) (hv : ∀ i, i ∉ A → v i = 1 + action P v i)
    (i : S) : meanHittingTime P A i ≤ v i := by
  rw [meanHittingTime_tail_sum, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => hitting_survival_partial_le P A v hA hv N i

theorem meanHittingTime_empty (P : StochasticMatrix S) (i : S) :
    meanHittingTime P ∅ i = ⊤ := by
  have hd : ∀ ω : ℕ → S, hittingDuration (∅ : Set S) ω = ⊤ := by
    intro ω
    apply hittingDuration_at_top
    simp [hittingTime, hittingAfter_empty]
  simp [meanHittingTime, hd]

theorem meanHittingTime_univ (P : StochasticMatrix S) (i : S) :
    meanHittingTime P Set.univ i = 0 :=
  meanHittingTime_boundary P Set.univ i (Set.mem_univ i)

end
end P207.Markov
