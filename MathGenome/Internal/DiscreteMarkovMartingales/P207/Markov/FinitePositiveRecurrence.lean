import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.FinitePositiveRecurrence
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.RecurrenceInterfaces
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.MeanHittingTime
import Mathlib.Tactic.Linarith

open MeasureTheory Filter
open scoped ENNReal MeasureTheory Classical
set_option backward.isDefEq.respectTransparency false
universe u
namespace P207.Markov
noncomputable section

namespace FinitePositiveRecurrence

variable {S : Type u} [Fintype S] [Nonempty S]

omit [Nonempty S] in
/-- Iterating a one-step subsolution against a stochastic matrix. -/
lemma subsolution_iterate (P : StochasticMatrix S) (f : S → ℝ)
    (hf : ∀ i, f i ≤ 1 + ∑ x, realMatrix P i x * f x) (n : ℕ) (i : S) :
    f i ≤ n + ∑ x, realMatrix (power P n) i x * f x := by
  induction n generalizing i with
  | zero =>
    simp [power_zero, realMatrix, identity_apply, apply_ite]
  | succ n ih =>
    calc
      f i ≤ 1 + ∑ x, realMatrix P i x * f x := hf i
      _ ≤ 1 + ∑ x, realMatrix P i x *
          ((n : ℝ) + ∑ y, realMatrix (power P n) x y * f y) := by
        gcongr with x
        exacts [realMatrix_nonneg P i x, ih x]
      _ = (n + 1 : ℕ) + ∑ y, realMatrix (power P (n + 1)) i y * f y := by
        have hp : power P (n + 1) = comp P (power P n) := by
          simpa [power_one, Nat.add_comm] using power_add P 1 n
        rw [hp]
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
          realMatrix_finite_rowsum, one_mul, realMatrix_comp_tsum, tsum_fintype]
        simp_rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
        push_cast
        ring

/-- Finite maximum principle with an absorbing boundary value.
The bound depends on the matrix and target, and is uniform over subsolutions. -/
lemma subsolution_bound (P : StochasticMatrix S) (hP : Irreducible P) (j : S) :
    ∃ B : ℝ, ∀ f : S → ℝ, f j = 0 →
      (∀ i, f i ≤ 1 + ∑ x, realMatrix P i x * f x) → ∀ i, f i ≤ B := by
  choose n hn using fun i => (hP i j).1
  let b : S → ℝ := fun i => (n i : ℝ) / realMatrix (power P (n i)) i j
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ b Finset.univ_nonempty
  refine ⟨b k, ?_⟩
  intro f hfj hf i
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hfa : ∀ x, f x ≤ f a := fun x => ha x (Finset.mem_univ x)
  have hp : 0 < realMatrix (power P (n a)) a j :=
    ENNReal.toReal_pos (ne_of_gt (hn a)) (entry_ne_top _ _ _)
  have hs : ∑ x, realMatrix (power P (n a)) a x * f x ≤
      f a - realMatrix (power P (n a)) a j * f a := by
    calc
      _ ≤ ∑ x, realMatrix (power P (n a)) a x *
          (f a - if x = j then f a else 0) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (realMatrix_nonneg _ _ _)
        by_cases hx : x = j
        · simp [hx, hfj]
        · simpa [hx] using hfa x
      _ = _ := by
        simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
          realMatrix_finite_rowsum, mul_ite]
  have ht := subsolution_iterate P f hf (n a) a
  have hb : f a ≤ b a := (le_div_iff₀ hp).mpr (by linarith)
  exact (hfa i).trans (hb.trans (hk a (Finset.mem_univ a)))

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

local instance finite_statePathLaw_probability (P : StochasticMatrix S) (i : S) :
    IsProbabilityMeasure (statePathLaw P i) := pathLaw_probability P (PMF.pure i)

/-- The real expectation of a truncated entrance time. -/
def truncatedMean (P : StochasticMatrix S) (j : S) (N : ℕ) (i : S) : ℝ :=
  ∑ n ∈ Finset.range N,
    (statePathLaw P i {ω | (n : WithTop ℕ) < hittingTime {j} ω}).toReal

omit [Nonempty S] in
lemma truncatedMean_nonneg (P : StochasticMatrix S) (j : S) (N : ℕ) (i : S) :
    0 ≤ truncatedMean P j N i := by
  exact Finset.sum_nonneg fun n _ => ENNReal.toReal_nonneg

lemma truncatedMean_boundary (P : StochasticMatrix S) (j : S) (N : ℕ) :
    truncatedMean P j N j = 0 := by
  simp [truncatedMean, hitting_survival_boundary P {j} j (Set.mem_singleton j)]

lemma truncatedMean_step (P : StochasticMatrix S) (j : S) (N : ℕ) (i : S)
    (hi : i ≠ j) :
    truncatedMean P j (N + 1) i =
      1 + ∑ x, realMatrix P i x * truncatedMean P j N x := by
  have hi' : i ∉ ({j} : Set S) := hi
  unfold truncatedMean
  rw [Finset.sum_range_succ', hitting_survival_zero P {j} i hi']
  simp_rw [hitting_survival_step P {j} i hi', tsum_fintype,
    ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top (entry_ne_top _ _ _)
      (measure_ne_top _ _)), ENNReal.toReal_mul]
  simp only [ENNReal.toReal_one]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  rw [add_comm]
  rfl

lemma truncatedMean_subsolution (P : StochasticMatrix S) (j : S) (N : ℕ) (i : S) :
    truncatedMean P j N i ≤
      1 + ∑ x, realMatrix P i x * truncatedMean P j N x := by
  by_cases hi : i = j
  · subst i
    rw [truncatedMean_boundary]
    have hs : 0 ≤ ∑ x, realMatrix P j x * truncatedMean P j N x :=
      Finset.sum_nonneg fun x _ => mul_nonneg (realMatrix_nonneg P j x)
        (truncatedMean_nonneg P j N x)
    linarith
  · calc
      _ ≤ truncatedMean P j (N + 1) i := by
        unfold truncatedMean
        rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_right ENNReal.toReal_nonneg
      _ = _ := truncatedMean_step P j N i hi

/-- A uniform bound on the truncations passes to the extended expectation. -/
lemma meanHittingTime_finite (P : StochasticMatrix S) (hP : Irreducible P) (i j : S) :
    meanHittingTime P {j} i < ⊤ := by
  obtain ⟨B, hB⟩ := subsolution_bound P hP j
  have hbound (N : ℕ) : truncatedMean P j N i ≤ B :=
    hB _ (truncatedMean_boundary P j N) (truncatedMean_subsolution P j N) i
  have hle : meanHittingTime P {j} i ≤ ENNReal.ofReal B := by
    rw [meanHittingTime_tail_sum, ENNReal.tsum_eq_iSup_nat]
    apply iSup_le
    intro N
    calc
      _ = ENNReal.ofReal (truncatedMean P j N i) := by
        rw [truncatedMean, ENNReal.ofReal_sum_of_nonneg
          (fun n _ => ENNReal.toReal_nonneg)]
        simp only [ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hbound N)
  exact hle.trans_lt ENNReal.ofReal_lt_top

omit [Fintype S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- A positive return is bounded by one step followed by an entrance time.
This pointwise bound also covers paths with an infinite entrance time. -/
lemma returnDuration_le (j : S) (ω : ℕ → S) :
    ENat.toENNReal (returnTime j ω) ≤
      1 + hittingDuration {j} (fun k => ω (1 + k)) := by
  by_cases ht : hittingTime {j} (fun k => ω (1 + k)) = ⊤
  · simp [hittingDuration_at_top _ _ ht]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ht
    have hhit : hittingTime {j} (fun k => ω (1 + k)) ≤ n := le_of_eq hn.symm
    obtain ⟨k, hk, hkj⟩ := (hittingTime_le_iff _ _ _).mp hhit
    have hret : returnTime j ω ≤ ((1 + n : ℕ) : WithTop ℕ) := by
      apply (positiveReturnTime_le_iff coordinate j ω (1 + n)).mpr
      exact ⟨1 + k, by omega, by omega, hkj⟩
    calc
      _ ≤ ENat.toENNReal ((1 + n : ℕ) : WithTop ℕ) := ENat.toENNReal_mono hret
      _ = 1 + hittingDuration {j} (fun k => ω (1 + k)) := by
        rw [hittingDuration_at_finite _ _ n hn.symm]
        norm_cast

/-- First-step disintegration for the nonnegative entrance duration. -/
lemma shifted_hittingDuration_integral (P : StochasticMatrix S) (i j : S) :
    (∫⁻ ω, hittingDuration {j} (fun k => ω (1 + k)) ∂statePathLaw P i) =
      ∑' x, P i x * meanHittingTime P {j} x := by
  let shift : (ℕ → S) → (ℕ → S) := fun ω k => ω (1 + k)
  have hshift : Measurable shift :=
    measurable_pi_iff.mpr fun k => measurable_pi_apply (1 + k)
  unfold hittingDuration
  rw [lintegral_tsum]
  · calc
      _ = ∑' n : ℕ, statePathLaw P i
          {ω | (n : WithTop ℕ) < hittingTime {j} (shift ω)} := by
        apply tsum_congr
        intro n
        simpa [Set.indicator, shift] using
          lintegral_indicator_one (μ := statePathLaw P i)
            ((measurableSet_hittingTime_gt ({j} : Set S) n).preimage hshift)
      _ = ∑' n : ℕ, ∑' x, P i x * statePathLaw P x
          {ω | (n : WithTop ℕ) < hittingTime {j} ω} := by
        apply tsum_congr
        intro n
        exact hitting_first_step P i _ (measurableSet_hittingTime_gt _ n)
      _ = _ := by
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro x
        rw [meanHittingTime_tail_sum, ENNReal.tsum_mul_left]
  · intro n
    exact (Measurable.ite
      ((measurableSet_hittingTime_gt ({j} : Set S) n).preimage hshift)
      measurable_const measurable_const).aemeasurable

lemma meanReturnTime_finite (P : StochasticMatrix S) (hP : Irreducible P) (j : S) :
    meanReturnTime P j < ⊤ := by
  have hle : meanReturnTime P j ≤ 1 + ∑' x, P j x * meanHittingTime P {j} x := by
    calc
      _ ≤ ∫⁻ ω, 1 + hittingDuration {j} (fun k => ω (1 + k))
          ∂statePathLaw P j := lintegral_mono (returnDuration_le j)
      _ = _ := by
        rw [lintegral_add_left measurable_const, shifted_hittingDuration_integral]
        simp
  apply hle.trans_lt
  rw [tsum_fintype]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.one_lt_top
  · apply (ENNReal.sum_lt_top).mpr
    intro x _
    exact ENNReal.mul_lt_top (entry_ne_top P j x).lt_top
      (meanHittingTime_finite P hP x j)

end FinitePositiveRecurrence

/-- Every singleton entrance time has finite mean in a finite irreducible chain. -/
theorem finite_meanHittingTime_lt_top : FinitePositiveRecurrenceSpec.meanHittingTime_lt_top.{u} := by
  intro S _ _ _ _ P hP i j
  let _ := Fintype.ofFinite S
  exact FinitePositiveRecurrence.meanHittingTime_finite P hP i j

/-- Positive return has finite mean, including for a one-state chain. -/
theorem finite_meanReturnTime_lt_top : FinitePositiveRecurrenceSpec.meanReturnTime_lt_top.{u} := by
  intro S _ _ _ _ P hP j
  let _ := Fintype.ofFinite S
  exact FinitePositiveRecurrence.meanReturnTime_finite P hP j

/-- Every state of a finite irreducible chain is positive recurrent. -/
theorem finite_irreducible_positiveRecurrent : FinitePositiveRecurrenceSpec.positiveRecurrent.{u} := by
  exact finite_meanReturnTime_lt_top

end
end P207.Markov
