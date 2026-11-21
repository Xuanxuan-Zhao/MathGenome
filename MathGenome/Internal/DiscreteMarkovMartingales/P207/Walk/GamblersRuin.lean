import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.GamblersRuin
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.RuinAbsorption
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.Ring

open MeasureTheory Filter
open scoped ENNReal

namespace P207.Walk
noncomputable section

local instance ruin_exit_probability_measure (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) : IsProbabilityMeasure (Markov.statePathLaw (ruinKernel N p hp hp1) i) :=
  Markov.pathLaw_probability _ (PMF.pure i)

namespace GamblersRuin
abbrev probability : GamblersRuinSpec.probabilityType := ruinExitProbability
end GamblersRuin

/-- A strict comparison of entrance times as a countable union of finite tests. -/
theorem hittingTime_lt_iff_race {S : Type*} (A B : Set S) (ω : ℕ → S) :
    Markov.hittingTime A ω < Markov.hittingTime B ω ↔
      ∃ n : ℕ, ω n ∈ A ∧ ∀ k ≤ n, ω k ∉ B := by
  constructor
  · intro h
    generalize ht : Markov.hittingTime A ω = t at h
    induction t using WithTop.recTopCoe with
    | top => exact (not_lt_of_ge le_top h).elim
    | coe n =>
      obtain ⟨k, hk, hkA⟩ := (Markov.hittingTime_le_iff A ω n).mp ht.le
      refine ⟨k, hkA, ?_⟩
      intro j hj hjB
      have hB := (Markov.hittingTime_le_iff B ω n).mpr ⟨j, hj.trans hk, hjB⟩
      exact (not_le_of_gt h) hB
  · rintro ⟨n, hnA, hnB⟩
    have hA := (Markov.hittingTime_le_iff A ω n).mpr ⟨n, le_rfl, hnA⟩
    apply hA.trans_lt
    apply lt_of_not_ge
    intro hB
    obtain ⟨k, hk, hkB⟩ := (Markov.hittingTime_le_iff B ω n).mp hB
    exact hnB k hk hkB

theorem measurableSet_hittingTime_race {S : Type*} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (A B : Set S) :
    MeasurableSet {ω : ℕ → S | Markov.hittingTime A ω < Markov.hittingTime B ω} := by
  have he : {ω : ℕ → S | Markov.hittingTime A ω < Markov.hittingTime B ω} =
      ⋃ n : ℕ, {ω | ω n ∈ A} ∩ {ω | ¬ Markov.hittingTime B ω ≤ n} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      hittingTime_lt_iff_race, Markov.hittingTime_le_iff, not_exists, not_and]
  rw [he]
  exact MeasurableSet.iUnion fun n =>
    ((measurable_pi_apply n) (Set.to_countable A).measurableSet).inter
      (Markov.measurableSet_hittingTime_le B n).compl

private theorem race_shift {S : Type*} (A B : Set S) (ω : ℕ → S)
    (hA : ω 0 ∉ A) (hB : ω 0 ∉ B) :
    (Markov.hittingTime A ω < Markov.hittingTime B ω) ↔
      Markov.hittingTime A (fun k => ω (1 + k)) <
        Markov.hittingTime B (fun k => ω (1 + k)) := by
  simp only [hittingTime_lt_iff_race]
  constructor
  · rintro ⟨n, hn, h⟩
    cases n with
    | zero => exact (hA hn).elim
    | succ n =>
      refine ⟨n, by simpa [Nat.add_comm] using hn, ?_⟩
      intro k hk
      exact h (1 + k) (by omega)
  · rintro ⟨n, hn, h⟩
    refine ⟨1 + n, hn, ?_⟩
    intro k hk
    cases k with
    | zero => exact hB
    | succ k => simpa [Nat.add_comm] using h k (by omega)

theorem ruinExitProbability_zero : GamblersRuinSpec.exit_zero := by
  intro N hN p hp hp1
  unfold ruinExitProbability
  have he : Markov.statePathLaw (ruinKernel N p hp hp1) 0
      {ω | Markov.hittingTime {Fin.last N} ω < Markov.hittingTime {0} ω} = 0 := by
    rw [← measure_empty (μ := Markov.statePathLaw (ruinKernel N p hp hp1) 0)]
    apply measure_congr
    filter_upwards [Markov.coordinate_zero_ae (ruinKernel N p hp hp1) 0] with ω hω
    apply propext
    simp only [Set.mem_empty_iff_false, iff_false]
    rw [hittingTime_lt_iff_race]
    rintro ⟨n, _, hn⟩
    exact hn 0 (Nat.zero_le n) (by simp [hω])
  simp [he]

theorem ruinExitProbability_last : GamblersRuinSpec.exit_last := by
  intro N hN p hp hp1
  unfold ruinExitProbability
  have he : Markov.statePathLaw (ruinKernel N p hp hp1) (Fin.last N)
      {ω | Markov.hittingTime {Fin.last N} ω < Markov.hittingTime {0} ω} = 1 := by
    apply (mem_ae_iff_prob_eq_one (measurableSet_hittingTime_race _ _)).mp
    filter_upwards [Markov.coordinate_zero_ae (ruinKernel N p hp hp1) (Fin.last N)] with ω hω
    rw [hittingTime_lt_iff_race]
    refine ⟨0, by simp [hω], ?_⟩
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp only [hω, Set.mem_singleton_iff]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp [he]

theorem ruinExitProbability_step (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) (hi : i ∉ ruinBoundary N) :
    ruinExitProbability N p hp hp1 i =
      p * ruinExitProbability N p hp hp1 (ruinRight i) +
      (1 - p) * ruinExitProbability N p hp hp1 (ruinLeft i) := by
  let B : Set (ℕ → RuinState N) :=
    {ω | Markov.hittingTime {Fin.last N} ω < Markov.hittingTime {0} ω}
  have he : Markov.statePathLaw (ruinKernel N p hp hp1) i B =
      Markov.action (ruinKernel N p hp hp1)
        (fun j => Markov.statePathLaw (ruinKernel N p hp hp1) j B) i := by
    rw [Markov.action, ← Markov.hitting_first_step _ i B (measurableSet_hittingTime_race _ _)]
    apply measure_congr
    filter_upwards [Markov.coordinate_zero_ae (ruinKernel N p hp hp1) i] with ω hω
    apply propext
    apply race_shift
    · simp only [hω, Set.mem_singleton_iff]
      intro h
      exact hi (Or.inr (congrArg Fin.val h))
    · simp only [hω, Set.mem_singleton_iff]
      intro h
      exact hi (Or.inl (congrArg Fin.val h))
  rw [ruinKernel_action N p hp hp1 i hi] at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal (sub_nonneg.mpr hp1.le)] at hr
  exact hr

/-- The difference equation determines all increments from the first one. -/
theorem ruin_recurrence_increments (N : ℕ) (p : ℝ) (hp : p ≠ 0) (u : ℕ → ℝ)
    (h0 : u 0 = 0)
    (hs : ∀ k, 0 < k → k < N → u k = p * u (k + 1) + (1 - p) * u (k - 1))
    (k : ℕ) (hk : k + 1 ≤ N) :
    u (k + 1) - u k = ((1 - p) / p) ^ k * u 1 := by
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    have hd := ih (by omega)
    have he := hs (k + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at he
    rw [pow_succ]
    apply (mul_left_cancel₀ hp)
    have hr : p * ((1 - p) / p) = 1 - p := mul_div_cancel₀ _ hp
    calc
      p * (u (k + 1 + 1) - u (k + 1)) = (1 - p) * (u (k + 1) - u k) := by
        nlinarith [he]
      _ = (1 - p) * (((1 - p) / p) ^ k * u 1) := by rw [hd]
      _ = p * (((1 - p) / p) ^ k * ((1 - p) / p) * u 1) := by
        rw [show p * (((1 - p) / p) ^ k * ((1 - p) / p) * u 1) =
          (p * ((1 - p) / p)) * (((1 - p) / p) ^ k * u 1) by ring, hr]

/-- Summing the increments gives a geometric sum, including at zero. -/
theorem ruin_recurrence_sum (N : ℕ) (p : ℝ) (hp : p ≠ 0) (u : ℕ → ℝ)
    (h0 : u 0 = 0)
    (hs : ∀ k, 0 < k → k < N → u k = p * u (k + 1) + (1 - p) * u (k - 1))
    (k : ℕ) (hk : k ≤ N) :
    u k = u 1 * ∑ j ∈ Finset.range k, ((1 - p) / p) ^ j := by
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    have hd := ruin_recurrence_increments N p hp u h0 hs k hk
    rw [Finset.sum_range_succ]
    rw [ih (by omega)] at hd
    nlinarith

/-- Solving the two boundary equations without presupposing a probabilistic recurrence. -/
theorem ruin_recurrence_solution (N : ℕ) (hN : 1 ≤ N) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (u : ℕ → ℝ) (h0 : u 0 = 0) (hN1 : u N = 1)
    (hs : ∀ k, 0 < k → k < N → u k = p * u (k + 1) + (1 - p) * u (k - 1))
    (k : ℕ) (hk : k ≤ N) :
    u k = if p = 1 - p then (k : ℝ) / N
      else (1 - ((1 - p) / p) ^ k) / (1 - ((1 - p) / p) ^ N) := by
  let r := (1 - p) / p
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hp1.le) hp.le
  have hsum : (∑ j ∈ Finset.range N, r ^ j) ≠ 0 :=
    ne_of_gt (geom_sum_pos hr (by omega))
  have htotal := ruin_recurrence_sum N p hp.ne' u h0 hs N le_rfl
  rw [hN1] at htotal
  have hone : u 1 = 1 / (∑ j ∈ Finset.range N, r ^ j) := by
    apply (eq_div_iff hsum).mpr
    exact htotal.symm
  rw [ruin_recurrence_sum N p hp.ne' u h0 hs k hk, hone]
  change 1 / (∑ j ∈ Finset.range N, r ^ j) * (∑ j ∈ Finset.range k, r ^ j) = _
  by_cases he : p = 1 - p
  · rw [ite_eq_left he]
    have hr1 : r = 1 := (div_eq_one_iff_eq hp.ne').mpr he.symm
    simp [hr1, div_eq_mul_inv, mul_comm]
  · rw [ite_eq_right he]
    have hr1 : r ≠ 1 := by
      intro h
      exact he ((div_eq_one_iff_eq hp.ne').mp h).symm
    have hden : 1 - r ^ N ≠ 0 := by
      rw [← geom_sum_mul_neg r N]
      exact mul_ne_zero hsum (sub_ne_zero.mpr (Ne.symm hr1))
    change _ = (1 - r ^ k) / (1 - r ^ N)
    apply (eq_div_iff hden).mpr
    rw [← geom_sum_mul_neg r N, ← geom_sum_mul_neg r k]
    field_simp

private def intervalState (N k : ℕ) : RuinState N :=
  ⟨min k N, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The actual exit probabilities, rather than an assumed solution of a recurrence. -/
theorem gamblers_ruin : GamblersRuinSpec.gamblers_ruin := by
  intro N hN p hp hp1 i
  let u : ℕ → ℝ := fun k => ruinExitProbability N p hp hp1 (intervalState N k)
  have h0 : u 0 = 0 := by
    have he : intervalState N 0 = 0 := by apply Fin.ext; simp [intervalState]
    change ruinExitProbability N p hp hp1 (intervalState N 0) = 0
    rw [he]
    exact ruinExitProbability_zero N hN p hp hp1
  have hlast : u N = 1 := by
    have he : intervalState N N = Fin.last N := by apply Fin.ext; simp [intervalState]
    change ruinExitProbability N p hp hp1 (intervalState N N) = 1
    rw [he]
    exact ruinExitProbability_last N hN p hp hp1
  have hs : ∀ k, 0 < k → k < N → u k = p * u (k + 1) + (1 - p) * u (k - 1) := by
    intro k hk hkN
    have hi : intervalState N k ∉ ruinBoundary N := by
      simp only [ruinBoundary, Set.mem_ofPred_eq, intervalState, min_eq_left hkN.le]
      omega
    have hR : ruinRight (intervalState N k) = intervalState N (k + 1) := by
      apply Fin.ext
      simp [ruinRight, intervalState, min_eq_left hkN.le]
    have hL : ruinLeft (intervalState N k) = intervalState N (k - 1) := by
      apply Fin.ext
      simp [ruinLeft, intervalState, min_eq_left hkN.le, min_eq_left (show k - 1 ≤ N by omega)]
    have he := ruinExitProbability_step N p hp hp1 (intervalState N k) hi
    rw [hR, hL] at he
    exact he
  have hi : intervalState N i.val = i := by
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt_succ i.isLt)
  have he := ruin_recurrence_solution N hN p hp hp1 u h0 hlast hs i.val
    (Nat.le_of_lt_succ i.isLt)
  change ruinExitProbability N p hp hp1 (intervalState N i.val) = _ at he
  rwa [hi] at he

end
end P207.Walk
