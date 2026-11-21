import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.IntegerHitting
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.GamblersRuin
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.RecurrenceInterfaces
import Mathlib.Analysis.SpecificLimits.Basic
import Batteries.Tactic.OpenPrivate
import Mathlib.Probability.Independence.InfinitePi

/-! The hitting formulas follow from the least-nonnegative harmonic solution
and the bounded half-line recurrence. The finite-interval exit race is identified
independently by the two boundary values and uniqueness of that recurrence.
The canonical path law is also realized as the cumulative sum of product moves,
which proves the asserted independent-increment model. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace P207.Walk
noncomputable section

namespace IntegerHitting
abbrev kernel : IntegerHittingSpec.kernelType := integerKernel
abbrev law : IntegerHittingSpec.lawType := integerLaw
abbrev increment : IntegerHittingSpec.incrementType := integerIncrement
abbrev probability : IntegerHittingSpec.probabilityType := integerHittingProbability
end IntegerHitting

theorem integerKernel_mass : IntegerHittingSpec.kernel_mass := by
  intro p hp hp1 i j
  unfold integerKernel
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, ruinCoin, PMF.ofFintype_apply]

theorem integerKernel_action (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : ℤ) (f : ℤ → ℝ≥0∞) :
    Markov.action (integerKernel p hp hp1) f i =
      ENNReal.ofReal p * f (i + 1) + ENNReal.ofReal (1 - p) * f (i - 1) := by
  unfold Markov.action
  simp_rw [integerKernel_mass p hp hp1 i, add_mul, ite_mul, zero_mul]
  rw [ENNReal.tsum_add]
  simp

theorem integer_natural_chain : IntegerHittingSpec.natural_chain := by
  intro p hp hp1 i
  exact Markov.coordinate_isMarkovChain _ (PMF.pure i)

theorem integerHittingProbability_zero : IntegerHittingSpec.hit_zero := by
  intro p hp hp1
  unfold integerHittingProbability
  rw [Markov.hittingProbability_boundary _ _ _ (by simp)]
  exact ENNReal.toReal_one

theorem integerHittingProbability_nonneg (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : ℤ) :
    0 ≤ integerHittingProbability p hp hp1 i := ENNReal.toReal_nonneg

theorem integerHittingProbability_le_one (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : ℤ) :
    integerHittingProbability p hp hp1 i ≤ 1 := by
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  simpa using Markov.hittingProbability_le_one (integerKernel p hp hp1) {0} i

/-- The bounded hitting probabilities satisfy the unrestricted difference equation. -/
theorem integerHittingProbability_step (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : ℤ) (hi : i ≠ 0) :
    integerHittingProbability p hp hp1 i =
      p * integerHittingProbability p hp hp1 (i + 1) +
      (1 - p) * integerHittingProbability p hp hp1 (i - 1) := by
  have he := Markov.hittingProbability_harmonic (integerKernel p hp hp1) {0} i hi
  rw [integerKernel_action] at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lt_top_iff_ne_top.mp
      ((Markov.hittingProbability_le_one _ _ _).trans_lt (by simp))))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lt_top_iff_ne_top.mp
      ((Markov.hittingProbability_le_one _ _ _).trans_lt (by simp)))),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal (sub_nonneg.mpr hp1.le)] at hr
  exact hr

/-- Summing the geometric increments of the deficit from the boundary value. -/
theorem harmonic_deficit_sum (p : ℝ) (hp : 0 < p) (u : ℕ → ℝ)
    (h0 : u 0 = 1)
    (hs : ∀ k, 0 < k → u k = p * u (k + 1) + (1 - p) * u (k - 1))
    (k : ℕ) :
    1 - u k = (1 - u 1) * ∑ j ∈ Finset.range k, ((1 - p) / p) ^ j := by
  apply ruin_recurrence_sum (k + 1) p hp.ne' (fun n => 1 - u n)
    (by simp [h0])
  · intro n hn _
    have := hs n hn
    nlinarith
  · omega

/-- A bounded harmonic function with boundary value one must be identically one
on the half line when its drift is toward that boundary (including zero drift). -/
theorem bounded_harmonic_eq_one (p : ℝ) (hp : 0 < p) (hdrift : p ≤ 1 - p)
    (u : ℕ → ℝ) (h0 : u 0 = 1) (hb : ∀ n, 0 ≤ u n ∧ u n ≤ 1)
    (hs : ∀ k, 0 < k → u k = p * u (k + 1) + (1 - p) * u (k - 1)) :
    ∀ k, u k = 1 := by
  have hr : 1 ≤ (1 - p) / p := (le_div_iff₀ hp).mpr (by simpa using hdrift)
  have hnon : 0 ≤ 1 - u 1 := sub_nonneg.mpr (hb 1).2
  have hsum (k : ℕ) : (k : ℝ) ≤ ∑ j ∈ Finset.range k, ((1 - p) / p) ^ j := by
    calc
      (k : ℝ) = ∑ _j ∈ Finset.range k, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun _ _ => one_le_pow₀ hr)
  have hbound (k : ℕ) : (1 - u 1) * (k : ℝ) ≤ 1 := by
    calc
      _ ≤ (1 - u 1) * ∑ j ∈ Finset.range k, ((1 - p) / p) ^ j :=
        mul_le_mul_of_nonneg_left (hsum k) hnon
      _ = 1 - u k := (harmonic_deficit_sum p hp u h0 hs k).symm
      _ ≤ 1 := by linarith [(hb k).1]
  have hfirst : 1 - u 1 = 0 := by
    by_contra h
    have hpos : 0 < 1 - u 1 := lt_of_le_of_ne hnon (Ne.symm h)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - u 1))
    have hlt : 1 < (1 - u 1) * (n : ℝ) := by
      have := (div_lt_iff₀ hpos).mp hn
      nlinarith
    exact (not_lt_of_ge (hbound n)) hlt
  intro k
  have := harmonic_deficit_sum p hp u h0 hs k
  rw [hfirst, zero_mul] at this
  linarith

/-- In the outward drift case boundedness gives the geometric lower bound. -/
theorem bounded_harmonic_ge_pow (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hdrift : 1 - p < p) (u : ℕ → ℝ) (h0 : u 0 = 1)
    (hb : ∀ n, 0 ≤ u n ∧ u n ≤ 1)
    (hs : ∀ k, 0 < k → u k = p * u (k + 1) + (1 - p) * u (k - 1))
    (k : ℕ) : ((1 - p) / p) ^ k ≤ u k := by
  let r := (1 - p) / p
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hp1.le) hp.le
  have hr1 : r < 1 := (div_lt_one hp).mpr hdrift
  have he (n : ℕ) : (1 - u n) * (1 - r) = (1 - u 1) * (1 - r ^ n) := by
    rw [harmonic_deficit_sum p hp u h0 hs n]
    change ((1 - u 1) * ∑ j ∈ Finset.range n, r ^ j) * (1 - r) = _
    rw [mul_assoc, geom_sum_mul_neg]
  have hbound (n : ℕ) : (1 - u 1) * (1 - r ^ n) ≤ 1 - r := by
    rw [← he n]
    exact mul_le_of_le_one_left (sub_nonneg.mpr hr1.le) (by linarith [(hb n).1])
  have hlim : Tendsto (fun n : ℕ => (1 - u 1) * (1 - r ^ n)) atTop (𝓝 (1 - u 1)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)).const_mul (1 - u 1)
  have hfirst : 1 - u 1 ≤ 1 - r := le_of_tendsto' hlim hbound
  have hkpow : 0 ≤ 1 - r ^ k := sub_nonneg.mpr (pow_le_one₀ hr0 hr1.le)
  have := mul_le_mul_of_nonneg_right hfirst hkpow
  rw [← he k] at this
  nlinarith [sub_pos.mpr hr1]

/-- Transfer the least-nonnegative-solution theorem to ordinary real functions. -/
theorem integerHittingProbability_le_solution (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (v : ℤ → ℝ) (hv0 : v 0 = 1) (hv : ∀ i, 0 ≤ v i)
    (hs : ∀ i, i ≠ 0 → v i = p * v (i + 1) + (1 - p) * v (i - 1))
    (i : ℤ) : integerHittingProbability p hp hp1 i ≤ v i := by
  apply ENNReal.toReal_le_of_le_ofReal (hv i)
  apply Markov.hittingProbability_least (integerKernel p hp hp1) {0}
    (fun j => ENNReal.ofReal (v j))
  · intro j hj
    simpa only [Set.mem_singleton_iff] using hj ▸ (show ENNReal.ofReal (v 0) = 1 by simp [hv0])
  · intro j hj
    rw [integerKernel_action, hs j hj,
      ENNReal.ofReal_add (mul_nonneg hp.le (hv _))
        (mul_nonneg (sub_nonneg.mpr hp1.le) (hv _)),
      ENNReal.ofReal_mul hp.le, ENNReal.ofReal_mul (sub_nonneg.mpr hp1.le)]

/-- The geometric solution extended constantly to the negative half line is
harmonic away from zero. No boundary condition is imposed at infinity. -/
theorem geometric_halfLine_harmonic (p : ℝ) (hp : 0 < p) (i : ℤ) (hi : i ≠ 0) :
    ((1 - p) / p) ^ i.toNat =
      p * ((1 - p) / p) ^ (i + 1).toNat +
      (1 - p) * ((1 - p) / p) ^ (i - 1).toNat := by
  by_cases hpos : 0 < i
  · have hiNat : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hpos.le
    have hn : 0 < i.toNat := by omega
    have hR : (i + 1).toNat = i.toNat + 1 := by omega
    have hL : (i - 1).toNat = i.toNat - 1 := by omega
    rw [hR, hL]
    have hpow : ((1 - p) / p) ^ i.toNat =
        ((1 - p) / p) ^ (i.toNat - 1) * ((1 - p) / p) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [pow_succ, hpow]
    field_simp
    ring
  · have h0 : i.toNat = 0 := by omega
    have hR : (i + 1).toNat = 0 := by omega
    have hL : (i - 1).toNat = 0 := by omega
    simp [h0, hR, hL]

theorem integerHittingProbability_le_pow (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : ℤ) :
    integerHittingProbability p hp hp1 i ≤ ((1 - p) / p) ^ i.toNat := by
  apply integerHittingProbability_le_solution p hp hp1
    (fun j => ((1 - p) / p) ^ j.toNat) (by simp)
  · intro j
    exact pow_nonneg (div_nonneg (sub_nonneg.mpr hp1.le) hp.le) _
  · exact geometric_halfLine_harmonic p hp

/-- Both sides use the same bounded half-line recurrence; reflection exchanges
the right and left coefficients. -/
theorem integerHittingProbability_positive : IntegerHittingSpec.hit_positive := by
  intro p hp hp1 i hi
  let u : ℕ → ℝ := fun n => integerHittingProbability p hp hp1 (n : ℤ)
  have h0 : u 0 = 1 := integerHittingProbability_zero p hp hp1
  have hb (n : ℕ) : 0 ≤ u n ∧ u n ≤ 1 :=
    ⟨integerHittingProbability_nonneg p hp hp1 n, integerHittingProbability_le_one p hp hp1 n⟩
  have hs (n : ℕ) (hn : 0 < n) :
      u n = p * u (n + 1) + (1 - p) * u (n - 1) := by
    have he := integerHittingProbability_step p hp hp1 (n : ℤ) (by omega)
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    simpa only [u, Nat.cast_add, Nat.cast_one, hcast] using he
  have hiNat : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi.le
  by_cases hdrift : 1 - p < p
  · rw [ite_eq_left hdrift]
    apply le_antisymm (integerHittingProbability_le_pow p hp hp1 i)
    simpa only [u, hiNat] using bounded_harmonic_ge_pow p hp hp1 hdrift u h0 hb hs i.toNat
  · rw [ite_eq_right hdrift]
    simpa only [u, hiNat] using bounded_harmonic_eq_one p hp (le_of_not_gt hdrift) u h0 hb hs i.toNat

theorem integerHittingProbability_le_reflected_pow (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1) (i : ℤ) :
    integerHittingProbability p hp hp1 i ≤ (p / (1 - p)) ^ (-i).toNat := by
  apply integerHittingProbability_le_solution p hp hp1
    (fun j => (p / (1 - p)) ^ (-j).toNat) (by simp)
  · intro j
    exact pow_nonneg (div_nonneg hp.le (sub_nonneg.mpr hp1.le)) _
  · intro j hj
    have he := geometric_halfLine_harmonic (1 - p) (sub_pos.mpr hp1) (-j)
      (neg_ne_zero.mpr hj)
    have hR : -j + 1 = -(j - 1) := by omega
    have hL : -j - 1 = -(j + 1) := by omega
    rw [sub_sub_cancel, hR, hL] at he
    exact he.trans (add_comm _ _)

theorem integerHittingProbability_negative : IntegerHittingSpec.hit_negative := by
  intro p hp hp1 i hi
  let u : ℕ → ℝ := fun n => integerHittingProbability p hp hp1 (-(n : ℤ))
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hq1 : 1 - p < 1 := by linarith
  have h0 : u 0 = 1 := integerHittingProbability_zero p hp hp1
  have hb (n : ℕ) : 0 ≤ u n ∧ u n ≤ 1 :=
    ⟨integerHittingProbability_nonneg p hp hp1 _, integerHittingProbability_le_one p hp hp1 _⟩
  have hs (n : ℕ) (hn : 0 < n) :
      u n = (1 - p) * u (n + 1) + (1 - (1 - p)) * u (n - 1) := by
    have he := integerHittingProbability_step p hp hp1 (-(n : ℤ)) (by omega)
    have hR : -(n : ℤ) + 1 = -((n - 1 : ℕ) : ℤ) := by omega
    have hL : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hR, hL] at he
    simpa only [sub_sub_cancel, add_comm, u] using he
  have hiNat : (-((-i).toNat : ℤ)) = i := by omega
  by_cases hdrift : p < 1 - p
  · rw [ite_eq_left hdrift]
    apply le_antisymm (integerHittingProbability_le_reflected_pow p hp hp1 i)
    have ht := bounded_harmonic_ge_pow (1 - p) hq hq1 (by linarith) u h0 hb hs (-i).toNat
    simpa only [sub_sub_cancel, u, hiNat] using ht
  · rw [ite_eq_right hdrift]
    have ht := bounded_harmonic_eq_one (1 - p) hq (by linarith) u h0 hb hs (-i).toNat
    simpa only [u, hiNat] using ht

/-- A positive return is precisely an entrance in the future starting at time one. -/
theorem integer_return_finite_shift (ω : ℕ → ℤ) :
    Markov.returnTime 0 ω < ⊤ ↔
      Markov.hittingTime {0} (fun k => ω (1 + k)) < ⊤ := by
  rw [Markov.returnTime, Markov.positiveReturnTime_finite_iff,
    Markov.hittingTime_finite_iff]
  simp only [Markov.coordinate, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n - 1, by simpa only [Nat.add_sub_of_le hn] using h⟩
  · rintro ⟨n, hn⟩
    exact ⟨1 + n, by omega, hn⟩

theorem integer_return_first_step (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (Markov.returnProbability (integerKernel p hp hp1) 0).toReal =
      p * integerHittingProbability p hp hp1 1 +
      (1 - p) * integerHittingProbability p hp hp1 (-1) := by
  have he : Markov.returnProbability (integerKernel p hp hp1) 0 =
      Markov.action (integerKernel p hp hp1)
        (Markov.hittingProbability (integerKernel p hp hp1) {0}) 0 := by
    unfold Markov.returnProbability Markov.hittingProbability Markov.action
    rw [← Markov.hitting_first_step _ _ _ (Markov.measurableSet_hittingTime_finite {0})]
    congr 1
    ext ω
    exact integer_return_finite_shift ω
  rw [integerKernel_action] at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lt_top_iff_ne_top.mp
      ((Markov.hittingProbability_le_one _ _ _).trans_lt (by simp))))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lt_top_iff_ne_top.mp
      ((Markov.hittingProbability_le_one _ _ _).trans_lt (by simp)))),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal (sub_nonneg.mpr hp1.le)] at hr
  simpa only [zero_add, zero_sub, integerHittingProbability] using hr

theorem integer_positive_return : IntegerHittingSpec.positive_return := by
  intro p hp hp1
  rw [integer_return_first_step,
    integerHittingProbability_positive p hp hp1 1 (by omega),
    integerHittingProbability_negative p hp hp1 (-1) (by omega)]
  simp only [Int.toNat_one, neg_neg, pow_one]
  rcases lt_trichotomy p (1 - p) with h | h | h
  · rw [ite_eq_right (not_lt_of_ge h.le), ite_eq_left h, min_eq_left h.le]
    field_simp
    ring
  · rw [ite_eq_right (by linarith), ite_eq_right (by linarith), min_eq_left h.le]
    linarith
  · rw [ite_eq_left h, ite_eq_right (not_lt_of_ge h.le), min_eq_right h.le]
    field_simp
    ring

open private race_shift from MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.GamblersRuin

/-- First-step equation for an unrestricted race between two distinct targets. -/
theorem integer_race_step (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (a b i : ℤ) (ha : i ≠ a) (hb : i ≠ b) :
    ((integerLaw p hp hp1 i)
      {ω | Markov.hittingTime {a} ω < Markov.hittingTime {b} ω}).toReal =
    p * ((integerLaw p hp hp1 (i + 1))
      {ω | Markov.hittingTime {a} ω < Markov.hittingTime {b} ω}).toReal +
    (1 - p) * ((integerLaw p hp hp1 (i - 1))
      {ω | Markov.hittingTime {a} ω < Markov.hittingTime {b} ω}).toReal := by
  let B : Set (ℕ → ℤ) := {ω | Markov.hittingTime {a} ω < Markov.hittingTime {b} ω}
  have he : integerLaw p hp hp1 i B = Markov.action (integerKernel p hp hp1)
      (fun j => integerLaw p hp hp1 j B) i := by
    simp only [integerLaw, Markov.action]
    rw [← Markov.hitting_first_step _ i B (measurableSet_hittingTime_race _ _)]
    apply measure_congr
    filter_upwards [Markov.coordinate_zero_ae (integerKernel p hp hp1) i] with ω hω
    apply propext
    apply race_shift
    · simpa only [hω, Set.mem_singleton_iff] using ha
    · simpa only [hω, Set.mem_singleton_iff] using hb
  rw [integerKernel_action] at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal (sub_nonneg.mpr hp1.le)] at hr
  exact hr

/-- Uniqueness of the finite boundary recurrence identifies the actual
unrestricted and absorbed exit probabilities. This avoids assuming a coupling. -/
theorem integer_interval_bridge : IntegerHittingSpec.interval_bridge := by
  intro N hN p hp hp1 i
  let u : ℕ → ℝ := fun k => ((integerLaw p hp hp1 (k : ℤ))
    {ω | Markov.hittingTime {(N : ℤ)} ω < Markov.hittingTime {0} ω}).toReal
  have h0 : u 0 = 0 := by
    have he : integerLaw p hp hp1 0
        {ω | Markov.hittingTime {(N : ℤ)} ω < Markov.hittingTime {0} ω} = 0 := by
      rw [← measure_empty (μ := integerLaw p hp hp1 0)]
      apply measure_congr
      filter_upwards [Markov.coordinate_zero_ae (integerKernel p hp hp1) 0] with ω hω
      apply propext
      simp only [Set.mem_empty_iff_false, iff_false, hittingTime_lt_iff_race]
      rintro ⟨n, _, hn⟩
      exact hn 0 (Nat.zero_le n) (by simp [hω])
    simp only [u, Nat.cast_zero, he, ENNReal.toReal_zero]
  have hlast : u N = 1 := by
    have he : integerLaw p hp hp1 (N : ℤ)
        {ω | Markov.hittingTime {(N : ℤ)} ω < Markov.hittingTime {0} ω} = 1 := by
      apply (mem_ae_iff_prob_eq_one (measurableSet_hittingTime_race _ _)).mp
      filter_upwards [Markov.coordinate_zero_ae (integerKernel p hp hp1) (N : ℤ)] with ω hω
      rw [hittingTime_lt_iff_race]
      refine ⟨0, by simp [hω], ?_⟩
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simp only [hω, Set.mem_singleton_iff]
      omega
    simp only [u, he, ENNReal.toReal_one]
  have hs (k : ℕ) (hk : 0 < k) (hkN : k < N) :
      u k = p * u (k + 1) + (1 - p) * u (k - 1) := by
    have he := integer_race_step p hp hp1 N 0 k (by omega) (by omega)
    have hcast : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    simpa only [u, Nat.cast_add, Nat.cast_one, hcast] using he
  change u i.val = _
  rw [ruin_recurrence_solution N hN p hp hp1 u h0 hlast hs i.val (by omega),
    gamblers_ruin N hN p hp hp1 i]

/-- The cumulative-sum realization on the product space of integer moves. -/
private def cumulativePath (i : ℤ) (ξ : ℕ → ℤ) (n : ℕ) : ℤ :=
  i + ∑ k ∈ Finset.range n, ξ k

private theorem cumulativePath_step (i : ℤ) (ξ : ℕ → ℤ) (n : ℕ) :
    cumulativePath i ξ (n + 1) = cumulativePath i ξ n + ξ n := by
  simp only [cumulativePath, Finset.sum_range_succ]
  omega

private theorem measurable_cumulativePath (i : ℤ) : Measurable (cumulativePath i) := by
  apply measurable_pi_iff.mpr
  intro n
  unfold cumulativePath
  fun_prop

private theorem increment_cumulativePath (i : ℤ) (ξ : ℕ → ℤ) (n : ℕ) :
    integerIncrement n (cumulativePath i ξ) = ξ n := by
  simp [integerIncrement, cumulativePath_step]

private theorem cumulativePath_prefix (i : ℤ) (ξ : ℕ → ℤ) (n : ℕ) (x : ℕ → ℤ) :
    cumulativePath i ξ ∈ Markov.prefixCylinder n x ↔
      i = x 0 ∧ ∀ k < n, ξ k = x (k + 1) - x k := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [cumulativePath] using h 0 (Nat.zero_le n)
    · intro k hk
      have h1 := h (k + 1) (by omega)
      have h2 := h k (by omega)
      rw [cumulativePath_step] at h1
      omega
  · rintro ⟨h0, hs⟩ k hk
    induction k with
    | zero => simpa [cumulativePath] using h0
    | succ k ih =>
      have hprev := ih (by omega)
      rw [cumulativePath_step, hprev, hs k (by omega)]
      omega

theorem integerKernel_translation (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i j : ℤ) :
    integerKernel p hp hp1 i j = integerKernel p hp hp1 0 (j - i) := by
  rw [integerKernel_mass, integerKernel_mass]
  have hR : (j - i = 0 + 1) ↔ j = i + 1 := by omega
  have hL : (j - i = 0 - 1) ↔ j = i - 1 := by omega
  simp only [hR, hL]

/-- Equality of whole path laws, proved on every atomic finite prefix. -/
private theorem integerLaw_cumulative (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : ℤ) :
    integerLaw p hp hp1 i =
      (Measure.infinitePi (fun _ : ℕ => (integerKernel p hp hp1 0).toMeasure)).map
        (cumulativePath i) := by
  let μ := Measure.infinitePi (fun _ : ℕ => (integerKernel p hp hp1 0).toMeasure)
  have hm := measurable_cumulativePath i
  have : IsProbabilityMeasure (μ.map (cumulativePath i)) :=
    inferInstance
  symm
  apply Markov.pathLaw_unique (integerKernel p hp hp1) (PMF.pure i)
  intro n x
  rw [Measure.map_apply hm (Markov.measurableSet_prefixCylinder n x)]
  by_cases h0 : i = x 0
  · have he : cumulativePath i ⁻¹' Markov.prefixCylinder n x =
        Set.pi (Finset.range n : Set ℕ) (fun k => {x (k + 1) - x k}) := by
      ext ξ
      simp only [Set.mem_preimage, cumulativePath_prefix, h0, true_and,
        Set.mem_pi, Finset.mem_coe, Finset.mem_range, Set.mem_singleton_iff]
    rw [he]
    change Measure.infinitePi _ _ = _
    rw [Measure.infinitePi_pi _ (fun k _ => measurableSet_singleton _)]
    simp only [PMF.pure_apply, h0, ↓reduceIte, one_mul]
    apply Finset.prod_congr rfl
    intro k _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact (integerKernel_translation p hp hp1 (x k) (x (k + 1))).symm
  · have he : cumulativePath i ⁻¹' Markov.prefixCylinder n x = ∅ := by
      ext ξ
      simp only [Set.mem_preimage, cumulativePath_prefix, h0, false_and, Set.mem_empty_iff_false]
    rw [he, measure_empty]
    simp only [PMF.pure_apply, Ne.symm h0, ↓reduceIte, zero_mul]

theorem measurable_integerIncrement (n : ℕ) : Measurable (integerIncrement n) :=
  (measurable_pi_apply (n + 1)).sub (measurable_pi_apply n)

private theorem integerKernel_zero (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    integerKernel p hp hp1 0 =
      (ruinCoin p hp hp1).map (fun b => if b then (1 : ℤ) else -1) := by
  simp only [integerKernel, zero_add, zero_sub]

theorem integer_increment_law : IntegerHittingSpec.increment_law := by
  intro p hp hp1 i n
  rw [integerLaw_cumulative,
    Measure.map_map (measurable_integerIncrement n) (measurable_cumulativePath i)]
  have he : integerIncrement n ∘ cumulativePath i = fun ξ => ξ n := by
    funext ξ
    exact increment_cumulativePath i ξ n
  rw [he, Measure.infinitePi_map_eval, integerKernel_zero]

theorem integer_increments_independent : IntegerHittingSpec.increments_independent := by
  intro p hp hp1 i
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map measurable_integerIncrement]
  simp_rw [integer_increment_law p hp hp1 i]
  rw [integerLaw_cumulative,
    Measure.map_map (measurable_pi_iff.mpr measurable_integerIncrement) (measurable_cumulativePath i)]
  have he : (fun ω n => integerIncrement n ω) ∘ cumulativePath i = id := by
    funext ξ n
    exact increment_cumulativePath i ξ n
  rw [he, Measure.map_id, integerKernel_zero]

end
end P207.Walk
