import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.PellSigns
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch06.SquareRootReturnPoints
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.LegendreCriterion
import Mathlib.Tactic.Positivity

namespace P203
open P203Specs

/-- A norm of absolute value one forces the integer coordinates to be reduced. -/
theorem pell_coprime (D ε x y : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hn : x ^ 2 - D * y ^ 2 = ε) : Int.gcd x y = 1 := by
  have hd : (Int.gcd x y : ℤ) ∣ ε := by
    rw [← hn]
    exact dvd_sub (dvd_pow (Int.gcd_dvd_left x y) (by decide))
      (dvd_mul_of_dvd_right (dvd_pow (Int.gcd_dvd_right x y) (by decide)) D)
  have hd1 : (Int.gcd x y : ℤ) ∣ 1 := by
    rcases hε with rfl | rfl
    · exact hd
    · exact dvd_neg.mp hd
  exact Nat.dvd_one.mp (by exact_mod_cast hd1)

/-- The strict Legendre bound, valid for either sign and every positive pair. -/
theorem pell_legendre_bound (D ε x y : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D)
    (hε : ε = 1 ∨ ε = -1) (hx : 0 < x) (hy : 0 < y)
    (hn : x ^ 2 - D * y ^ 2 = ε) :
    |Real.sqrt (D : ℝ) - (x : ℝ) / (y : ℝ)| < 1 / (2 * (y : ℝ) ^ 2) := by
  have hD2 : 2 ≤ D := by
    by_contra! h
    have he : D = 1 := by omega
    exact hns (he ▸ ⟨1, by norm_num⟩)
  have hεlo : -1 ≤ ε := by rcases hε with rfl | rfl <;> norm_num
  have hxy : y ≤ x := by nlinarith [sq_nonneg (y - 1), sq_nonneg (x - y)]
  let s := Real.sqrt (D : ℝ)
  have hs : 1 < s := (sqrt_floor_bounds D hD hns).1
  have hsq : s ^ 2 = (D : ℝ) := Real.sq_sqrt (by exact_mod_cast hD.le)
  have hyr : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hyne : (y : ℝ) ≠ 0 := ne_of_gt hyr
  have ht : (1 : ℝ) ≤ (x : ℝ) / (y : ℝ) :=
    (le_div_iff₀ hyr).mpr (by simpa using (show (y : ℝ) ≤ (x : ℝ) by exact_mod_cast hxy))
  have hsum : 2 < s + (x : ℝ) / (y : ℝ) := by linarith
  have hnorm : (x : ℝ) ^ 2 - (D : ℝ) * (y : ℝ) ^ 2 = (ε : ℝ) := by exact_mod_cast hn
  have hprod : (s - (x : ℝ) / (y : ℝ)) * (s + (x : ℝ) / (y : ℝ)) =
      -(ε : ℝ) / (y : ℝ) ^ 2 := by
    field_simp
    nlinarith [hnorm, hsq]
  have habs : |s - (x : ℝ) / (y : ℝ)| * (s + (x : ℝ) / (y : ℝ)) =
      1 / (y : ℝ) ^ 2 := by
    have ha := congrArg abs hprod
    rw [abs_mul, abs_of_pos (by linarith : 0 < s + (x : ℝ) / (y : ℝ)),
      abs_div] at ha
    rw [abs_of_nonneg (sq_nonneg (y : ℝ))] at ha
    rcases hε with rfl | rfl <;> norm_num at ha ⊢ <;> exact ha
  have ha : 0 < |s - (x : ℝ) / (y : ℝ)| := by
    have hb : 0 < 1 / (y : ℝ) ^ 2 := by positivity
    nlinarith [abs_nonneg (s - (x : ℝ) / (y : ℝ))]
  have hhalf : 1 / (2 * (y : ℝ) ^ 2) = (1 / (y : ℝ) ^ 2) / 2 := by ring
  rw [hhalf]
  nlinarith

/-- Positivity and strict numerator growth, including the first transition. -/
theorem sqrt_numerator_growth (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D) :
    ∀ n : ℕ, 0 < P203Specs.convergentNumerator (Real.sqrt (D : ℝ)) n ∧
      P203Specs.convergentNumerator (Real.sqrt (D : ℝ)) n <
        P203Specs.convergentNumerator (Real.sqrt (D : ℝ)) (n + 1) := by
  let s := Real.sqrt (D : ℝ)
  have hzero : P203Specs.convergentNumerator s 0 = ⌊s⌋ := by
    norm_num [P203Specs.convergentNumerator, P203Specs.integerContinuants]
  intro n
  change 0 < P203Specs.convergentNumerator s (n : ℤ) ∧
    P203Specs.convergentNumerator s (n : ℤ) < P203Specs.convergentNumerator s ((n : ℤ) + 1)
  induction n with
  | zero =>
    obtain ⟨a, ha, _⟩ := sqrt_state_step D hD hns 1
    have hapos := later_partialQuotients s a 1 (by omega) ha
    have hr := (convergent_recurrences s 1 a ha).1
    norm_num only at hr
    rw [(convergent_initial s).2.1, hzero] at hr
    have hp : 0 < ⌊s⌋ := lt_of_lt_of_le (by norm_num) (sqrt_floor_bounds D hD hns).2.1
    norm_num only [Nat.cast_zero, zero_add]
    rw [hzero]
    exact ⟨hp, by nlinarith [mul_le_mul_of_nonneg_right hapos hp.le]⟩
  | succ n ih =>
    obtain ⟨a, ha, _⟩ := sqrt_state_step D hD hns (n + 2)
    have hapos := later_partialQuotients s a (n + 2) (by omega) ha
    have hr := (convergent_recurrences s (n + 2) a ha).1
    rw [show ((n + 2 : ℕ) : ℤ) - 1 = ((n + 1 : ℕ) : ℤ) by omega,
      show ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) by omega] at hr
    push_cast at hr
    have hp : 0 < P203Specs.convergentNumerator s (n + 1) := lt_trans ih.1 ih.2
    exact ⟨hp, by
      change P203Specs.convergentNumerator s (n + 1) < P203Specs.convergentNumerator s (n + 2)
      nlinarith [mul_le_mul_of_nonneg_right hapos hp.le]⟩

/-- Every return pair is positive and has the prescribed parity norm. -/
theorem pell_period_pair (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D)
    (k : ℕ) (hk : 1 ≤ k) :
    PositivePell D ((-1 : ℤ) ^ (k * P203Specs.sqrtPeriod D))
      (pellPeriodNumerator D k) (pellPeriodDenominator D k) := by
  have hl : 0 < P203Specs.sqrtPeriod D := (sqrt_periodicity D hD hns).1
  have hkl : 1 ≤ k * P203Specs.sqrtPeriod D := by nlinarith
  let n := k * P203Specs.sqrtPeriod D - 1
  have hn : n + 1 = k * P203Specs.sqrtPeriod D := Nat.sub_add_cancel hkl
  have hindex : ((k * P203Specs.sqrtPeriod D : ℕ) : ℤ) - 1 = (n : ℤ) := by
    dsimp [n]
    omega
  change PositivePell D _
    (P203Specs.convergentNumerator _ _) (P203Specs.convergentDenominator _ _)
  rw [hindex]
  refine ⟨(sqrt_numerator_growth D hD hns n).1, convergent_denominator_pos _ n, ?_⟩
  rw [sqrt_convergent_norm D hD hns n, hn,
    ((sqrt_return_points D hD hns).2 _ hkl).mpr (dvd_mul_left _ _), mul_one]

theorem pell_classification : PellClassification := by
  intro D hD hns ε hε x y hx hy
  constructor
  · intro hnorm
    have hi : Irrational (Real.sqrt (D : ℝ)) :=
      (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hns
    obtain ⟨n, hxn, hyn⟩ := legendre_criterion _ hi x y hy
      (pell_coprime D ε x y hε hnorm)
      (pell_legendre_bound D ε x y hD hns hε hx hy hnorm)
    have hn := sqrt_convergent_norm D hD hns n
    rw [← hxn, ← hyn, hnorm] at hn
    have hQpos := (sqrt_reduced_states D hD hns (n + 1) (by omega)).1
    have hunit : P203Specs.sqrtQ D (n + 1) = 1 := by
      rcases neg_one_pow_eq_or ℤ (n + 1) with hsign | hsign <;>
        rw [hsign] at hn <;> rcases hε with rfl | rfl <;> nlinarith
    have hdiv := ((sqrt_return_points D hD hns).2 (n + 1) (by omega)).mp hunit
    obtain ⟨k, hk⟩ := hdiv
    have hkpos : 1 ≤ k := by
      by_contra! hz
      have : k = 0 := by omega
      simp [this] at hk
    have hindex : ((k * P203Specs.sqrtPeriod D : ℕ) : ℤ) - 1 = (n : ℤ) := by
      rw [show k * P203Specs.sqrtPeriod D = n + 1 by simpa [Nat.mul_comm] using hk.symm]
      push_cast
      omega
    refine ⟨k, hkpos, ?_, ?_, ?_⟩
    · simpa only [pellPeriodNumerator, hindex] using hxn
    · simpa only [pellPeriodDenominator, hindex] using hyn
    · rw [hunit, mul_one] at hn
      simpa only [hk, Nat.mul_comm] using hn.symm
  · rintro ⟨k, hk, rfl, rfl, hsign⟩
    simpa only [hsign] using (pell_period_pair D hD hns k hk).2.2

/-- Denominators do not decrease, including `q₀ ≤ q₁`. -/
theorem sqrt_denominator_monotone (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D) :
    Monotone (fun n : ℕ => P203Specs.convergentDenominator (Real.sqrt (D : ℝ)) n) := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero =>
    obtain ⟨a, ha, _⟩ := sqrt_state_step D hD hns 1
    have hapos := later_partialQuotients _ a 1 (by omega) ha
    norm_num only [Nat.cast_zero, zero_add, Nat.cast_one]
    simpa only [(convergent_denominator_growth).1,
      (convergent_denominator_growth).2.1 _ a ha] using hapos
  | succ n =>
    have hd : P203Specs.partialQuotient (Real.sqrt (D : ℝ)) (n + 1 + 1) ≠ none := by
      obtain ⟨a, ha, _⟩ := sqrt_state_step D hD hns (n + 1 + 1)
      rw [ha]
      simp
    exact ((convergent_denominator_growth).2.2 _ (n + 1) (by omega) hd).le

/-- The source ordering grows strictly along all square-root convergents. -/
theorem sqrt_convergent_value_strictMono (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D) :
    StrictMono (fun n : ℕ => pellValue D
      (P203Specs.convergentNumerator (Real.sqrt (D : ℝ)) n)
      (P203Specs.convergentDenominator (Real.sqrt (D : ℝ)) n)) := by
  have hp : StrictMono (fun n : ℕ => P203Specs.convergentNumerator (Real.sqrt (D : ℝ)) n) :=
    strictMono_nat_of_lt_succ (fun n => (sqrt_numerator_growth D hD hns n).2)
  have hq := sqrt_denominator_monotone D hD hns
  intro i j hij
  exact add_lt_add_of_lt_of_le (by exact_mod_cast hp hij)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hq hij.le) (Real.sqrt_nonneg _))

theorem pell_ordering : PellOrdering := by
  intro D hD hns j k hj hk
  have hl : 0 < P203Specs.sqrtPeriod D := (sqrt_periodicity D hD hns).1
  have hjl : 1 ≤ j * P203Specs.sqrtPeriod D := by nlinarith
  have hkl : 1 ≤ k * P203Specs.sqrtPeriod D := by nlinarith
  have hji : ((j * P203Specs.sqrtPeriod D : ℕ) : ℤ) - 1 =
      ((j * P203Specs.sqrtPeriod D - 1 : ℕ) : ℤ) := by omega
  have hki : ((k * P203Specs.sqrtPeriod D : ℕ) : ℤ) - 1 =
      ((k * P203Specs.sqrtPeriod D - 1 : ℕ) : ℤ) := by omega
  simp only [pellPeriodNumerator, pellPeriodDenominator, hji, hki]
  rw [(sqrt_convergent_value_strictMono D hD hns).lt_iff_lt]
  have hm : j * P203Specs.sqrtPeriod D < k * P203Specs.sqrtPeriod D ↔ j < k :=
    Nat.mul_lt_mul_right hl
  omega

/-- Characterization of minimality by the least admissible return multiplier. -/
theorem pell_least_index : PellLeastIndex := by
  intro D hD hns ε hε k hk hsign
  have hpair : PositivePell D ε (pellPeriodNumerator D k) (pellPeriodDenominator D k) := by
    simpa only [hsign] using pell_period_pair D hD hns k hk
  constructor
  · intro hleast j hj hjsign
    by_contra! hkj
    have hjpair : PositivePell D ε (pellPeriodNumerator D j) (pellPeriodDenominator D j) := by
      simpa only [hjsign] using pell_period_pair D hD hns j hj
    have hlt := (pell_ordering D hD hns j k hj hk).mpr hkj
    exact (not_lt_of_ge (hleast.2 _ _ hjpair)) hlt
  · intro hmin
    refine ⟨hpair, ?_⟩
    intro x y hxy
    obtain ⟨j, hj, rfl, rfl, hjsign⟩ :=
      (pell_classification D hD hns ε hε x y hxy.1 hxy.2.1).mp hxy.2.2
    have hkj := hmin j hj hjsign
    rcases hkj.eq_or_lt with he | he
    · rw [he]
    · exact ((pell_ordering D hD hns k j hk hj).mpr he).le

/-- Parity determines the first allowed multiplier for both signs. -/
theorem pell_fundamental_signs : PellFundamentalSigns := by
  intro D hD hns
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heven
    have hsign : (-1 : ℤ) ^ (1 * P203Specs.sqrtPeriod D) = 1 := by
      simpa only [one_mul] using heven.neg_one_pow (α := ℤ)
    exact (pell_least_index D hD hns 1 (Or.inl rfl) 1 (by omega) hsign).mpr
      (fun j hj _ => hj)
  · intro hodd
    have hsign : (-1 : ℤ) ^ (2 * P203Specs.sqrtPeriod D) = 1 := by
      rw [pow_mul]
      norm_num
    apply (pell_least_index D hD hns 1 (Or.inl rfl) 2 (by omega) hsign).mpr
    intro j hj hjsgn
    have hjeven : Even j := by
      have hm := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℤ) ≠ 1)).mp hjsgn
      exact (Nat.even_mul.mp hm).resolve_right (Nat.not_even_iff_odd.mpr hodd)
    exact Nat.one_lt_of_ne_zero_of_even (by omega) hjeven
  · constructor
    · rintro ⟨x, y, hxy⟩
      obtain ⟨k, _, _, _, hsgn⟩ :=
        (pell_classification D hD hns (-1) (Or.inr rfl) x y hxy.1 hxy.2.1).mp hxy.2.2
      exact ((Nat.odd_mul).mp
        ((neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℤ) ≠ 1)).mp hsgn)).2
    · intro hodd
      have hsign : (-1 : ℤ) ^ (1 * P203Specs.sqrtPeriod D) = -1 := by
        simpa only [one_mul] using hodd.neg_one_pow (α := ℤ)
      exact ⟨_, _, by simpa only [hsign] using pell_period_pair D hD hns 1 (by omega)⟩
  · intro hodd
    have hsign : (-1 : ℤ) ^ (1 * P203Specs.sqrtPeriod D) = -1 := by
      simpa only [one_mul] using hodd.neg_one_pow (α := ℤ)
    exact (pell_least_index D hD hns (-1) (Or.inr rfl) 1 (by omega) hsign).mpr
      (fun j hj _ => hj)

end P203
