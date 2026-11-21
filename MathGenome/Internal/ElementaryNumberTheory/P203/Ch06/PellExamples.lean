import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.PellExamples
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch06.NegativePellSolutions
import Mathlib.Tactic.IntervalCases

namespace P203.Ch06.PellExamples
open P203Specs
open P203Specs.Ch06.PellUnits
open P203Specs.Ch06.FundamentalPellSolution
open P203Specs.Ch06.NegativePellSolutions
open P203Specs.Ch06.PellExamples

private lemma two_nonsquare : ¬IsSquare (2 : ℤ) := by
  rintro ⟨a, ha⟩
  have := Int.emod_nonneg a (by norm_num : (4 : ℤ) ≠ 0)
  have := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 4)
  have hm := congrArg (fun z : ℤ => z % 4) ha
  rw [Int.mul_emod] at hm
  interval_cases h : a % 4 <;> norm_num [h] at hm

private lemma three_nonsquare : ¬IsSquare (3 : ℤ) := by
  rintro ⟨a, ha⟩
  have := Int.emod_nonneg a (by norm_num : (4 : ℤ) ≠ 0)
  have := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 4)
  have hm := congrArg (fun z : ℤ => z % 4) ha
  rw [Int.mul_emod] at hm
  interval_cases h : a % 4 <;> norm_num [h] at hm

private lemma floor_sqrt_two : ⌊Real.sqrt (2 : ℝ)⌋ = 1 := by
  apply Int.floor_eq_iff.mpr
  norm_num

private lemma floor_sqrt_three : ⌊Real.sqrt (3 : ℝ)⌋ = 1 := by
  apply Int.floor_eq_iff.mpr
  norm_num
  exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

private lemma period_two : P203Specs.sqrtPeriod 2 = 1 := by
  have hq : P203Specs.sqrtQ 2 1 = 1 := by
    simpa [floor_sqrt_two] using (P203.sqrt_state_initial 2).2.2.2
  exact Nat.dvd_one.mp (((P203.sqrt_return_points 2 (by norm_num) two_nonsquare).2 1
    (by norm_num)).mp hq)

private lemma three_first_state : P203Specs.sqrtP 3 1 = 1 ∧ P203Specs.sqrtQ 3 1 = 2 := by
  have h := P203.sqrt_state_initial 3
  simpa [floor_sqrt_three] using h.2.2

private lemma three_first_digit : P203Specs.partialQuotient (Real.sqrt 3) 1 = some 1 := by
  have h := (P203.sqrt_state_valid 3 (by norm_num) three_nonsquare 1).2.2
  norm_num [three_first_state.1, three_first_state.2] at h
  rw [P203.algorithm_digits, h, Option.map_some]
  congr 1
  apply Int.floor_eq_iff.mpr
  norm_num
  have hlo : 1 ≤ Real.sqrt (3 : ℝ) :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hhi : Real.sqrt (3 : ℝ) < 2 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  constructor <;> linarith

private lemma period_three : P203Specs.sqrtPeriod 3 = 2 := by
  obtain ⟨a, ha, hp, hq, _⟩ := P203.sqrt_state_step 3 (by norm_num) three_nonsquare 1
  have ha1 : a = 1 := Option.some.inj (ha.symm.trans three_first_digit)
  have hp2 : P203Specs.sqrtP 3 2 = 1 := by
    simpa [ha1, three_first_state.1, three_first_state.2] using hp
  have hq2 : P203Specs.sqrtQ 3 2 = 1 := by
    simpa [hp2, three_first_state.2] using hq
  have hdiv := ((P203.sqrt_return_points 3 (by norm_num) three_nonsquare).2 2 (by norm_num)).mp hq2
  have hn : P203Specs.sqrtPeriod 3 ≠ 1 := by
    intro he
    have hh := ((P203.sqrt_return_points 3 (by norm_num) three_nonsquare).2 1 (by norm_num)).mpr
      (by rw [he])
    rw [three_first_state.2] at hh
    norm_num at hh
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
  have hpos := (P203.sqrt_periodicity 3 (by norm_num) three_nonsquare).1
  omega

theorem sqrt_two_expansion : SqrtTwoExpansion := by
  refine ⟨period_two, ?_, ?_⟩
  · simpa [floor_sqrt_two] using (P203.algorithm_initial (Real.sqrt 2)).2
  · have hfirst : P203Specs.partialQuotient (Real.sqrt 2) 1 = some 2 := by
      simpa [period_two, floor_sqrt_two] using
        (P203.sqrt_period_last 2 (by norm_num) two_nonsquare).2
    intro n
    induction n with
    | zero => exact hfirst
    | succ n ih =>
      have h := (P203.sqrt_periodicity 2 (by norm_num) two_nonsquare).2.2.2.2.2.1 n
      simpa [period_two] using h.trans ih

theorem sqrt_three_expansion : SqrtThreeExpansion := by
  refine ⟨period_three, ?_, ?_⟩
  · simpa [floor_sqrt_three] using (P203.algorithm_initial (Real.sqrt 3)).2
  · have hsecond : P203Specs.partialQuotient (Real.sqrt 3) 2 = some 2 := by
      simpa [period_three, floor_sqrt_three] using
        (P203.sqrt_period_last 3 (by norm_num) three_nonsquare).2
    intro n
    induction n with
    | zero => exact ⟨three_first_digit, hsecond⟩
    | succ n ih =>
      have h := (P203.sqrt_periodicity 3 (by norm_num) three_nonsquare).2.2.2.2.2.1
      constructor
      · simpa [period_three, Nat.mul_succ, Nat.add_assoc] using (h (2 * n)).trans ih.1
      · simpa [period_three, Nat.mul_succ, Nat.add_assoc] using (h (2 * n + 1)).trans ih.2

/-- Transfer the period theorem's least positive pair to minimality among all
integral norm-ε units greater than one. -/
private lemma least_unit_of_pair (D ε x y : ℤ) (hD : 0 < D)
    (hε : ε = 1 ∨ ε = -1) (h : IsLeastPositivePell D ε x y) :
    norm (⟨x, y⟩ : IntegralQuadratic D) = ε ∧
    1 < realValue D (⟨x, y⟩ : IntegralQuadratic D) ∧
    ∀ v : IntegralQuadratic D, norm v = ε → 1 < realValue D v →
      realValue D (⟨x, y⟩ : IntegralQuadratic D) ≤ realValue D v := by
  have hn : norm (⟨x, y⟩ : IntegralQuadratic D) = ε :=
    (P203.Ch06.PellUnits.coefficient_formulas D x y).2.2.trans h.1.2.2
  have hi := (P203.Ch06.PellUnits.unit_criterion D (⟨x, y⟩ : IntegralQuadratic D)).mpr
    (by rw [hn]; exact hε)
  refine ⟨hn, (P203.Ch06.PellUnits.positive_coordinates D hD _ hi).mpr
    ⟨h.1.1, h.1.2.1⟩, ?_⟩
  intro v hv hvpos
  have hvi := (P203.Ch06.PellUnits.unit_criterion D v).mpr (by simpa [hv] using hε)
  have hc := (P203.Ch06.PellUnits.positive_coordinates D hD v hvi).mp hvpos
  apply h.2 v.re v.im
  refine ⟨hc.1, hc.2, ?_⟩
  simpa only [norm, Zsqrtd.norm_def, pow_two, mul_assoc] using hv

private lemma two_minus_least : LeastNegative 2 twoMinus := by
  have h := (P203.pell_fundamental_signs 2 (by norm_num) two_nonsquare).2.2.2
    (by rw [period_two]; decide)
  have hp : IsLeastPositivePell 2 (-1) 1 1 := by
    simpa [pellPeriodNumerator, pellPeriodDenominator, period_two,
      P203Specs.convergentNumerator, P203Specs.convergentDenominator,
      P203Specs.integerContinuants, floor_sqrt_two] using h
  exact least_unit_of_pair 2 (-1) 1 1 (by norm_num) (Or.inr rfl) hp

private lemma two_plus_least : LeastPositive 2 twoPlus := by
  have h := (P203.pell_fundamental_signs 2 (by norm_num) two_nonsquare).2.1
    (by rw [period_two]; decide)
  have hd : P203Specs.partialQuotient (Real.sqrt 2) 1 = some 2 := sqrt_two_expansion.2.2 0
  have hp : IsLeastPositivePell 2 1 3 2 := by
    simpa [pellPeriodNumerator, pellPeriodDenominator, period_two,
      P203Specs.convergentNumerator, P203Specs.convergentDenominator,
      P203Specs.integerContinuants, floor_sqrt_two, hd] using h
  exact least_unit_of_pair 2 1 3 2 (by norm_num) (Or.inl rfl) hp

private lemma three_plus_least : LeastPositive 3 threePlus := by
  have h := (P203.pell_fundamental_signs 3 (by norm_num) three_nonsquare).1
    (by rw [period_three]; decide)
  have hp : IsLeastPositivePell 3 1 2 1 := by
    simpa [pellPeriodNumerator, pellPeriodDenominator, period_three,
      P203Specs.convergentNumerator, P203Specs.convergentDenominator,
      P203Specs.integerContinuants, floor_sqrt_three, three_first_digit] using h
  exact least_unit_of_pair 3 1 2 1 (by norm_num) (Or.inl rfl) hp

theorem two_fundamental_units : TwoFundamentalUnits := by
  refine ⟨two_minus_least, two_plus_least, ?_, ?_, ?_⟩
  · norm_num [twoMinus, realValue]
  · norm_num [twoPlus, realValue]
  · exact P203.Ch06.NegativePellSolutions.fundamental_square 2 (by norm_num)
      two_nonsquare twoMinus twoPlus two_minus_least two_plus_least

theorem three_fundamental_unit : ThreeFundamentalUnit := by
  refine ⟨three_plus_least, ?_, ?_⟩
  · norm_num [threePlus, realValue]
  · rintro ⟨x, y, h⟩
    have := Int.emod_nonneg x (by norm_num : (3 : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 3)
    have hm := congrArg (fun z : ℤ => z % 3) h
    interval_cases hx : x % 3 <;>
      norm_num [pow_two, Int.sub_emod, Int.mul_emod, hx] at hm

private lemma positive_classification (D : ℤ) (hD : 0 < D) (hns : ¬IsSquare D)
    (u : IntegralQuadratic D) (hu : LeastPositive D u) : PositiveClassification D u :=
  ⟨P203.Ch06.FundamentalPellSolution.positive_parametrization D hD hns u hu,
   P203.Ch06.FundamentalPellSolution.positive_powers D hD hns u hu,
   P203.Ch06.FundamentalPellSolution.integer_parametrization D hD hns u hu,
   P203.Ch06.FundamentalPellSolution.integer_powers D hD hns u hu⟩

theorem two_solution_classification : TwoSolutionClassification :=
  ⟨positive_classification 2 (by norm_num) two_nonsquare twoPlus two_plus_least,
   P203.Ch06.NegativePellSolutions.negative_parametrization 2 (by norm_num) two_nonsquare
     twoMinus twoPlus two_minus_least two_plus_least,
   P203.Ch06.NegativePellSolutions.negative_products 2 (by norm_num) two_nonsquare
     twoMinus twoPlus two_minus_least two_plus_least⟩

theorem three_solution_classification : ThreeSolutionClassification :=
  positive_classification 3 (by norm_num) three_nonsquare threePlus three_plus_least

end P203.Ch06.PellExamples
