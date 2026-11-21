import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.PellConvergentNorm
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.QuadraticSurdRecurrence
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.Convergents
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace P203

noncomputable abbrev sqrtState : P203Specs.SqrtStateType := P203Specs.sqrtState
noncomputable abbrev sqrtP : P203Specs.SqrtParameterType := P203Specs.sqrtP
noncomputable abbrev sqrtQ : P203Specs.SqrtParameterType := P203Specs.sqrtQ

open P203Specs

theorem sqrtP_succ (D : ℤ) (j : ℕ) :
    sqrtP D (j + 1) = surdNextP (sqrtP D j) (sqrtQ D j) D := rfl

theorem sqrtQ_succ (D : ℤ) (j : ℕ) :
    sqrtQ D (j + 1) = surdNextQ (sqrtP D j) (sqrtQ D j) D := rfl

theorem sqrt_state_initial : SqrtStateInitial := by
  intro D
  norm_num [P203Specs.sqrtP, P203Specs.sqrtQ, P203Specs.sqrtState,
    P203Specs.surdNextP, P203Specs.surdNextQ]

theorem sqrt_state_valid : SqrtStateValid := by
  intro D hD hns j
  have hx : Irrational (Real.sqrt (D : ℝ)) :=
    (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hns
  induction j with
  | zero =>
    simpa [P203Specs.sqrtP, P203Specs.sqrtQ, P203Specs.sqrtState] using
      (show (1 : ℤ) ≠ 0 ∧ (1 : ℤ) ∣ D - 0 ^ 2 ∧
        completeQuotient (Real.sqrt (D : ℝ)) 0 = some (Real.sqrt (D : ℝ)) from
        ⟨one_ne_zero, one_dvd _, (algorithm_initial _).1⟩)
  | succ j ih =>
    obtain ⟨hQ, hdiv, hquot⟩ := ih
    obtain ⟨hne, hprod, hdiv', hstep⟩ := surd_recurrence _ _ D hD hns hQ hdiv
    refine ⟨hne, hdiv', ?_⟩
    obtain ⟨β, hβ⟩ := irrational_completeQuotient_defined _ hx (j + 1)
    let α : ℝ := ((sqrtP D j : ℝ) + Real.sqrt (D : ℝ)) / (sqrtQ D j : ℝ)
    have hnot : α ≠ (⌊α⌋ : ℝ) := by
      intro he
      have hn := (algorithm_stopping _ α j hquot).mpr he
      rw [hβ] at hn
      cases hn
    rw [algorithm_step, hquot, Option.bind_some, ite_eq_right hnot]
    exact congrArg some hstep

theorem sqrt_state_step : SqrtStateStep := by
  intro D hD hns j
  obtain ⟨hQ, hdiv, hquot⟩ := sqrt_state_valid D hD hns j
  let α : ℝ := ((sqrtP D j : ℝ) + Real.sqrt (D : ℝ)) / (sqrtQ D j : ℝ)
  refine ⟨⌊α⌋, ?_, rfl, rfl, ?_⟩
  · rw [algorithm_digits, hquot]
    rfl
  · exact (surd_recurrence _ _ D hD hns hQ hdiv).2.1

/-- Coefficients in the rational basis `1,x` are unique when `x` is irrational.
This is used only with integer coefficients, after clearing denominators. -/
theorem irrational_integer_coefficients {x : ℝ} (hx : Irrational x) (A B : ℤ)
    (h : (A : ℝ) + (B : ℝ) * x = 0) : A = 0 ∧ B = 0 := by
  have hB : B = 0 := by
    by_contra hB
    apply (irrational_iff_ne_rational x).mp hx (-A) B hB
    apply (eq_div_iff (by exact_mod_cast hB : (B : ℝ) ≠ 0)).mpr
    push_cast
    linarith
  refine ⟨?_, hB⟩
  rw [hB] at h
  exact_mod_cast (show (A : ℝ) = 0 by simpa using h)

/-- Clear the two denominators in the convergent tail formula and compare
coefficients of the irrational square root. -/
theorem surd_tail_coefficients {x : ℝ} (hx : Irrational x)
    (D P Q p q pp qp : ℤ) (hsq : x ^ 2 = (D : ℝ)) (hQ : Q ≠ 0)
    (hden : (q : ℝ) * (((P : ℝ) + x) / (Q : ℝ)) + (qp : ℝ) ≠ 0)
    (htail : x = ((p : ℝ) * (((P : ℝ) + x) / (Q : ℝ)) + (pp : ℝ)) /
      ((q : ℝ) * (((P : ℝ) + x) / (Q : ℝ)) + (qp : ℝ))) :
    q * D = p * P + pp * Q ∧ q * P + qp * Q = p := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  have hcross := (eq_div_iff hden).mp htail
  field_simp [hQr] at hcross
  have hcoeff : ((q * D - p * P - pp * Q : ℤ) : ℝ) +
      ((q * P + qp * Q - p : ℤ) : ℝ) * x = 0 := by
    push_cast
    linear_combination hcross - (q : ℝ) * hsq
  obtain ⟨hconstant, hlinear⟩ := irrational_integer_coefficients hx _ _ hcoeff
  constructor <;> omega

/-- The exact norm comes from the tail identity and the adjacent-convergent
determinant, without any periodicity or return assumption. -/
theorem sqrt_convergent_norm : SqrtConvergentNorm := by
  intro D hD hns n
  let x := Real.sqrt (D : ℝ)
  let p := P203Specs.convergentNumerator x n
  let q := P203Specs.convergentDenominator x n
  let pp := P203Specs.convergentNumerator x ((n : ℤ) - 1)
  let qp := P203Specs.convergentDenominator x ((n : ℤ) - 1)
  let P := sqrtP D (n + 1)
  let Q := sqrtQ D (n + 1)
  have hx : Irrational x := (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hns
  have hsq : x ^ 2 = (D : ℝ) := Real.sq_sqrt (by exact_mod_cast hD.le)
  obtain ⟨hQ, _, hquot⟩ := sqrt_state_valid D hD hns (n + 1)
  obtain ⟨α, hα, _, hden, htail, _⟩ := convergent_exact_tail x hx n
  have hαval : α = ((P : ℝ) + x) / (Q : ℝ) :=
    Option.some.inj (hα.symm.trans hquot)
  rw [hαval] at hden htail
  obtain ⟨hconstant, hlinear⟩ :=
    surd_tail_coefficients hx D P Q p q pp qp hsq hQ hden htail
  have hdefined : P203Specs.partialQuotient x n ≠ none := by
    rw [algorithm_digits, (sqrt_state_valid D hD hns n).2.2]
    simp
  have hdet : p * qp - pp * q = (-1 : ℤ) ^ (n + 1) :=
    convergent_determinant x n hdefined
  change p ^ 2 - D * q ^ 2 = (-1 : ℤ) ^ (n + 1) * Q
  calc
    p ^ 2 - D * q ^ 2 = Q * (p * qp - pp * q) := by
      linear_combination -p * hlinear - q * hconstant
    _ = (-1 : ℤ) ^ (n + 1) * Q := by rw [hdet, mul_comm]

theorem sqrt_convergent_denominators : SqrtConvergentDenominators := by
  intro D hD hns n
  let x := Real.sqrt (D : ℝ)
  let p := P203Specs.convergentNumerator x n
  let q := P203Specs.convergentDenominator x n
  have hx : Irrational x := (irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hns
  have hdefined : P203Specs.partialQuotient x n ≠ none := by
    rw [algorithm_digits, (sqrt_state_valid D hD hns n).2.2]
    simp
  have hq : q ≠ 0 := ne_of_gt (convergent_reduced x n hdefined).1
  constructor
  · intro hz
    have hc : ((-p : ℤ) : ℝ) + (q : ℝ) * x = 0 := by
      push_cast
      linarith
    exact hq (irrational_integer_coefficients hx (-p) q hc).2
  · have hnorm : p ^ 2 - D * q ^ 2 = (-1 : ℤ) ^ (n + 1) * sqrtQ D (n + 1) :=
      sqrt_convergent_norm D hD hns n
    have hnonzero : (-1 : ℤ) ^ (n + 1) * sqrtQ D (n + 1) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by decide)) (sqrt_state_valid D hD hns (n + 1)).1
    intro hz
    apply hnonzero
    rw [← hnorm]
    linarith

end P203
