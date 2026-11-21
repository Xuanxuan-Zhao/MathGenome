import MathGenome.Internal.Specs.D05.Foundations.DifferentiationTaylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

/-! Formal differentiation and finite Taylor expansion (paper.tex:385–389).
The proof first works with coefficients in K[x][h]. Hasse derivatives give the
expansion without division in any characteristic; ordinary iterated derivatives
replace them only after the nonzero factorials are inverted in characteristic zero.
-/

noncomputable section

namespace D05.Foundations.DifferentiationTaylor

open Polynomial

variable {K : Type*} [Field K]

/-- The coefficient of h^j in f(x+h), as a polynomial in x. -/
theorem shiftCoefficient (f : Polynomial K) (j : ℕ) :
    (taylor (X : Polynomial K) (f.map C)).coeff j = hasseDeriv j f := by
  simp [taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X]

/-- Binomial expansion in coefficient form, valid in every characteristic. -/
theorem hasseExpansion (f : Polynomial K) :
    (f.map C).comp (C X + X) =
      ∑ j ∈ Finset.range (f.natDegree + 1), C (hasseDeriv j f) * X ^ j := by
  have h := (taylor (X : Polynomial K) (f.map C)).as_sum_range
  rw [natDegree_taylor, natDegree_map_eq_of_injective C_injective] at h
  simp only [shiftCoefficient] at h
  simpa only [C_mul_X_pow_eq_monomial, taylor_apply, add_comm] using h

/-- The normalization uses characteristic zero exactly to invert j!. -/
theorem hasseDerivativeNormalization [CharZero K] (f : Polynomial K) (j : ℕ) :
    hasseDeriv j f = (j.factorial : K)⁻¹ • (derivative^[j] f) := by
  have h := congrFun (factorial_smul_hasseDeriv (R := K) j) f
  simp only [LinearMap.smul_apply] at h
  rw [← h, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)), one_smul]

theorem productRule : D05.Specs.DifferentiationTaylor.productRule := by
  intro K _ f g
  exact Polynomial.derivative_mul

theorem quadraticRemainder : D05.Specs.DifferentiationTaylor.quadraticRemainder := by
  intro K _ f
  have hd : X ^ 2 ∣ (f.map C).comp (C X + X) - C f - X * C f.derivative := by
    rw [X_pow_dvd_iff]
    intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    all_goals
      have h : (f.map C).comp (C X + X) = taylor (X : Polynomial K) (f.map C) := by
        rw [taylor_apply, add_comm]
      rw [h]
      simp [taylor_coeff, eval_map, eval₂_C_X, derivative_map]
  obtain ⟨R, hR⟩ := hd
  exact ⟨R, by linear_combination hR⟩

theorem finiteTaylor : D05.Specs.DifferentiationTaylor.finiteTaylor := by
  intro K _ _ f _hf
  simpa only [hasseDerivativeNormalization] using hasseExpansion f

theorem zeroTaylor : D05.Specs.DifferentiationTaylor.zeroTaylor := by
  intro K _
  have hz (j : ℕ) : (derivative^[j]) (0 : Polynomial K) = 0 := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, derivative_zero]
  exact ⟨hz, by simp, by simp [hz]⟩

section Substitution

variable {A : Type*} [Ring A] [Algebra K A] {x h : A}

/-- A polynomial in x commutes with every element commuting with x. -/
theorem polynomialEval_commute (f : Polynomial K) (hc : Commute x h) :
    Commute (aeval x f) h := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add_left hq
  | monomial j a =>
    simpa only [aeval_monomial] using
      (Algebra.commute_algebraMap_left a h).mul_left (hc.pow_left j)

/-- Evaluate the inner variable at x and the outer variable at h. -/
def evaluatePair (x h : A) (hc : Commute x h) : Polynomial (Polynomial K) →ₐ[K] A :=
  eval₂AlgHom (aeval x) h (fun f => polynomialEval_commute f hc)

theorem evaluatePair_apply (hc : Commute x h) (P : Polynomial (Polynomial K)) :
    evaluatePair x h hc P = P.eval₂ (aeval x).toRingHom h := rfl

@[simp] theorem evaluatePair_C (hc : Commute x h) (p : Polynomial K) :
    evaluatePair x h hc (C p) = aeval x p := by
  simp [evaluatePair]

@[simp] theorem evaluatePair_X (hc : Commute x h) :
    evaluatePair (K := K) x h hc X = h := by
  simp [evaluatePair]

/-- Substitution in the coefficient identity is ordinary evaluation at x+h. -/
theorem evaluatePair_shift (hc : Commute x h) (f : Polynomial K) :
    evaluatePair x h hc ((f.map C).comp (C X + X)) = aeval (x + h) f := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, add_comp, map_add, hp, hq]
  | monomial j a =>
    simp only [map_monomial, monomial_comp, map_mul, map_pow, map_add,
      evaluatePair_C, evaluatePair_X, aeval_X, aeval_C, aeval_monomial]

end Substitution

theorem commutingSubstitution : D05.Specs.DifferentiationTaylor.commutingSubstitution := by
  intro K A _ _ _ x h hc
  exact ⟨evaluatePair x h hc, fun _ => rfl, evaluatePair_C hc,
    evaluatePair_X hc, evaluatePair_shift hc⟩

theorem evaluatedProductRule : D05.Specs.DifferentiationTaylor.evaluatedProductRule := by
  intro K A _ _ _ f g x
  rw [productRule K f g]
  simp only [map_add, map_mul]

theorem evaluatedQuadraticRemainder :
    D05.Specs.DifferentiationTaylor.evaluatedQuadraticRemainder := by
  intro K _ f
  obtain ⟨R, hR⟩ := quadraticRemainder K f
  refine ⟨R, hR, ?_⟩
  intro A _ _ x h hc
  have he := congrArg (evaluatePair x h hc) hR
  simp only [evaluatePair_shift, map_add, map_mul, map_pow,
    evaluatePair_C, evaluatePair_X] at he
  rw [evaluatePair_apply] at he
  exact he

theorem evaluatedFiniteTaylor : D05.Specs.DifferentiationTaylor.evaluatedFiniteTaylor := by
  intro K A _ _ _ _ f x h hc
  have hpoly : (f.map C).comp (C X + X) =
      ∑ j ∈ Finset.range (f.natDegree + 1),
        C ((j.factorial : K)⁻¹ • ((derivative^[j]) f)) * X ^ j := by
    simpa only [hasseDerivativeNormalization] using hasseExpansion f
  have he := congrArg (evaluatePair x h hc) hpoly
  simpa only [evaluatePair_shift, map_sum, map_mul, map_pow,
    evaluatePair_C, evaluatePair_X, map_smul] using he

end D05.Foundations.DifferentiationTaylor
