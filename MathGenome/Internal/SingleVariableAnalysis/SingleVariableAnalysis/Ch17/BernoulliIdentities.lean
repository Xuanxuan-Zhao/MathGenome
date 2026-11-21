import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.BernoulliIdentities
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.Bernoulli

/-! Bernoulli reflection, endpoints, odd numbers, discrete differences and
finite power sums, K03.17.bernoulli. The algebraic identities for Mathlib's
negative-first-number convention are mapped from ℚ[X] to ℝ[X], then
 evaluated at arbitrary real points. The final formula telescopes the
 discrete differences, including the cases p = 0 and N = 0. -/
noncomputable section
namespace SingleVariableAnalysis
open Polynomial
open scoped BigOperators

/-- Rational evaluation commutes with the canonical coefficient map to ℝ. -/
theorem bernoulli_eval_rat (n : ℕ) (q : ℚ) :
    (bernoulliPolynomial n).eval (algebraMap ℚ ℝ q) =
      algebraMap ℚ ℝ ((Polynomial.bernoulli n).eval q) := by
  exact Polynomial.eval_map_apply (algebraMap ℚ ℝ) q

theorem bernoulli_endpoints :
    Specs.SingleVariableAnalysis.Ch17.BernoulliIdentities.bernoulliEndpoints := by
  intro n hn
  have h := _root_.bernoulli_eq_bernoulli'_of_ne_one (show n ≠ 1 by omega)
  have h0 := bernoulli_eval_rat n 0
  have h1 := bernoulli_eval_rat n 1
  simp only [map_zero, Polynomial.bernoulli_eval_zero] at h0
  simp only [map_one, Polynomial.bernoulli_eval_one] at h1
  exact h1.trans ((congrArg (algebraMap ℚ ℝ) h).symm.trans h0.symm)

/-- Polynomial form of reflection; mapping preserves composition. -/
theorem bernoulli_reflection_polynomial (n : ℕ) :
    (bernoulliPolynomial n).comp (1 - X) =
      C ((-1 : ℝ) ^ n) * bernoulliPolynomial n := by
  have h := congrArg (Polynomial.map (algebraMap ℚ ℝ))
    (Polynomial.bernoulli_comp_one_sub_X n)
  simpa [bernoulliPolynomial, BernoulliSpec.bernoulliPolynomialValue,
    Polynomial.map_comp] using h

theorem bernoulli_reflection :
    Specs.SingleVariableAnalysis.Ch17.BernoulliIdentities.bernoulliReflection := by
  intro n x
  have h := congrArg (fun p : Polynomial ℝ => p.eval x)
    (bernoulli_reflection_polynomial n)
  simpa using h

theorem bernoulli_odd_number :
    Specs.SingleVariableAnalysis.Ch17.BernoulliIdentities.bernoulliOddNumber := by
  intro n hn hodd
  have h := bernoulli_reflection n 0
  simp only [sub_zero, hodd.neg_one_pow, neg_one_mul] at h
  rw [bernoulli_endpoints n (by omega)] at h
  change (bernoulliPolynomial n).eval 0 = 0
  linarith

/-- Polynomial form of the shift identity, with no restriction on evaluation. -/
theorem bernoulli_translation_polynomial (n : ℕ) :
    (bernoulliPolynomial n).comp (1 + X) =
      bernoulliPolynomial n + n • (X : Polynomial ℝ) ^ (n - 1) := by
  have h := congrArg (Polynomial.map (algebraMap ℚ ℝ))
    (Polynomial.bernoulli_comp_one_add_X n)
  simpa [bernoulliPolynomial, BernoulliSpec.bernoulliPolynomialValue,
    Polynomial.map_comp] using h

theorem bernoulli_difference :
    Specs.SingleVariableAnalysis.Ch17.BernoulliIdentities.bernoulliDifference := by
  intro n _ x
  have h := congrArg (fun p : Polynomial ℝ => p.eval x)
    (bernoulli_translation_polynomial n)
  simpa [add_comm, sub_eq_iff_eq_add, nsmul_eq_mul] using h

theorem bernoulli_power_sum :
    Specs.SingleVariableAnalysis.Ch17.BernoulliIdentities.bernoulliPowerSum := by
  intro p N
  have htel : ((p : ℝ) + 1) * (∑ k ∈ Finset.range N, (k : ℝ) ^ p) =
      (bernoulliPolynomial (p + 1)).eval (N : ℝ) -
        (bernoulliPolynomial (p + 1)).eval 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hd := bernoulli_difference (p + 1) (by omega) (N : ℝ)
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hd
      push_cast
      linarith
  apply (eq_div_iff (by positivity : (p : ℝ) + 1 ≠ 0)).mpr
  exact (mul_comm _ _).trans htel

end SingleVariableAnalysis
