import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Bernstein
import Mathlib.Tactic.Ring

/-! K03.16.bernstein: finite Bernstein weights and the real/complex
continuous polynomial approximations on [0,1]. The moments are obtained
from the canonical polynomial binomial identities, with no limiting argument.
-/
noncomputable section
open scoped BigOperators unitInterval

namespace SingleVariableAnalysis

def bernsteinWeight (n k : ℕ) (x : ℝ) : ℝ :=
  (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)

def realBernsteinApproximation (n : ℕ) (f : C(I, ℝ)) : C(I, ℝ) :=
  bernsteinApproximation n f

def complexBernsteinApproximation (n : ℕ) (f : C(I, ℂ)) : C(I, ℂ) :=
  bernsteinApproximation n f

theorem bernsteinNode_coordinate (n : ℕ) (k : Fin (n + 1)) :
    (bernstein.z k : ℝ) = (k : ℝ) / n := rfl

theorem bernsteinWeight_eq_polynomial (n k : ℕ) (x : ℝ) :
    bernsteinWeight n k x = (bernsteinPolynomial ℝ n k).eval x := by
  simp [bernsteinWeight, bernsteinPolynomial]

theorem bernsteinWeight_eq_continuous (n k : ℕ) (x : I) :
    bernsteinWeight n k x = bernstein n k x := by
  rw [bernstein_apply]
  rfl

theorem bernsteinWeight_nonneg (n k : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ bernsteinWeight n k x := by
  exact (bernsteinWeight_eq_continuous n k ⟨x, hx⟩).symm ▸ bernstein_nonneg

theorem bernsteinWeight_sum (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (n + 1), bernsteinWeight n k x) = 1 := by
  simpa only [bernsteinWeight_eq_polynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_one] using
    congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)

theorem bernsteinWeight_mean (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n) * bernsteinWeight n k x) = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn)
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum_smul ℝ n)
  simp only [nsmul_eq_mul, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_natCast, Polynomial.eval_X, ← bernsteinWeight_eq_polynomial] at h
  calc
    _ = (∑ k ∈ Finset.range (n + 1), (k : ℝ) * bernsteinWeight n k x) / n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = x := by rw [h]; exact mul_div_cancel_left₀ x hn0

theorem bernsteinWeight_variance (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 2 * bernsteinWeight n k x) =
      x * (1 - x) / n := by
  have h := bernstein.variance (Nat.ne_zero_of_lt hn) (⟨x, hx⟩ : I)
  simpa only [bernstein.z, bernstein_apply, Finset.sum_range,
    bernsteinWeight, sub_sq_comm] using h

theorem bernsteinWeight_endpoints (n k : ℕ) :
    bernsteinWeight n k 0 = (if k = 0 then 1 else 0) ∧
    bernsteinWeight n k 1 = (if k = n then 1 else 0) := by
  rw [bernsteinWeight_eq_polynomial, bernsteinWeight_eq_polynomial]
  exact ⟨bernsteinPolynomial.eval_at_0 ℝ n k, bernsteinPolynomial.eval_at_1 ℝ n k⟩

theorem realBernsteinApproximation_formula (n : ℕ) (_hn : 1 ≤ n)
    (f : C(I, ℝ)) (x : I) :
    realBernsteinApproximation n f x =
      ∑ k : Fin (n + 1), f (bernstein.z k) * bernsteinWeight n k x := by
  simp only [realBernsteinApproximation, bernsteinApproximation.apply,
    ← bernsteinWeight_eq_continuous, smul_eq_mul, mul_comm]

theorem complexBernsteinApproximation_formula (n : ℕ) (_hn : 1 ≤ n)
    (f : C(I, ℂ)) (x : I) :
    complexBernsteinApproximation n f x =
      ∑ k : Fin (n + 1), f (bernstein.z k) * (bernsteinWeight n k x : ℂ) := by
  simp only [complexBernsteinApproximation, bernsteinApproximation.apply,
    ← bernsteinWeight_eq_continuous, Complex.real_smul, mul_comm]

theorem realBernsteinApproximation_canonical (n : ℕ) (f : C(I, ℝ)) :
    realBernsteinApproximation n f = bernsteinApproximation n f := rfl

theorem complexBernsteinApproximation_canonical (n : ℕ) (f : C(I, ℂ)) :
    complexBernsteinApproximation n f = bernsteinApproximation n f := rfl

theorem realBernsteinApproximation_polynomial (n : ℕ) (hn : 1 ≤ n) (f : C(I, ℝ)) :
    ∃ p : Polynomial ℝ, ∀ x : I, realBernsteinApproximation n f x = p.eval (x : ℝ) := by
  refine ⟨∑ k : Fin (n + 1), Polynomial.C (f (bernstein.z k)) *
    bernsteinPolynomial ℝ n k, ?_⟩
  intro x
  rw [realBernsteinApproximation_formula n hn]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    ← bernsteinWeight_eq_polynomial]

theorem complexBernsteinApproximation_polynomial (n : ℕ) (hn : 1 ≤ n) (f : C(I, ℂ)) :
    ∃ p : Polynomial ℂ, ∀ x : I, complexBernsteinApproximation n f x = p.eval ((x : ℝ) : ℂ) := by
  refine ⟨∑ k : Fin (n + 1), Polynomial.C (f (bernstein.z k)) *
    bernsteinPolynomial ℂ n k, ?_⟩
  intro x
  rw [complexBernsteinApproximation_formula n hn]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k _
  simp [bernsteinWeight, bernsteinPolynomial]

theorem realBernsteinApproximation_endpoints (n : ℕ) (hn : 1 ≤ n) (f : C(I, ℝ)) :
    realBernsteinApproximation n f 0 = f 0 ∧ realBernsteinApproximation n f 1 = f 1 := by
  exact ⟨bernsteinApproximation.apply_zero n f,
    bernsteinApproximation.apply_one (Nat.ne_zero_of_lt hn) f⟩

theorem complexBernsteinApproximation_endpoints (n : ℕ) (hn : 1 ≤ n) (f : C(I, ℂ)) :
    complexBernsteinApproximation n f 0 = f 0 ∧ complexBernsteinApproximation n f 1 = f 1 := by
  exact ⟨bernsteinApproximation.apply_zero n f,
    bernsteinApproximation.apply_one (Nat.ne_zero_of_lt hn) f⟩

end SingleVariableAnalysis
