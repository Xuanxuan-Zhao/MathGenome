import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Higher
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.TaylorPolynomial
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear

/-!
# Finite Taylor interpolation

K03.06.taylor_polynomial (paper.tex:2759–2770). The coefficients belong to
ℝ or ℂ (the proofs work over RCLike); the input and every analytic derivative
are real. We use ordinary scalar polynomials, evaluated along the real axis.

The proof follows the manuscript's finite coefficient argument. Mathlib's
algebraic Taylor shift and `factorial_smul_hasseDeriv` identify each shifted
coefficient with the corresponding iterated derivative divided by k!. The
analytic-to-algebraic derivative bridge is proved below by real scalar
restriction and induction, so complex differentiation is not substituted for
the required real-variable derivative.

The interpolation identities hold for any prescribed finite list of derivative
values. Their algebraic validity does not assert differentiability of an arbitrary
input function. `taylorPolynomial_existsUnique` retains the upstream predicate
for existence of the derivatives through order n at a. No regularity of the
highest derivative away from a, continuity of that derivative, or convergence of
an infinite series is used. The n=0 case is included.
-/

noncomputable section
namespace SingleVariableAnalysis
open Polynomial
open scoped BigOperators
universe u
variable {K : Type u} [RCLike K]

/-- Evaluate a scalar polynomial at a real argument. -/
def RealPolynomialEval (p : Polynomial K) (x : ℝ) : K :=
  p.eval (algebraMap ℝ K x)

/-- The finite Taylor polynomial, in powers of X-a. -/
def TaylorPolynomial (f : ℝ → K) (n : ℕ) (a : ℝ) : Polynomial K :=
  ∑ k ∈ Finset.range (n+1), C (RealIteratedDerivative k f a / (k.factorial : K)) *
    (X - C (algebraMap ℝ K a)) ^ k

def TaylorPolynomialEval (f : ℝ → K) (n : ℕ) (a x : ℝ) : K :=
  RealPolynomialEval (TaylorPolynomial f n a) x

def TaylorRemainder (f : ℝ → K) (n : ℕ) (a x : ℝ) : K :=
  f x - TaylorPolynomialEval f n a x

theorem realPolynomial_hasDerivAt (p : Polynomial K) (x : ℝ) :
    HasDerivAt (RealPolynomialEval p) (RealPolynomialEval p.derivative x) x := by
  simpa [RealPolynomialEval] using! (p.hasDerivAt (algebraMap ℝ K x)).scomp x
    (RCLike.ofRealCLM : ℝ →L[ℝ] K).hasDerivAt

theorem realPolynomial_iteratedDerivative (p : Polynomial K) (k : ℕ) :
    RealIteratedDerivative k (RealPolynomialEval p) =
      RealPolynomialEval (derivative^[k] p) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [realIteratedDerivative_succ, ih, Function.iterate_succ_apply']
    exact funext fun x => (realPolynomial_hasDerivAt _ x).deriv

/-- The coefficient calculation behind finite Hermite interpolation at one point. -/
theorem realPolynomial_jet_coefficient (p : Polynomial K) (a : ℝ) (k : ℕ) :
    RealIteratedDerivative k (RealPolynomialEval p) a =
      (k.factorial : K) * (taylor (algebraMap ℝ K a) p).coeff k := by
  rw [realPolynomial_iteratedDerivative, RealPolynomialEval, Polynomial.taylor_coeff,
    ← Polynomial.factorial_smul_hasseDeriv]
  simp [nsmul_eq_mul]

theorem taylorPolynomial_shifted_coeff (f : ℝ → K) (n : ℕ) (a : ℝ) (k : ℕ) :
    (taylor (algebraMap ℝ K a) (TaylorPolynomial f n a)).coeff k =
      if k ≤ n then RealIteratedDerivative k f a / (k.factorial : K) else 0 := by
  simp [TaylorPolynomial, map_sum, taylor_apply, sub_comp, mul_comp, pow_comp,
    Finset.mem_range]

theorem taylorPolynomial_natDegree_le (f : ℝ → K) (n : ℕ) (a : ℝ) :
    (TaylorPolynomial f n a).natDegree ≤ n := by
  rw [← natDegree_taylor (TaylorPolynomial f n a) (algebraMap ℝ K a)]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [taylorPolynomial_shifted_coeff, not_le.mpr hk]

theorem taylorPolynomial_degree_le (f : ℝ → K) (n : ℕ) (a : ℝ) :
    (TaylorPolynomial f n a).degree ≤ (n : WithBot ℕ) := by
  exact Polynomial.degree_le_of_natDegree_le (taylorPolynomial_natDegree_le f n a)

theorem taylorPolynomialEval_formula (f : ℝ → K) (n : ℕ) (a x : ℝ) :
    TaylorPolynomialEval f n a x =
      ∑ k ∈ Finset.range (n+1),
        (RealIteratedDerivative k f a / (k.factorial : K)) *
          (algebraMap ℝ K (x-a)) ^ k := by
  simp [TaylorPolynomialEval, RealPolynomialEval, TaylorPolynomial, Polynomial.eval_finsetSum, map_sub]

theorem taylorRemainder_eq (f : ℝ → K) (n : ℕ) (a x : ℝ) :
    TaylorRemainder f n a x = f x - TaylorPolynomialEval f n a x := rfl

@[simp] theorem taylorPolynomial_zero (f : ℝ → K) (a : ℝ) :
    TaylorPolynomial f 0 a = C (f a) := by
  simp [TaylorPolynomial]

@[simp] theorem taylorPolynomialEval_zero (f : ℝ → K) (a x : ℝ) :
    TaylorPolynomialEval f 0 a x = f a := by
  simp [TaylorPolynomialEval, RealPolynomialEval]

@[simp] theorem taylorRemainder_zero (f : ℝ → K) (a x : ℝ) :
    TaylorRemainder f 0 a x = f x - f a := by
  simp [TaylorRemainder]

theorem taylorPolynomial_derivatives_match (f : ℝ → K) (n : ℕ) (a : ℝ)
    (k : ℕ) (hk : k ≤ n) :
    RealIteratedDerivative k (TaylorPolynomialEval f n a) a =
      RealIteratedDerivative k f a := by
  change RealIteratedDerivative k (RealPolynomialEval (TaylorPolynomial f n a)) a = _
  rw [realPolynomial_jet_coefficient, taylorPolynomial_shifted_coeff, ite_eq_left hk]
  exact mul_div_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero k)

@[simp] theorem taylorPolynomialEval_self (f : ℝ → K) (n : ℕ) (a : ℝ) :
    TaylorPolynomialEval f n a a = f a := by
  simpa using taylorPolynomial_derivatives_match f n a 0 (Nat.zero_le n)

theorem taylorPolynomial_unique (f : ℝ → K) (n : ℕ) (a : ℝ) (p : Polynomial K)
    (hp : p.natDegree ≤ n)
    (hm : ∀ k ≤ n, RealIteratedDerivative k (RealPolynomialEval p) a =
      RealIteratedDerivative k f a) : p = TaylorPolynomial f n a := by
  apply taylor_injective (algebraMap ℝ K a)
  ext k
  rw [taylorPolynomial_shifted_coeff]
  by_cases hk : k ≤ n
  · rw [ite_eq_left hk, ← hm k hk, realPolynomial_jet_coefficient]
    exact (mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero k)).symm
  · rw [ite_eq_right hk]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_taylor]
    exact lt_of_le_of_lt hp (Nat.lt_of_not_ge hk)

/-- Existence and uniqueness under precisely pointwise existence through n;
continuity of the highest derivative is not needed for finite interpolation. -/
theorem taylorPolynomial_existsUnique (f : ℝ → K) (n : ℕ) (a : ℝ)
    (_hf : KTimesDifferentiableOn n f {a}) :
    ∃! p : Polynomial K, p.degree ≤ (n : WithBot ℕ) ∧
      ∀ k ≤ n, RealIteratedDerivative k (RealPolynomialEval p) a =
        RealIteratedDerivative k f a := by
  refine ⟨TaylorPolynomial f n a, ⟨taylorPolynomial_degree_le f n a, ?_⟩, ?_⟩
  · exact taylorPolynomial_derivatives_match f n a
  · intro p hp
    exact taylorPolynomial_unique f n a p (Polynomial.natDegree_le_of_degree_le hp.1) hp.2

end SingleVariableAnalysis
