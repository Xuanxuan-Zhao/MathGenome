import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Higher
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.RCLike.Basic

/-! Independent specification of K03.06.taylor_polynomial, paper.tex:2759–2770.
The indeterminate is evaluated only at real inputs, also for complex coefficients.
The finite sum interpolates the supplied derivative values algebraically. The
existence/uniqueness statement explicitly retains existence through order n;
no continuity of the nth derivative or infinite-series claim is imposed.
`natDegree ≤ n` includes the zero polynomial and is equivalent to `degree ≤ n`
for natural n. RCLike generality includes both canonical scalar fields ℝ and ℂ.
-/
namespace Specs.SingleVariableAnalysis.Ch06.TaylorPolynomial
open Polynomial
open scoped BigOperators
universe u

variable {K : Type u} [RCLike K]

def realPolynomialEvalType : Type (u+1) :=
  ∀ {K : Type u} [RCLike K], Polynomial K → ℝ → K
noncomputable def realPolynomialEvalValue (p : Polynomial K) (x : ℝ) : K :=
  p.eval (algebraMap ℝ K x)

def taylorPolynomialType : Type (u+1) :=
  ∀ {K : Type u} [RCLike K], (ℝ → K) → ℕ → ℝ → Polynomial K
noncomputable def taylorPolynomialValue (f : ℝ → K) (n : ℕ) (a : ℝ) : Polynomial K :=
  ∑ k ∈ Finset.range (n+1),
    C (Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k f a / (k.factorial : K)) *
      (X - C (algebraMap ℝ K a)) ^ k

def taylorPolynomialEvalType : Type (u+1) :=
  ∀ {K : Type u} [RCLike K], (ℝ → K) → ℕ → ℝ → ℝ → K
noncomputable def taylorPolynomialEvalValue (f : ℝ → K) (n : ℕ) (a x : ℝ) : K :=
  realPolynomialEvalValue (taylorPolynomialValue f n a) x

def taylorRemainderType : Type (u+1) :=
  ∀ {K : Type u} [RCLike K], (ℝ → K) → ℕ → ℝ → ℝ → K
noncomputable def taylorRemainderValue (f : ℝ → K) (n : ℕ) (a x : ℝ) : K :=
  f x - taylorPolynomialEvalValue f n a x

def realPolynomial_hasDerivAt : Prop :=
  ∀ {K : Type u} [RCLike K] (p : Polynomial K) (x : ℝ),
    HasDerivAt (realPolynomialEvalValue p) (realPolynomialEvalValue p.derivative x) x

def realPolynomial_iteratedDerivative : Prop :=
  ∀ {K : Type u} [RCLike K] (p : Polynomial K) (k : ℕ),
    Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k (realPolynomialEvalValue p) =
      realPolynomialEvalValue (derivative^[k] p)

def realPolynomial_jet_coefficient : Prop :=
  ∀ {K : Type u} [RCLike K] (p : Polynomial K) (a : ℝ) (k : ℕ),
    Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k (realPolynomialEvalValue p) a =
      (k.factorial : K) * (taylor (algebraMap ℝ K a) p).coeff k

def taylorPolynomial_shifted_coeff : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ) (k : ℕ),
    (taylor (algebraMap ℝ K a) (taylorPolynomialValue f n a)).coeff k =
      if k ≤ n then Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k f a / (k.factorial : K) else 0

def taylorPolynomial_natDegree_le : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ),
    (taylorPolynomialValue f n a).natDegree ≤ n

def taylorPolynomial_degree_le : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ),
    (taylorPolynomialValue f n a).degree ≤ (n : WithBot ℕ)

def taylorPolynomialEval_formula : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a x : ℝ),
    taylorPolynomialEvalValue f n a x =
      ∑ k ∈ Finset.range (n+1),
        (Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k f a / (k.factorial : K)) *
          (algebraMap ℝ K (x-a)) ^ k

def taylorRemainder_eq : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a x : ℝ),
    taylorRemainderValue f n a x = f x - taylorPolynomialEvalValue f n a x

def taylorPolynomial_zero : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (a : ℝ),
    taylorPolynomialValue f 0 a = C (f a)

def taylorPolynomialEval_zero : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (a x : ℝ),
    taylorPolynomialEvalValue f 0 a x = f a

def taylorRemainder_zero : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (a x : ℝ),
    taylorRemainderValue f 0 a x = f x - f a

def taylorPolynomialEval_self : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ),
    taylorPolynomialEvalValue f n a a = f a

def taylorPolynomial_derivatives_match : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ)
    (k : ℕ), k ≤ n →
    Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k (taylorPolynomialEvalValue f n a) a =
      Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k f a

def taylorPolynomial_unique : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ)
    (p : Polynomial K), p.natDegree ≤ n →
    (∀ k ≤ n, Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k (realPolynomialEvalValue p) a =
      Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k f a) → p = taylorPolynomialValue f n a

def taylorPolynomial_existsUnique : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ),
    Specs.SingleVariableAnalysis.Ch04.Higher.kTimesDifferentiableOnValue n f {a} →
    ∃! p : Polynomial K, p.degree ≤ (n : WithBot ℕ) ∧
      ∀ k ≤ n, Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k (realPolynomialEvalValue p) a =
        Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k f a

end Specs.SingleVariableAnalysis.Ch06.TaylorPolynomial
