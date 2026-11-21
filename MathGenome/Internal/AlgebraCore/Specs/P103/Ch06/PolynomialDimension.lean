import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.KrullDimension.Basic

/-! Independent statements of Lemma 6.4 and the polynomial assertion of
Theorem 6.6 (paper.tex:1075–1079,1089–1090).
`ringKrullDim` is the chain dimension used by `ringDimensionValue` in the
shared dimension conventions. Its values are in `WithBot ℕ∞`.
`Fin n` indexes the n variables, including no variables when n = 0.
All fields are allowed, without a cardinality or perfectness assumption. -/
namespace P103.Specs.Ch06.PolynomialDimension

universe u

def polynomial_dimensionType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞)

/-- The successor formulation avoids natural subtraction at n = 0.
Primeness includes properness, so the quotient has nonnegative dimension;
this bound also implies that its dimension is finite. -/
def nonzero_prime_quotient_dimensionType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)), P.IsPrime → P ≠ ⊥ →
    ringKrullDim (MvPolynomial (Fin n) k ⧸ P) + 1 ≤ (n : WithBot ℕ∞)

def zero_variables_primeType : Prop :=
  ∀ (k : Type u) [Field k] (P : Ideal (MvPolynomial (Fin 0) k)),
    P.IsPrime → P = ⊥

end P103.Specs.Ch06.PolynomialDimension
