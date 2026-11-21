import MathGenome.Internal.Specs.D05.M08.Evaluation
import Mathlib.RingTheory.Binomial

/-! Independent statements for the nilpotent lemma in K05.10.complex_square_roots
(paper.tex:1605–1614). The polynomial is a finite coefficient object. The
endomorphism algebra uses composition for multiplication and identity for 1.
No finite-dimensional or nonzero-space assumption is needed. -/

noncomputable section

namespace Specs.D05.M10.ComplexSquareRoots

/-- The finite binomial polynomial with rational coefficients transported to K. -/
def rootPolynomial_type := ∀ (K : Type*) [Field K] [CharZero K], ℕ → Polynomial K

def rootPolynomial_value : rootPolynomial_type := fun K _ _ r =>
  ∑ k ∈ Finset.range r, Polynomial.monomial k (↑(Ring.choose (1 / 2 : ℚ) k) : K)

/-- The exact formal congruence; it also makes sense when r = 0. -/
def polynomial_congruence : Prop := ∀ (K : Type*) [Field K] [CharZero K] (r : ℕ),
  (Polynomial.X : Polynomial K) ^ r ∣ rootPolynomial_value K r ^ 2 - (1 + Polynomial.X)

/-- Substitution of the constructed polynomial at a nilpotent operator. -/
def polynomial_square_root : Prop :=
  ∀ (K V : Type*) [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (Q : Module.End K V) (r : ℕ), 1 ≤ r → Q ^ r = 0 →
      (Polynomial.aeval Q (rootPolynomial_value K r)) ^ 2 = 1 + Q

/-- Existence with a finite degree bound, including r = 1 and the zero space. -/
def exists_polynomial_square_root : Prop :=
  ∀ (K V : Type*) [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (Q : Module.End K V) (r : ℕ), 1 ≤ r → Q ^ r = 0 →
      ∃ q : Polynomial K, q.natDegree < r ∧ (Polynomial.aeval Q q) ^ 2 = 1 + Q

end Specs.D05.M10.ComplexSquareRoots
