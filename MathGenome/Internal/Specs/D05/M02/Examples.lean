import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.M02.Dimension
import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.Polynomial.Basic

/-! Independent statements for K05.02.examples, paper.tex:523–524.
All polynomials are formal coefficient polynomials. The degree-at-most-`d`
space is presented as `degreeLT K (d + 1)`; `degree_bound` supplies the exact
bridge, including the zero polynomial. No field is assumed infinite.
-/

namespace Specs.D05.M02.Examples

open scoped BigOperators

def coordinate_basis : Prop :=
  ∀ (K : Type*) [Field K] (n : ℕ),
    ∃ b : Module.Basis (Fin n) K (D05.Foundations.CoordinateModule K n),
      (∀ j, b j = Pi.single j 1) ∧ ∀ x j, b.repr x j = x j

def coordinate_expansion : Prop :=
  ∀ (K : Type*) [Field K] (n : ℕ) (x : D05.Foundations.CoordinateModule K n),
    x = ∑ j : Fin n, x j • Pi.single j 1

def coordinate_dimension : Prop :=
  ∀ (K : Type*) [Field K] (n : ℕ),
    FiniteDimensional K (D05.Foundations.CoordinateModule K n) ∧
      Module.finrank K (D05.Foundations.CoordinateModule K n) = n

def matrix_basis : Prop :=
  ∀ (K : Type*) [Field K] (m n : ℕ),
    ∃ b : Module.Basis (Fin m × Fin n) K (Matrix (Fin m) (Fin n) K),
      (∀ ij, b ij = Matrix.single ij.1 ij.2 1) ∧
        ∀ A ij, b.repr A ij = A ij.1 ij.2

def matrix_expansion : Prop :=
  ∀ (K : Type*) [Field K] (m n : ℕ) (A : Matrix (Fin m) (Fin n) K),
    A = ∑ ij : Fin m × Fin n, A ij.1 ij.2 • Matrix.single ij.1 ij.2 1

def matrix_dimension : Prop :=
  ∀ (K : Type*) [Field K] (m n : ℕ),
    FiniteDimensional K (Matrix (Fin m) (Fin n) K) ∧
      Module.finrank K (Matrix (Fin m) (Fin n) K) = m * n

def degree_bound : Prop :=
  ∀ (K : Type*) [Field K] (d : ℕ) (p : Polynomial K),
    (p ∈ Polynomial.degreeLT K (d + 1) ↔ p.degree ≤ (d : WithBot ℕ)) ∧
      (0 : Polynomial K) ∈ Polynomial.degreeLT K (d + 1)

def bounded_polynomial_basis : Prop :=
  ∀ (K : Type*) [Field K] (d : ℕ),
    ∃ b : Module.Basis (Fin (d + 1)) K (Polynomial.degreeLT K (d + 1)),
      (∀ i, (b i : Polynomial K) = Polynomial.X ^ (i : ℕ)) ∧
        ∀ p i, b.repr p i = (p : Polynomial K).coeff i

def bounded_polynomial_expansion : Prop :=
  ∀ (K : Type*) [Field K] (d : ℕ) (p : Polynomial.degreeLT K (d + 1)),
    (p : Polynomial K) =
      ∑ i : Fin (d + 1), (p : Polynomial K).coeff i • Polynomial.X ^ (i : ℕ)

def bounded_polynomial_dimension : Prop :=
  ∀ (K : Type*) [Field K] (d : ℕ),
    FiniteDimensional K (Polynomial.degreeLT K (d + 1)) ∧
      Module.finrank K (Polynomial.degreeLT K (d + 1)) = d + 1

def monomials_independent : Prop :=
  ∀ (K : Type*) [Field K],
    LinearIndependent K (fun i : ℕ => (Polynomial.X : Polynomial K) ^ i)

def polynomial_infinite_dimensional : Prop :=
  ∀ (K : Type*) [Field K], ¬ FiniteDimensional K (Polynomial K)

/-- These are the finitely supported coordinate vectors inside the full product,
not a claim that they span all sequences. -/
def standard_sequences_independent : Prop :=
  ∀ (K : Type*) [Field K],
    LinearIndependent K (fun i : ℕ => (Pi.single i 1 : ℕ → K))

def sequences_infinite_dimensional : Prop :=
  ∀ (K : Type*) [Field K], ¬ FiniteDimensional K (ℕ → K)

/-- An explicit obstruction to treating formal polynomials as value functions. -/
def finite_field_evaluation : Prop :=
  ∀ (K : Type*) [Field K] [Fintype K],
    (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) ≠ 0 ∧
      (∀ a : K, Polynomial.eval a
        (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) = 0) ∧
      ¬ Function.Injective (fun p : Polynomial K => fun a : K => Polynomial.eval a p)

end Specs.D05.M02.Examples
