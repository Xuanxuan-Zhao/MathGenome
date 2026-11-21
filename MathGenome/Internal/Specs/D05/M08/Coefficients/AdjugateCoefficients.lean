import MathGenome.Internal.Specs.D05.M05.Adjugate
import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M04.Trace
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Derivative

/-! Independent specification of paper.tex:1211–1226. All coefficients are
coefficients of the actual determinant and cofactor adjugate, rather than an
assumed recurrence. No characteristic or splitting assumption is imposed.
The matrix statements apply to every basis matrix of every endomorphism. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace Specs.D05.M08.Coefficients.AdjugateCoefficients

/-- The paper's plus-sign polynomial matrix. -/
def pencil {K : Type*} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (Polynomial K) := (X : Polynomial K) • 1 + A.map C

/-- Elementary coefficients in decreasing degree, including the leading one. -/
def e {K : Type*} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : ℕ) : K :=
  (D05.M05.determinant (pencil A)).coeff (n - p)

/-- Coefficients of the cofactor adjugate, in decreasing degree. -/
def Q {K : Type*} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : ℕ) :
    Matrix (Fin n) (Fin n) K :=
  (D05.M05.adjugate (pencil A)).map (fun f => f.coeff (n - 1 - p))

def determinant_expansion : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K),
  D05.M05.determinant (pencil A) =
    ∑ p ∈ Finset.range (n + 1), C (e A p) * X ^ (n - p)

def leading_coefficient : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K), e A 0 = 1

/-- The determinant polynomial has no coefficients beyond dimension. -/
def determinant_coefficient_bound : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (r : ℕ), n < r →
  (D05.M05.determinant (pencil A)).coeff r = 0

/-- Each actual cofactor polynomial has degree strictly less than dimension. -/
def adjugate_coefficient_bound : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K), 0 < n →
    ∀ (r : ℕ) (i j : Fin n), n ≤ r →
  (D05.M05.adjugate (pencil A) i j).coeff r = 0

def adjugate_expansion : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K), 0 < n →
  D05.M05.adjugate (pencil A) =
    ∑ p ∈ Finset.range n, (X ^ (n - 1 - p) : Polynomial K) • (Q A p).map C

def initial_coefficient : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K), 0 < n → Q A 0 = 1

def coefficient_recurrence : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (p : ℕ), 1 ≤ p → p < n →
  Q A p + A * Q A (p - 1) = e A p • 1

def coefficient_formula : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (p : ℕ), p < n →
  Q A p = ∑ j ∈ Finset.range (p + 1), ((-1 : K) ^ j * e A (p - j)) • A ^ j

def determinant_derivative : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K),
  (D05.M05.determinant (pencil A)).derivative =
    Matrix.trace (D05.M05.adjugate (pencil A))

def trace_coefficient : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (p : ℕ), p < n →
  Matrix.trace (Q A p) = ((n - p : ℕ) : K) * e A p

def constant_adjugate : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K), 0 < n →
  D05.M05.adjugate A =
    ∑ j ∈ Finset.range n, ((-1 : K) ^ j * e A (n - 1 - j)) • A ^ j

/-- The plus-sign polynomial and the usual characteristic polynomial. -/
def sign_conversion : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K),
  D05.M05.determinant (pencil A) = C ((-1 : K) ^ n) * A.charpoly.comp (-X)

def characteristic_expansion : Prop := ∀ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K),
  A.charpoly = ∑ p ∈ Finset.range (n + 1),
    C ((-1 : K) ^ p * e A p) * X ^ (n - p)

/-- The same coefficients for an endomorphism in any ordered basis, with
intrinsic characteristic polynomial and intrinsic trace of each coefficient. -/
def endomorphism_coefficients : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (T : V →ₗ[K] V),
  let A := Specs.D05.M04.MatrixOfMap.matrixOfMap_value b b T
  Specs.D05.M08.Charpoly.charpoly_value T =
    ∑ p ∈ Finset.range (n + 1), C ((-1 : K) ^ p * e A p) * X ^ (n - p) ∧
  ∀ p : ℕ, p < n →
    LinearMap.trace K V (Matrix.toLin b b (Q A p)) = ((n - p : ℕ) : K) * e A p

end Specs.D05.M08.Coefficients.AdjugateCoefficients
