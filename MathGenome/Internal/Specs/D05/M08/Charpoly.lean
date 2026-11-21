import MathGenome.Internal.Specs.D05.M04.ChangeBasis
import MathGenome.Internal.Specs.D05.M05.DetProduct
import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
Independent specification of K05.08.charpoly, paper.tex:1145–1150.
Scalars are an arbitrary field and the space is finite dimensional, including
zero dimension. Polynomials are formal coefficient polynomials. We reuse the
standard endomorphism characteristic polynomial; `determinant_formula` is the
required bridge to the shared column Leibniz determinant of `xI - [T]`.
No characteristic, splitting, or positive-dimension assumption is imposed.
-/

noncomputable section

namespace Specs.D05.M08.Charpoly

universe u v

/-- The characteristic polynomial is a scalar polynomial attached to an
endomorphism, with no basis argument in its final interface. -/
def charpoly_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] →
  [Module K V] → [FiniteDimensional K V] → (V →ₗ[K] V) → Polynomial K

/-- Canonical library object, to be identified with the paper's formula. -/
def charpoly_value : charpoly_type.{u, v} := fun T => LinearMap.charpoly T

/-- The standard matrix characteristic polynomial is the paper's determinant
of the polynomial matrix `xI - A`, where entries of `A` become constants. -/
def matrix_det_formula : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    Matrix.charpoly A = D05.M05.determinant
      (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) - A.map Polynomial.C)

/-- Every ordered basis computes the same characteristic polynomial by the
paper's original determinant, using the accepted column matrix of the map. -/
def determinant_formula : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (T : V →ₗ[K] V),
    charpoly_value T = D05.M05.determinant
      (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) -
        (Specs.D05.M04.MatrixOfMap.matrixOfMap_value b b T).map Polynomial.C)

/-- Similarity invariance with exactly the paper's `P⁻¹ A P` convention.
Invertibility of `P` is explicit; the operator matrix `A` may be singular. -/
def similarity_invariance : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A P : Matrix (Fin n) (Fin n) K),
    IsUnit P →
      D05.M05.determinant
        (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) -
          (P⁻¹ * A * P).map Polynomial.C) =
      D05.M05.determinant
        (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) - A.map Polynomial.C)

/-- Changing the basis in both the domain and codomain changes none of the
scalar polynomial. The two finite ordered bases may have different index types. -/
def basis_independence : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n m : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K V)
    (T : V →ₗ[K] V),
    D05.M05.determinant
      (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) -
        (Specs.D05.M04.MatrixOfMap.matrixOfMap_value b b T).map Polynomial.C) =
    D05.M05.determinant
      (Matrix.scalar (Fin m) (Polynomial.X : Polynomial K) -
        (Specs.D05.M04.MatrixOfMap.matrixOfMap_value c c T).map Polynomial.C)

def monic : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V), (charpoly_value T).Monic

/-- Natural degree, together with monicity, gives the nonzero degree used in
the paper, including degree zero for the constant polynomial one. -/
def natDegree : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V),
    (charpoly_value T).natDegree = Module.finrank K V

/-- Degree with a separate bottom value for the zero polynomial. -/
def degree : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V),
    (charpoly_value T).degree = (Module.finrank K V : WithBot ℕ)

/-- The empty matrix has characteristic polynomial one. -/
def empty_matrix : Prop :=
  ∀ {K : Type*} [Field K] (A : Matrix (Fin 0) (Fin 0) K),
    D05.M05.determinant
      (Matrix.scalar (Fin 0) (Polynomial.X : Polynomial K) - A.map Polynomial.C) = 1

/-- The full zero-space conclusion, expressed intrinsically by dimension. -/
def zero_dimensional : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V),
    Module.finrank K V = 0 → charpoly_value T = 1

end Specs.D05.M08.Charpoly
