import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.M04.MatrixOfMap
import MathGenome.Internal.Specs.D05.M09.Eigenspace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent specifications for K05.09.diagonalizable (paper.tex:1272–1273).

Diagonalizability means existence of a finite eigenbasis over the named field.
The index `Fin n` follows the upstream ordered-basis convention; `n = 0` is
allowed. The matrix is the upstream matrix of the same endomorphism with the
same basis on both sides. Equality with `Matrix.diagonal μ` specifies every
entry, including the diagonal entries and their order.
-/

namespace Specs.D05.M09.Diagonalizable

universe u v

def diagonalizable_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    [FiniteDimensional K V] → Module.End K V → Prop

/-- The paper's eigenbasis definition, with all eigenvalues in `K`. -/
def diagonalizable_value : diagonalizable_type.{u, v} :=
  fun K V _ _ _ _ T =>
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K V) (μ : Fin n → K),
      ∀ i, T (b i) = μ i • b i

/-- The column of an eigenbasis vector has just its own eigenvalue coordinate. -/
def coordinate_column : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (μ : Fin n → K),
    (∀ i, T (b i) = μ i • b i) →
      ∀ j, b.repr (T (b j)) = μ j • Finsupp.single j (1 : K)

/-- Basis vectors satisfying these equations really are nonzero eigenvectors. -/
def eigenbasis_iff_hasEigenvector : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (μ : Fin n → K),
    (∀ i, T (b i) = μ i • b i) ↔ ∀ i, T.HasEigenvector (μ i) (b i)

/-- Both implications for a specified basis and a specified diagonal. -/
def matrix_eq_diagonal_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (μ : Fin n → K),
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value b b T = Matrix.diagonal μ ↔
      ∀ i, T (b i) = μ i • b i

/-- Diagonalizability is equivalent to a diagonal matrix in some basis. -/
def diagonalizable_iff_diagonal_matrix : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    diagonalizable_value K V T ↔
      ∃ (n : ℕ) (b : Module.Basis (Fin n) K V) (μ : Fin n → K),
        Specs.D05.M04.MatrixOfMap.matrixOfMap_value b b T = Matrix.diagonal μ

/-- On a zero space the empty basis and empty diagonal give the claimed matrix. -/
def empty_basis_diagonalizes : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Subsingleton V]
    (T : Module.End K V),
    ∃ b : Module.Basis (Fin 0) K V,
      (∀ i, T (b i) = (0 : K) • b i) ∧
        Specs.D05.M04.MatrixOfMap.matrixOfMap_value b b T = Matrix.diagonal (fun _ => (0 : K))

/-- The unique operator on the zero space is zero and diagonalizable. -/
def zero_space_diagonalizable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Subsingleton V] (T : Module.End K V),
    T = 0 ∧ diagonalizable_value K V T

end Specs.D05.M09.Diagonalizable
