import MathGenome.Internal.Specs.D05.M12.GramSchmidt
import Mathlib.Analysis.InnerProductSpace.PiL2
import MathGenome.Internal.Specs.D05.M05.DetDefinition

/-! The Gram–Schmidt stage of K05.05.hadamard, paper.tex:913–921.
All column norms are Euclidean norms, over either real or complex scalars via
`RCLike`. The shared recursion fixes the residuals and the normalized vectors;
no factorization or determinant identity is assumed in these definitions.
The index `Fin n` includes the empty matrix. -/

noncomputable section
open scoped BigOperators Matrix

namespace D05.M05.Hadamard

/-- The matrix whose j-th column is the Euclidean vector v j. -/
def columnMatrix {F : Type*} [RCLike F] {n : ℕ}
    (v : Fin n → EuclideanSpace F (Fin n)) : Matrix (Fin n) (Fin n) F :=
  fun i j => v j i

/-- The normalized Gram–Schmidt vectors as matrix columns. -/
def qFactor {F : Type*} [RCLike F] {n : ℕ}
    (v : Fin n → EuclideanSpace F (Fin n)) : Matrix (Fin n) (Fin n) F :=
  columnMatrix (D05.gramSchmidtVectors (F := F) v)

/-- Projection coefficients above the diagonal, positive residual norms on the
 diagonal, and zero below. Positivity is a conclusion for independent inputs. -/
def rFactor {F : Type*} [RCLike F] {n : ℕ}
    (v : Fin n → EuclideanSpace F (Fin n)) : Matrix (Fin n) (Fin n) F :=
  fun i j => if i < j then
    D05.firstInner (F := F) (v j) (D05.gramSchmidtVectors (F := F) v i)
    else if i = j then (‖D05.gramSchmidtResidual (F := F) v j‖ : F) else 0

end D05.M05.Hadamard

namespace Specs.D05.M05.Hadamard.OrthogonalFactorization

open _root_.D05 _root_.D05.M05.Hadamard

/-- The actual QR factorization, with both unitary identities and its full
 triangular and positive-diagonal properties. -/
def qr_factorization : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n)),
    LinearIndependent F v →
    columnMatrix v = qFactor v * rFactor v ∧
    (qFactor v)ᴴ * qFactor v = 1 ∧ qFactor v * (qFactor v)ᴴ = 1 ∧
    (∀ i j, j < i → rFactor v i j = 0) ∧
    (∀ j, rFactor v j j = (‖gramSchmidtResidual (F := F) v j‖ : F) ∧
      0 < ‖gramSchmidtResidual (F := F) v j‖)

def det_q_norm : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n)),
    LinearIndependent F v → ‖_root_.D05.M05.determinant (qFactor v)‖ = 1

def det_columns_norm : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n)),
    LinearIndependent F v →
    ‖_root_.D05.M05.determinant (columnMatrix v)‖ = ∏ j, ‖gramSchmidtResidual (F := F) v j‖

/-- Pythagoras at each step, valid in any ambient inner-product space, including
 when the orthonormal list does not span the whole ambient space. -/
def norm_decomposition : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (v : Fin n → V), LinearIndependent F v → ∀ j,
    ‖v j‖ ^ 2 =
      (∑ i ∈ Finset.Iio j,
        ‖firstInner (F := F) (v j) (gramSchmidtVectors (F := F) v i)‖ ^ 2) +
      ‖gramSchmidtResidual (F := F) v j‖ ^ 2

/-- Every residual ratio belongs to (0,1], with the exact coefficient-vanishing
 equality criterion. No nonzero-column premise beyond independence is needed. -/
def residual_ratio : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (v : Fin n → V), LinearIndependent F v → ∀ j,
    0 < ‖gramSchmidtResidual (F := F) v j‖ / ‖v j‖ ∧
    ‖gramSchmidtResidual (F := F) v j‖ / ‖v j‖ ≤ 1 ∧
    (‖gramSchmidtResidual (F := F) v j‖ / ‖v j‖ = 1 ↔
      ∀ i, i < j → firstInner (F := F) (v j) (gramSchmidtVectors (F := F) v i) = 0)

/-- Explicit zero-dimensional determinant and product convention. -/
def empty_case : Prop :=
  ∀ {F : Type*} [RCLike F] (v : Fin 0 → EuclideanSpace F (Fin 0)),
    _root_.D05.M05.determinant (columnMatrix v) = 1 ∧
    _root_.D05.M05.determinant (qFactor v) = 1 ∧
    _root_.D05.M05.determinant (rFactor v) = 1 ∧
      (∏ j, ‖gramSchmidtResidual (F := F) v j‖) = 1

end Specs.D05.M05.Hadamard.OrthogonalFactorization
