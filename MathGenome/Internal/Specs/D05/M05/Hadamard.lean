import MathGenome.Internal.Specs.D05.M05.Hadamard.OrthogonalFactorization

/-! Independent statements for K05.05.hadamard, paper.tex:913–921.
`columnMatrix` is the shared coordinate matrix, `determinant` is the paper's
column Leibniz determinant, and the norms on columns are Euclidean (not sup).
`RCLike` includes both real and complex scalars. All statements include n = 0.
Orthogonality uses the shared first-slot-linear convention. -/

noncomputable section
open scoped BigOperators

namespace Specs.D05.M05.Hadamard

open _root_.D05 _root_.D05.M05.Hadamard

def inequality : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n)),
    ‖_root_.D05.M05.determinant (columnMatrix v)‖ ≤ ∏ j, ‖v j‖

def equality_nonzero : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n)),
    (∀ j, v j ≠ 0) →
    (‖_root_.D05.M05.determinant (columnMatrix v)‖ = ∏ j, ‖v j‖ ↔
      orthogonalFamily (F := F) v)

/-- No angle or independence hypothesis is imposed on the other columns. -/
def zero_column : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n))
    (j : Fin n), v j = 0 →
    _root_.D05.M05.determinant (columnMatrix v) = 0 ∧
    (∏ k, ‖v k‖) = 0 ∧
    ‖_root_.D05.M05.determinant (columnMatrix v)‖ = ∏ k, ‖v k‖

def dependent_strict : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n)),
    (∀ j, v j ≠ 0) → ¬ LinearIndependent F v →
    ‖_root_.D05.M05.determinant (columnMatrix v)‖ < ∏ j, ‖v j‖

/-- The full equality classification, with the singular exception explicit. -/
def equality_iff : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (v : Fin n → EuclideanSpace F (Fin n)),
    (‖_root_.D05.M05.determinant (columnMatrix v)‖ = ∏ j, ‖v j‖ ↔
      (∃ j, v j = 0) ∨ orthogonalFamily (F := F) v)

/-- An arbitrary square matrix is covered by taking its actual Euclidean columns. -/
def matrix_statement : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F),
    let v : Fin n → EuclideanSpace F (Fin n) := fun j => WithLp.toLp 2 (A.col j)
    ‖_root_.D05.M05.determinant A‖ ≤ ∏ j, ‖v j‖ ∧
    (‖_root_.D05.M05.determinant A‖ = ∏ j, ‖v j‖ ↔
      (∃ j, v j = 0) ∨ orthogonalFamily (F := F) v)

def empty_case : Prop :=
  ∀ {F : Type*} [RCLike F] (v : Fin 0 → EuclideanSpace F (Fin 0)),
    _root_.D05.M05.determinant (columnMatrix v) = 1 ∧
    (∏ j, ‖v j‖) = 1 ∧
    ‖_root_.D05.M05.determinant (columnMatrix v)‖ = ∏ j, ‖v j‖

end Specs.D05.M05.Hadamard
