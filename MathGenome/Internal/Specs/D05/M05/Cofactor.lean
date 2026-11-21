import MathGenome.Internal.Specs.D05.M05.DetDefinition
import Mathlib.Order.Fin.Basic

/-!
Independent interface for paper.tex:828–832, K05.05.cofactor.
Every positive size is written `n + 1`. Indices in Lean start at zero;
the paper's row and column numbers are `i.val + 1` and `j.val + 1`.
Their sum differs by two, so the cofactor sign is unchanged.
All assertions are over arbitrary commutative unital rings.
-/

noncomputable section

open scoped BigOperators

namespace D05.M05

/-- Delete row `i` and column `j`, retaining the increasing order of the
remaining indices. `Fin.succAbove` skips exactly its specified index. -/
def deletedMatrix {R : Type*} {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) R :=
  A.submatrix i.succAbove j.succAbove

/-- The signed deleted minor, using the shared column Leibniz determinant. -/
def cofactor {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) : R :=
  (-1 : R) ^ (i.val + j.val) * determinant (deletedMatrix A i j)

end D05.M05

namespace D05.Specs.Cofactor

open D05.M05

def deletedMatrix_type := ∀ {R : Type*} {n : ℕ},
  Matrix (Fin (n + 1)) (Fin (n + 1)) R →
    Fin (n + 1) → Fin (n + 1) → Matrix (Fin n) (Fin n) R

def deletedMatrix_value : deletedMatrix_type := @D05.M05.deletedMatrix

def cofactor_type := ∀ {R : Type*} [CommRing R] {n : ℕ},
  Matrix (Fin (n + 1)) (Fin (n + 1)) R → Fin (n + 1) → Fin (n + 1) → R

def cofactor_value : cofactor_type := @D05.M05.cofactor

/-- The deletion maps preserve order and enumerate exactly the complement
of the deleted index, including when their domain is empty. -/
def deletion_indices : Prop := ∀ (n : ℕ) (i : Fin (n + 1)),
  StrictMono i.succAbove ∧ Set.range i.succAbove = {i}ᶜ

def deletedMatrix_entry : Prop := ∀ {R : Type*} {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1))
    (k l : Fin n),
  deletedMatrix A i j k l = A (i.succAbove k) (j.succAbove l)

/-- Explicit agreement with the sign written using the paper's one-based
row and column numbers. -/
def paper_sign : Prop := ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)),
  cofactor A i j =
    (-1 : R) ^ ((i.val + 1) + (j.val + 1)) * determinant (deletedMatrix A i j)

/-- Expansion along any fixed column. -/
def column_expansion : Prop := ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (j : Fin (n + 1)),
  determinant A = ∑ i, A i j * cofactor A i j

/-- Expansion along any fixed row. -/
def row_expansion : Prop := ∀ {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)),
  determinant A = ∑ j, A i j * cofactor A i j

/-- At size one the deleted minor is empty and its determinant is one. -/
def singleton_minor : Prop := ∀ {R : Type*} [CommRing R]
    (A : Matrix (Fin 1) (Fin 1) R) (i j : Fin 1),
  determinant (deletedMatrix A i j) = 1

def singleton_cofactor : Prop := ∀ {R : Type*} [CommRing R]
    (A : Matrix (Fin 1) (Fin 1) R) (i j : Fin 1), cofactor A i j = 1

def singleton_expansion : Prop := ∀ {R : Type*} [CommRing R]
    (A : Matrix (Fin 1) (Fin 1) R), determinant A = A 0 0

end D05.Specs.Cofactor
