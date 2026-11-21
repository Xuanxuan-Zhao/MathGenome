import MathGenome.Internal.Specs.D05.M05.Alternating
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Independent interface for paper.tex:798–802, K05.05.det_definition.
The determinant is the column-indexed Leibniz sum with the shared
inversion-parity sign. All statements allow every commutative unital ring,
including characteristic two and the zero ring, and every natural size.
-/

noncomputable section

open scoped BigOperators

namespace D05.M05

/-- The paper's determinant, with the empty product and sum conventions of
finite sums over permutations. Row `σ j` is selected in column `j`. -/
def determinant {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : R :=
  ∑ σ : Equiv.Perm (Fin n),
    (D05.Foundations.permutationSign σ : R) * ∏ j, A (σ j) j

end D05.M05

namespace D05.Specs.DetDefinition

open D05.M05 D05.Foundations

def determinant_type := ∀ {R : Type*} [CommRing R] {n : ℕ},
  Matrix (Fin n) (Fin n) R → R

def determinant_value : determinant_type := @D05.M05.determinant

/-- Explicit bridge to the standard library determinant. -/
def matrix_det_bridge : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    determinant A = Matrix.det A

/-- The full column-indexed Leibniz formula with the paper's sign. -/
def leibniz_formula : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    determinant A = ∑ σ : Equiv.Perm (Fin n),
      (permutationSign σ : R) * ∏ j, A (σ j) j

/-- There is precisely one permutation in size zero, with sign one; every
empty product appearing in its determinant expansion is one. -/
def empty_expansion : Prop :=
  (∀ σ : Equiv.Perm (Fin 0), σ = 1 ∧ permutationSign σ = 1) ∧
  (∀ {R : Type*} [CommRing R] (A : Matrix (Fin 0) (Fin 0) R)
    (σ : Equiv.Perm (Fin 0)), (∏ j, A (σ j) j) = 1)

def empty_determinant : Prop :=
  ∀ {R : Type*} [CommRing R] (A : Matrix (Fin 0) (Fin 0) R),
    determinant A = 1

/-- Only the identity-permutation summand can contribute on the identity
matrix; this statement is also valid in the zero ring. -/
def identity_summand : Prop :=
  ∀ {R : Type*} [CommRing R] (n : ℕ) (σ : Equiv.Perm (Fin n)),
    (permutationSign σ : R) * (∏ j, (1 : Matrix (Fin n) (Fin n) R) (σ j) j) =
      if σ = 1 then 1 else 0

def identity_determinant : Prop :=
  ∀ {R : Type*} [CommRing R] (n : ℕ),
    determinant (1 : Matrix (Fin n) (Fin n) R) = 1

/-- Additivity in any one column, with all other columns held fixed. -/
def column_add : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (j : Fin n) (u v : Fin n → R),
    determinant (A.updateCol j (u + v)) =
      determinant (A.updateCol j u) + determinant (A.updateCol j v)

/-- Homogeneity in any one column. -/
def column_smul : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (j : Fin n) (a : R) (u : Fin n → R),
    determinant (A.updateCol j (a • u)) = a * determinant (A.updateCol j u)

/-- Right composition with the transposition is an involution without fixed
points on the permutation index set. -/
def pairing_involution : Prop :=
  ∀ (n : ℕ) (j k : Fin n), j ≠ k → ∀ σ : Equiv.Perm (Fin n),
    (σ * Equiv.swap j k) * Equiv.swap j k = σ ∧ σ * Equiv.swap j k ≠ σ

/-- Equal columns make the paired scalar products equal and the signed
summands opposite. No cancellation by two is involved. -/
def paired_summands : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (j k : Fin n), j ≠ k → (∀ i, A i j = A i k) →
    ∀ σ : Equiv.Perm (Fin n),
      (∏ l, A ((σ * Equiv.swap j k) l) l) = (∏ l, A (σ l) l) ∧
      (permutationSign (σ * Equiv.swap j k) : R) *
          (∏ l, A ((σ * Equiv.swap j k) l) l) =
        -((permutationSign σ : R) * ∏ l, A (σ l) l)

/-- Alternation is vanishing on equal, distinct columns, in every
characteristic, rather than merely a permutation-sign rule. -/
def equal_columns_zero : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (j k : Fin n), j ≠ k → (∀ i, A i j = A i k) → determinant A = 0

/-- Bundled existence of the normalized alternating multilinear form on
column tuples. `v j i` is row `i` of column `j`. -/
def normalized_column_form : Prop :=
  ∀ (R : Type*) [CommRing R] (n : ℕ),
    ∃ f : AlternatingMap R (Fin n → R) R (Fin n),
      (∀ v : Fin n → (Fin n → R), f v = determinant (Matrix.of (fun i j => v j i))) ∧
      f (fun j i => (1 : Matrix (Fin n) (Fin n) R) i j) = 1

end D05.Specs.DetDefinition
