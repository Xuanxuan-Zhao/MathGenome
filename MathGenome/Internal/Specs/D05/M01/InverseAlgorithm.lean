import MathGenome.Internal.Specs.D05.M01.Elimination
import MathGenome.Internal.Specs.D05.M01.PivotRank
import MathGenome.Internal.Specs.D05.M04.InverseMatrix
import Mathlib.Data.Fin.Tuple.Basic

/-!
Independent statements for K05.01.inverse_algorithm, paper.tex:778–784.
The two blocks have ordered `Fin` column indices, the left block preceding
all columns of the right block. `applyOps` executes precisely the accepted
finite lists of elementary row operations. Invertibility is `IsUnit` in the
square matrix ring, not an assumed identity for the total operation `A⁻¹`.
Every statement includes dimension zero. No implementation is imported.
-/
namespace D05.M01.InverseAlgorithmData

universe u

/-- Horizontal augmentation by a whole matrix, with the left columns first.
This differs from augmentation by the single right-hand-side vector. -/
def blockAugment {K : Type u} {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (C : Matrix (Fin m) (Fin p) K) :
    Matrix (Fin m) (Fin (n + p)) K :=
  fun i => Fin.append (A i) (C i)

end D05.M01.InverseAlgorithmData

namespace Specs.D05.M01.InverseAlgorithm

open D05.M01.InverseAlgorithmData D05.M01.Elimination D05.M01.RowOps
universe u

def block_left : Prop :=
  ∀ {K : Type u} {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (C : Matrix (Fin m) (Fin p) K) i j,
    blockAugment A C i (Fin.castAdd p j) = A i j

def block_right : Prop :=
  ∀ {K : Type u} {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (C : Matrix (Fin m) (Fin p) K) i j,
    blockAugment A C i (Fin.natAdd n j) = C i j

/-- The stated successful endpoint really is reduced echelon in all 2n
ordered columns, regardless of the entries of its right block. -/
def identity_block_reduced : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (B : Matrix (Fin n) (Fin n) K),
    (blockAugment (1 : Matrix (Fin n) (Fin n) K) B).IsReducedRowEchelon

/-- Any permitted sequence acts simultaneously on both blocks by the same
invertible multiplier. This statement quantifies over the actual operations. -/
def augmented_multiplier : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ}
    (ops : List (RowOperation K n)) (A : Matrix (Fin n) (Fin n) K),
    ∃ E : Matrix (Fin n) (Fin n) K, IsUnit E ∧
      applyOps ops (blockAugment A 1) = blockAugment (E * A) E

/-- Success proves invertibility and identifies the computed right block,
including both inverse identities. -/
def successful_run : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ}
    (ops : List (RowOperation K n)) (A B : Matrix (Fin n) (Fin n) K),
    applyOps ops (blockAugment A 1) = blockAugment 1 B →
      IsUnit A ∧ B * A = 1 ∧ A * B = 1 ∧ B = A⁻¹

/-- Full invertibility forces a reduced square matrix to be the identity. -/
def reduced_unit_eq_one : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (R : Matrix (Fin n) (Fin n) K),
    R.IsReducedRowEchelon → IsUnit R → R = 1

/-- The conclusion applies to every completed reduction of the left block. -/
def reduced_left_iff : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ}
    (ops : List (RowOperation K n)) (A : Matrix (Fin n) (Fin n) K),
    (applyOps ops A).IsReducedRowEchelon →
      (applyOps ops A = 1 ↔ IsUnit A)

/-- Elimination actually supplies a successful sequence for every invertible
input; the same sequence computes the inverse on the augmented identity. -/
def inverse_by_reduction : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    IsUnit A → ∃ ops : List (RowOperation K n),
      applyOps ops A = 1 ∧
      applyOps ops (blockAugment A 1) = blockAugment 1 A⁻¹

/-- The paper's exact reachability equivalence, with the right block explicit. -/
def inverse_algorithm : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K),
    (∃ ops : List (RowOperation K n),
      applyOps ops (blockAugment A 1) = blockAugment 1 B) ↔
      IsUnit A ∧ B = A⁻¹

/-- A missing coefficient pivot in an echelon outcome means rank less than
n and failure of invertibility; no reduced or positivity assumption is needed. -/
def missing_pivot : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ}
    (ops : List (RowOperation K n)) (A : Matrix (Fin n) (Fin n) K),
    (applyOps ops A).IsRowEchelon →
    (∃ c : Fin n, ∀ i : Fin n, ¬ (applyOps ops A).IsLeadingEntry i c) →
      A.rank < n ∧ ¬ IsUnit A

/-- The empty identity needs no operations, and its inverse is the empty
identity too. The universal results above impose no nonempty-size instance. -/
def empty_reduction : Prop :=
  ∀ {K : Type u} [Field K] (A : Matrix (Fin 0) (Fin 0) K),
    IsUnit A ∧ applyOps ([] : List (RowOperation K 0)) A = 1 ∧
      applyOps ([] : List (RowOperation K 0)) (blockAugment A 1) =
        blockAugment 1 A⁻¹

end Specs.D05.M01.InverseAlgorithm
