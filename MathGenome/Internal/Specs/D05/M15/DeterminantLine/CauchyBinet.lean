import MathGenome.Internal.Specs.D05.M15.DeterminantLine.MinorCoefficients
import Mathlib.Analysis.Complex.Basic

/-! Independent statements for paper.tex:2966–2985. Subsets are enumerated
in increasing order, and determinants use the accepted column Leibniz definition.
No positivity, rank, invertibility, splitting, or characteristic assumption is
added. In particular k is allowed to be zero or larger than the inner dimension. -/

noncomputable section
namespace Specs.D05.M15.DeterminantLine.CauchyBinet

universe u
open scoped BigOperators ComplexConjugate
open D05.M05

/-- The ordered row minor, using every column in its original order. -/
def rowMinor {K : Type u} [Field K] {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) K) (S : Set.powersetCard (Fin n) k) : K :=
  determinant (X.submatrix (S.val.orderEmbOfFin S.prop) id)

/-- Gram matrix for the manuscript's first-slot-linear coordinate inner product. -/
def complexGram {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => ∑ l, X l i * conj (X l j)

def cauchy_binet : Prop :=
  ∀ {K : Type u} [Field K] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin r) K)
    (k : ℕ) (I : Set.powersetCard (Fin m) k) (J : Set.powersetCard (Fin r) k),
    determinant ((A * B).submatrix (I.val.orderEmbOfFin I.prop) (J.val.orderEmbOfFin J.prop)) =
      ∑ S : Set.powersetCard (Fin n) k,
        determinant (A.submatrix (I.val.orderEmbOfFin I.prop) (S.val.orderEmbOfFin S.prop)) *
        determinant (B.submatrix (S.val.orderEmbOfFin S.prop) (J.val.orderEmbOfFin J.prop))

def lagrange : Prop :=
  ∀ {K : Type u} [Field K] {n k : ℕ} (X Y : Matrix (Fin n) (Fin k) K),
    determinant (X.transpose * Y) =
      ∑ S : Set.powersetCard (Fin n) k, rowMinor X S * rowMinor Y S

def hermitian_lagrange : Prop :=
  ∀ {n k : ℕ} (X Y : Matrix (Fin n) (Fin k) ℂ),
    determinant (X.conjTranspose * Y) =
      ∑ S : Set.powersetCard (Fin n) k, conj (rowMinor X S) * rowMinor Y S

/-- Absolute values are the complex norm; the real squared norms are embedded in ℂ. -/
def complex_gram : Prop :=
  ∀ {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℂ),
    determinant (X.conjTranspose * X) =
      ∑ S : Set.powersetCard (Fin n) k, ((‖rowMinor X S‖ ^ 2 : ℝ) : ℂ)

def first_slot_gram_matrix : Prop :=
  ∀ {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℂ),
    complexGram X = (X.conjTranspose * X).transpose

def first_slot_gram : Prop :=
  ∀ {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℂ),
    determinant (complexGram X) =
      ∑ S : Set.powersetCard (Fin n) k, ((‖rowMinor X S‖ ^ 2 : ℝ) : ℂ)

def real_gram : Prop :=
  ∀ {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ),
    determinant (X.transpose * X) =
      ∑ S : Set.powersetCard (Fin n) k, rowMinor X S ^ 2

/-- When the inner dimension is too small, the minor and its empty sum both vanish. -/
def cauchy_binet_above_dimension : Prop :=
  ∀ {K : Type u} [Field K] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin r) K)
    (k : ℕ) (I : Set.powersetCard (Fin m) k) (J : Set.powersetCard (Fin r) k), n < k →
    determinant ((A * B).submatrix (I.val.orderEmbOfFin I.prop) (J.val.orderEmbOfFin J.prop)) = 0 ∧
      (∑ S : Set.powersetCard (Fin n) k,
        determinant (A.submatrix (I.val.orderEmbOfFin I.prop) (S.val.orderEmbOfFin S.prop)) *
        determinant (B.submatrix (S.val.orderEmbOfFin S.prop) (J.val.orderEmbOfFin J.prop))) = 0

def lagrange_above_dimension : Prop :=
  ∀ {K : Type u} [Field K] {n k : ℕ} (X Y : Matrix (Fin n) (Fin k) K), n < k →
    determinant (X.transpose * Y) = 0 ∧
      (∑ S : Set.powersetCard (Fin n) k, rowMinor X S * rowMinor Y S) = 0

def hermitian_above_dimension : Prop :=
  ∀ {n k : ℕ} (X Y : Matrix (Fin n) (Fin k) ℂ), n < k →
    determinant (X.conjTranspose * Y) = 0 ∧
      (∑ S : Set.powersetCard (Fin n) k, conj (rowMinor X S) * rowMinor Y S) = 0

/-- The empty minor is 1; the subset sum has exactly its one empty-subset term. -/
def cauchy_binet_degree_zero : Prop :=
  ∀ {K : Type u} [Field K] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin r) K)
    (I : Set.powersetCard (Fin m) 0) (J : Set.powersetCard (Fin r) 0),
    determinant ((A * B).submatrix (I.val.orderEmbOfFin I.prop) (J.val.orderEmbOfFin J.prop)) = 1 ∧
      (∑ S : Set.powersetCard (Fin n) 0,
        determinant (A.submatrix (I.val.orderEmbOfFin I.prop) (S.val.orderEmbOfFin S.prop)) *
        determinant (B.submatrix (S.val.orderEmbOfFin S.prop) (J.val.orderEmbOfFin J.prop))) = 1

def lagrange_degree_zero : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (X Y : Matrix (Fin n) (Fin 0) K),
    determinant (X.transpose * Y) = 1 ∧
      (∑ S : Set.powersetCard (Fin n) 0, rowMinor X S * rowMinor Y S) = 1

def hermitian_degree_zero : Prop :=
  ∀ {n : ℕ} (X Y : Matrix (Fin n) (Fin 0) ℂ),
    determinant (X.conjTranspose * Y) = 1 ∧
      (∑ S : Set.powersetCard (Fin n) 0, conj (rowMinor X S) * rowMinor Y S) = 1

/-- The first-slot Gram convention has the same boundary values. -/
def first_slot_gram_boundaries : Prop :=
  (∀ {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℂ), n < k →
    determinant (complexGram X) = 0) ∧
  (∀ {n : ℕ} (X : Matrix (Fin n) (Fin 0) ℂ), determinant (complexGram X) = 1)

end Specs.D05.M15.DeterminantLine.CauchyBinet
