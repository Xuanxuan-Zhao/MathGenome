import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

/-!
Independent specifications for Definition 7.3 and the TU closure facts in the proof
of the integer-right-hand-side theorem (paper.tex, 1557–1579).
The predicate throughout is Mathlib's `Matrix.IsTotallyUnimodular` on integer matrices.
The statements work for arbitrary index types, hence in particular all finite ones.
-/

namespace Specs.P205.Polyhedra.TotalUnimodularity

/-- Type of the canonical integer-matrix predicate. -/
def canonicalPredicateType := ∀ {m n : Type*}, Matrix m n ℤ → Prop

/-- The definition's expected value is precisely the existing canonical predicate. -/
def canonicalPredicateValue : canonicalPredicateType := Matrix.IsTotallyUnimodular

/-- The source definition: all square minors, with distinct selected rows and columns. -/
def square_minors_iff : Prop :=
  ∀ {m n : Type*} (A : Matrix m n ℤ), A.IsTotallyUnimodular ↔
    ∀ (k : ℕ) (f : Fin k → m) (g : Fin k → n),
      Function.Injective f → Function.Injective g →
      (A.submatrix f g).det = 0 ∨ (A.submatrix f g).det = 1 ∨
        (A.submatrix f g).det = -1

/-- A version allowing repetitions in both selected index maps. -/
def all_minors_iff : Prop :=
  ∀ {m n : Type*} (A : Matrix m n ℤ), A.IsTotallyUnimodular ↔
    ∀ (k : ℕ) (f : Fin k → m) (g : Fin k → n),
      (A.submatrix f g).det = 0 ∨ (A.submatrix f g).det = 1 ∨
        (A.submatrix f g).det = -1

/-- The zero-by-zero minor is included, with determinant one. -/
def empty_minor : Prop :=
  ∀ {m n : Type*} (A : Matrix m n ℤ) (f : Fin 0 → m) (g : Fin 0 → n),
    (A.submatrix f g).det = 1

/-- Transposition preserves TU in both directions. -/
def transpose_iff : Prop :=
  ∀ {m n : Type*} (A : Matrix m n ℤ),
    A.transpose.IsTotallyUnimodular ↔ A.IsTotallyUnimodular

/-- Submatrices preserve TU, with no injectivity assumptions on the index maps. -/
def submatrix : Prop :=
  ∀ {m n m' n' : Type*} {A : Matrix m n ℤ}, A.IsTotallyUnimodular →
    ∀ (f : m' → m) (g : n' → n), (A.submatrix f g).IsTotallyUnimodular

/-- In particular rows can be repeated arbitrarily. -/
def repeat_rows : Prop :=
  ∀ {m n r : Type*} {A : Matrix m n ℤ}, A.IsTotallyUnimodular →
    ∀ f : r → m, (A.submatrix f id).IsTotallyUnimodular

/-- Arbitrary permutations or equivalent presentations of the two index types. -/
def reindex_iff : Prop :=
  ∀ {m n m' n' : Type*} (A : Matrix m n ℤ) (em : m ≃ m') (en : n ≃ n'),
    (A.reindex em en).IsTotallyUnimodular ↔ A.IsTotallyUnimodular

/-- Change the signs of any chosen collection of rows. -/
def row_signs : Prop :=
  ∀ {m n : Type*} {A : Matrix m n ℤ}, A.IsTotallyUnimodular →
    ∀ s : m → ℤ, (∀ i, s i = 1 ∨ s i = -1) →
      (Matrix.of (fun i j => s i * A i j)).IsTotallyUnimodular

/-- Append arbitrary many coordinate rows with coefficient 0, 1 or -1.
The conditional form also covers the case of an empty column type. -/
def append_unitlike : Prop :=
  ∀ {m n r : Type*} [DecidableEq n] {A : Matrix m n ℤ} {B : Matrix r n ℤ},
    A.IsTotallyUnimodular →
    (Nonempty n → ∀ i, ∃ j : n, ∃ s : SignType, B i = Pi.single j s.cast) →
    (Matrix.fromRows A B).IsTotallyUnimodular

/-- Explicit signed coordinate rows, allowing any number, order and repetitions. -/
def append_signed_coordinate_rows : Prop :=
  ∀ {m n r : Type*} [DecidableEq n] {A : Matrix m n ℤ},
    A.IsTotallyUnimodular → ∀ (c : r → n) (s : r → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (Matrix.fromRows A (fun i => Pi.single (c i) (s i))).IsTotallyUnimodular

/-- Every equality row may be represented by both opposing inequality rows. -/
def opposing_rows : Prop :=
  ∀ {m n : Type*} {A : Matrix m n ℤ}, A.IsTotallyUnimodular →
    (Matrix.fromRows A (-A)).IsTotallyUnimodular

/-- Adjoining both upper and lower coordinate bound rows. -/
def append_bounds : Prop :=
  ∀ {m n : Type*} [DecidableEq n] {A : Matrix m n ℤ}, A.IsTotallyUnimodular →
    (Matrix.fromRows (Matrix.fromRows A (1 : Matrix n n ℤ))
      (-1 : Matrix n n ℤ)).IsTotallyUnimodular

/-- The two transformations can be combined, even for empty index types. -/
def opposing_rows_with_bounds : Prop :=
  ∀ {m n : Type*} [DecidableEq n] {A : Matrix m n ℤ}, A.IsTotallyUnimodular →
    (Matrix.fromRows
      (Matrix.fromRows (Matrix.fromRows A (-A)) (1 : Matrix n n ℤ))
      (-1 : Matrix n n ℤ)).IsTotallyUnimodular

end Specs.P205.Polyhedra.TotalUnimodularity
