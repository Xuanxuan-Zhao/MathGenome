import Mathlib.Data.Matrix.Mul

/-!
Independent statement types for paper.tex:630–633, K05.04.matrix_product.
We use standard `Matrix` operations over any commutative ring. Finite index
sets include the empty set; taking `Fin ℓ`, `Fin m`, ... gives the paper's
ordered rectangular sizes. No nonempty or nontrivial hypothesis is imposed.
These are arithmetic statements, so no basis or represented map is required.
-/
namespace D05.M04.MatrixProductSpec

open scoped BigOperators

/-- Addition is entrywise. -/
def add_entry : Prop :=
  ∀ {R : Type*} [CommRing R] {l n : Type*} [Fintype l] [Fintype n]
    (A B : Matrix l n R) (i : l) (j : n), (A + B) i j = A i j + B i j

/-- Scalar multiplication is entrywise. -/
def smul_entry : Prop :=
  ∀ {R : Type*} [CommRing R] {l n : Type*} [Fintype l] [Fintype n]
    (a : R) (A : Matrix l n R) (i : l) (j : n), (a • A) i j = a * A i j

/-- Multiplication is the row-by-column finite sum. -/
def mul_entry : Prop :=
  ∀ {R : Type*} [CommRing R] {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n]
    (A : Matrix l m R) (B : Matrix m n R) (i : l) (j : n),
    (A * B) i j = ∑ k, A i k * B k j

/-- Associativity for all compatible rectangular shapes. -/
def mul_assoc : Prop :=
  ∀ {R : Type*} [CommRing R] {l m n p : Type*}
    [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix l m R) (B : Matrix m n R) (C : Matrix n p R),
    (A * B) * C = A * (B * C)

/-- The common entry expansion in the paper, for both bracketings. -/
def triple_mul_entry : Prop :=
  ∀ {R : Type*} [CommRing R] {l m n p : Type*}
    [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix l m R) (B : Matrix m n R) (C : Matrix n p R) (i : l) (j : p),
    ((A * B) * C) i j = ∑ k, ∑ h, (A i h * B h k) * C k j ∧
    (A * (B * C)) i j = ∑ k, ∑ h, (A i h * B h k) * C k j

/-- The finite summation interchange used in the associativity argument. -/
def sum_interchange : Prop :=
  ∀ {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]
    (f : m → n → R), (∑ k, ∑ h, f h k) = ∑ h, ∑ k, f h k

/-- Distributing over a sum in the right factor. -/
def mul_add : Prop :=
  ∀ {R : Type*} [CommRing R] {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n]
    (A : Matrix l m R) (B C : Matrix m n R), A * (B + C) = A * B + A * C

/-- Distributing over a sum in the left factor. -/
def add_mul : Prop :=
  ∀ {R : Type*} [CommRing R] {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n]
    (A B : Matrix l m R) (C : Matrix m n R), (A + B) * C = A * C + B * C

/-- Scalar compatibility in the left factor. -/
def smul_mul : Prop :=
  ∀ {R : Type*} [CommRing R] {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n]
    (a : R) (A : Matrix l m R) (B : Matrix m n R), (a • A) * B = a • (A * B)

/-- Scalar compatibility in the right factor. -/
def mul_smul : Prop :=
  ∀ {R : Type*} [CommRing R] {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n]
    (a : R) (A : Matrix l m R) (B : Matrix m n R), A * (a • B) = a • (A * B)

/-- The identity has Kronecker-delta entries. -/
def one_entry : Prop :=
  ∀ {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n), (1 : Matrix n n R) i j = if i = j then 1 else 0

/-- The right identity has the column index set as its square shape. -/
def mul_one : Prop :=
  ∀ {R : Type*} [CommRing R] {l n : Type*}
    [Fintype l] [Fintype n] [DecidableEq n] (A : Matrix l n R),
    A * (1 : Matrix n n R) = A

/-- The left identity has the row index set as its square shape. -/
def one_mul : Prop :=
  ∀ {R : Type*} [CommRing R] {l n : Type*}
    [Fintype l] [Fintype n] [DecidableEq l] (A : Matrix l n R),
    (1 : Matrix l l R) * A = A

/-- An empty inner index set gives a zero product, regardless of outer sizes. -/
def mul_empty : Prop :=
  ∀ {R : Type*} [CommRing R] {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n] [IsEmpty m]
    (A : Matrix l m R) (B : Matrix m n R), A * B = 0

end D05.M04.MatrixProductSpec
