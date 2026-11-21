import MathGenome.Internal.Specs.D05.M04.MatrixProduct

/-!
Independent definitions and statement types for paper.tex:719–720,
K05.01.system. `Fin m` and `Fin n` retain the finite ordered row and column
sets, including zero sizes. Vectors are columns and `Matrix.mulVec` is the
row-by-column product. The augmented matrix has its new column at `Fin.last n`.
This file imports no candidate implementation and assumes no proof certificates.
-/
namespace D05.M01.SystemSpec

open scoped BigOperators Matrix

universe u

/-- Type of the solution predicate, with the coefficient matrix and right-hand side explicit. -/
def IsSolutionType :=
  ∀ {K : Type u} [Field K] {m n : ℕ},
    Matrix (Fin m) (Fin n) K → (Fin m → K) → (Fin n → K) → Prop

/-- Expected value: the column vector solves the matrix equation. -/
def IsSolutionValue : IsSolutionType :=
  fun A b x => A *ᵥ x = b

/-- Type of augmentation by one final right-hand-side column. -/
def augmentedMatrixType :=
  ∀ {K : Type u} [Field K] {m n : ℕ},
    Matrix (Fin m) (Fin n) K → (Fin m → K) → Matrix (Fin m) (Fin (n + 1)) K

/-- Expected value: the first `n` columns are `A`, and the final column is `b`. -/
def augmentedMatrixValue : augmentedMatrixType :=
  fun A b i => Fin.lastCases (b i) (A i)

/-- Homogeneity is a property of the system `(A,b)`. -/
def IsHomogeneousType :=
  ∀ {K : Type u} [Field K] {m n : ℕ},
    Matrix (Fin m) (Fin n) K → (Fin m → K) → Prop

/-- Expected value: exactly the zero right-hand side is homogeneous. -/
def IsHomogeneousValue : IsHomogeneousType :=
  fun _ b => b = 0

/-- The matrix equation is exactly the displayed equation at each row. -/
def solution_iff_rows : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x : Fin n → K),
    IsSolutionValue A b x ↔ ∀ i, (∑ j : Fin n, A i j * x j) = b i

/-- Original coefficient columns embed in order in the augmentation. -/
def augmentedMatrix_castSucc : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (i : Fin m) (j : Fin n),
    augmentedMatrixValue A b i j.castSucc = A i j

/-- The new last column is precisely the right-hand side. -/
def augmentedMatrix_last : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (i : Fin m),
    augmentedMatrixValue A b i (Fin.last n) = b i

/-- This equivalence records both directions of the homogeneity convention. -/
def homogeneous_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
    IsHomogeneousValue A b ↔ b = 0

/-- The zero vector is a solution of every homogeneous system. -/
def zero_solution : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K), IsSolutionValue A 0 0

/-- With no rows there are no constraints, for every number of unknowns. -/
def empty_rows : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ}
    (A : Matrix (Fin 0) (Fin n) K) (b : Fin 0 → K) (x : Fin n → K),
    IsSolutionValue A b x

/-- There is only one possible vector of zero unknowns. -/
def empty_vector_unique : Prop :=
  ∀ {K : Type u} [Field K] (x y : Fin 0 → K), x = y

/-- The empty vector solves the system exactly when its right-hand side is zero. -/
def empty_columns_iff : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ}
    (A : Matrix (Fin m) (Fin 0) K) (b : Fin m → K) (x : Fin 0 → K),
    IsSolutionValue A b x ↔ b = 0

/-- Existence and uniqueness of a solution in zero unknowns, including zero rows. -/
def empty_columns_unique_iff : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ}
    (A : Matrix (Fin m) (Fin 0) K) (b : Fin m → K),
    (∃! x : Fin 0 → K, IsSolutionValue A b x) ↔ b = 0

end D05.M01.SystemSpec
