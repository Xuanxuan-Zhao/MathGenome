import MathGenome.Internal.Specs.D05.M01.System
import MathGenome.Internal.D05.M04.MatrixProduct

/-! Linear systems and augmented matrices: paper.tex:719–720, K05.01.system. -/
namespace D05.M01.System

open scoped BigOperators Matrix

universe u

/-- A solution is a column vector whose matrix-vector product is the right-hand side. -/
def IsSolution {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x : Fin n → K) : Prop :=
  A *ᵥ x = b

/-- Append `b` as the final column, retaining the order of all coefficient columns. -/
def augmentedMatrix {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) : Matrix (Fin m) (Fin (n + 1)) K :=
  fun i => Fin.lastCases (b i) (A i)

/-- A system is homogeneous exactly when its right-hand side vanishes. -/
def IsHomogeneous {K : Type u} [Field K] {m n : ℕ}
    (_A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) : Prop :=
  b = 0

theorem solution_iff_rows {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x : Fin n → K) :
    IsSolution A b x ↔ ∀ i, (∑ j : Fin n, A i j * x j) = b i := by
  change A *ᵥ x = b ↔ ∀ i, (A *ᵥ x) i = b i
  exact funext_iff

theorem augmentedMatrix_castSucc {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (i : Fin m) (j : Fin n) :
    augmentedMatrix A b i j.castSucc = A i j := by
  exact Fin.lastCases_castSucc j

theorem augmentedMatrix_last {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (i : Fin m) :
    augmentedMatrix A b i (Fin.last n) = b i := by
  exact Fin.lastCases_last

theorem homogeneous_iff {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    IsHomogeneous A b ↔ b = 0 := Iff.rfl

theorem zero_solution {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) : IsSolution A 0 0 :=
  Matrix.mulVec_zero A

theorem empty_rows {K : Type u} [Field K] {n : ℕ}
    (A : Matrix (Fin 0) (Fin n) K) (b : Fin 0 → K) (x : Fin n → K) :
    IsSolution A b x := by
  funext i
  exact Fin.elim0 i

theorem empty_vector_unique {K : Type u} [Field K] (x y : Fin 0 → K) : x = y := by
  funext j
  exact Fin.elim0 j

theorem empty_columns_iff {K : Type u} [Field K] {m : ℕ}
    (A : Matrix (Fin m) (Fin 0) K) (b : Fin m → K) (x : Fin 0 → K) :
    IsSolution A b x ↔ b = 0 := by
  have hzero : A *ᵥ x = 0 := by
    funext i
    simp only [Matrix.mulVec_apply_eq_sum, Finset.univ_eq_empty, Finset.sum_empty,
      Pi.zero_apply]
  change A *ᵥ x = b ↔ b = 0
  rw [hzero, eq_comm]

theorem empty_columns_unique_iff {K : Type u} [Field K] {m : ℕ}
    (A : Matrix (Fin m) (Fin 0) K) (b : Fin m → K) :
    (∃! x : Fin 0 → K, IsSolution A b x) ↔ b = 0 := by
  constructor
  · rintro ⟨x, hx, _⟩
    exact (empty_columns_iff A b x).mp hx
  · intro hb
    refine ⟨0, (empty_columns_iff A b 0).mpr hb, ?_⟩
    intro y _
    exact empty_vector_unique y 0

end D05.M01.System
