import MathGenome.Internal.Specs.D05.M01.Echelon
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.EquivFin

/-!
Independent interface for paper.tex:762–765, K05.01.parametrization.
The pivot and solution predicates are the shared canonical predicates. The
free columns are exactly the complement of the coefficient pivot columns;
no parametrization, basis, rank, or decomposition certificate is assumed.
All shapes, including empty row and column sets, are allowed.
-/
namespace D05.M01.Parametrization

open scoped BigOperators Matrix
universe u
variable {K : Type u} [Field K] {m n : ℕ}

/-- Coefficient columns containing a leading entry. -/
abbrev PivotColumn (R : Matrix (Fin m) (Fin n) K) :=
  {j : Fin n // ∃ i, R.IsLeadingEntry i j}

/-- The remaining columns, with their original coordinate labels. -/
abbrev FreeColumn (R : Matrix (Fin m) (Fin n) K) :=
  {j : Fin n // ¬ ∃ i, R.IsLeadingEntry i j}

noncomputable instance pivotColumnFintype (R : Matrix (Fin m) (Fin n) K) :
    Fintype (PivotColumn R) := by classical exact Subtype.fintype _
noncomputable instance freeColumnFintype (R : Matrix (Fin m) (Fin n) K) :
    Fintype (FreeColumn R) := by classical exact Subtype.fintype _

/-- The number `r` of coefficient pivot columns. -/
noncomputable def pivotCount (R : Matrix (Fin m) (Fin n) K) : ℕ :=
  Fintype.card (PivotColumn R)

/-- The canonical solution space of the homogeneous system. -/
abbrev homogeneousSpace (R : Matrix (Fin m) (Fin n) K) := R.mulVecLin.ker

/-- Read off the free coordinates. -/
def freeCoordinates (R : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    FreeColumn R → K := fun j => x j

/-- The displayed formula. For a pivot column, select its pivot row.
Reducedness will prove that row unique, so the selection has no effect. -/
noncomputable def formula (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (t : FreeColumn R → K) : Fin n → K := by
  classical
  exact fun j => if h : ∃ i, R.IsLeadingEntry i j then
    b h.choose - ∑ k : FreeColumn R, R h.choose k * t k
  else t ⟨j, h⟩

end D05.M01.Parametrization

namespace Specs.D05.M01.Parametrization
open _root_.D05.M01.Parametrization
open scoped BigOperators Matrix
universe u

def parametrize_type := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K), (Fin m → K) → (FreeColumn R → K) → (Fin n → K)
noncomputable def parametrize_value : parametrize_type := @formula

def coefficient_reduced : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
  (D05.M01.SystemSpec.augmentedMatrixValue R b).IsReducedRowEchelon →
  R.IsReducedRowEchelon

def free_card : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K), Fintype.card (FreeColumn R) = n - pivotCount R

/-- In a reduced coefficient matrix each nonzero row contributes one distinct pivot. -/
def pivotCount_eq_nonzero_rows : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K), R.IsReducedRowEchelon →
  pivotCount R = Nat.card {i : Fin m // R i ≠ 0}

def parametrize_free : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (t : FreeColumn R → K)
  (j : FreeColumn R), formula R b t j = t j

def parametrize_pivot : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K), R.IsReducedRowEchelon →
  ∀ (t : FreeColumn R → K) (i : Fin m) (p : Fin n), R.IsLeadingEntry i p →
  formula R b t p = b i - ∑ j : FreeColumn R, R i j * t j

/-- This is both directions of the complete pivot-equation description. -/
def solution_iff_pivot_equations : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
  (D05.M01.SystemSpec.augmentedMatrixValue R b).IsReducedRowEchelon →
  (∃ x, D05.M01.SystemSpec.IsSolutionValue R b x) → ∀ x,
  D05.M01.SystemSpec.IsSolutionValue R b x ↔
  ∀ i p, R.IsLeadingEntry i p →
    x p = b i - ∑ j : FreeColumn R, R i j * x j

/-- Substitution satisfies every pivot row and every zero row. -/
def formula_solves : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
  (D05.M01.SystemSpec.augmentedMatrixValue R b).IsReducedRowEchelon →
  (∃ x, D05.M01.SystemSpec.IsSolutionValue R b x) → ∀ t,
  D05.M01.SystemSpec.IsSolutionValue R b (formula R b t)

/-- Each assignment of free variables extends to exactly one solution. -/
def unique_solution : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
  (D05.M01.SystemSpec.augmentedMatrixValue R b).IsReducedRowEchelon →
  (∃ x, D05.M01.SystemSpec.IsSolutionValue R b x) → ∀ t : FreeColumn R → K,
  ∃! x, D05.M01.SystemSpec.IsSolutionValue R b x ∧ freeCoordinates R x = t

/-- The bijection is the displayed formula; its inverse reads free coordinates. -/
def solution_equiv : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
  (D05.M01.SystemSpec.augmentedMatrixValue R b).IsReducedRowEchelon →
  (∃ x, D05.M01.SystemSpec.IsSolutionValue R b x) →
  ∃ e : (FreeColumn R → K) ≃ {x // D05.M01.SystemSpec.IsSolutionValue R b x},
    (∀ t, (e t).val = formula R b t) ∧
    (∀ x, e.symm x = freeCoordinates R x.val)

/-- Relabeling the free columns gives the paper's `K^(n-r)`. -/
def solution_equiv_fin : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
  (D05.M01.SystemSpec.augmentedMatrixValue R b).IsReducedRowEchelon →
  (∃ x, D05.M01.SystemSpec.IsSolutionValue R b x) →
  Nonempty ((Fin (n - pivotCount R) → K) ≃
    {x // D05.M01.SystemSpec.IsSolutionValue R b x})

/-- In the homogeneous case the same forward formula and inverse are linear. -/
def homogeneous_linear_equiv : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K), R.IsReducedRowEchelon →
  ∃ e : (FreeColumn R → K) ≃ₗ[K] homogeneousSpace R,
    (∀ t, (e t).val = formula R 0 t) ∧
    (∀ x, e.symm x = freeCoordinates R x.val)

/-- The homogeneous isomorphism also has exactly `n-r` scalar coordinates. -/
def homogeneous_linear_equiv_fin : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K), R.IsReducedRowEchelon →
  Nonempty ((Fin (n - pivotCount R) → K) ≃ₗ[K] homogeneousSpace R)

def homogeneous_dimension : Prop := ∀ {K : Type u} [Field K] {m n : ℕ}
  (R : Matrix (Fin m) (Fin n) K), R.IsReducedRowEchelon →
  Module.finrank K (homogeneousSpace R) = n - pivotCount R

end Specs.D05.M01.Parametrization
