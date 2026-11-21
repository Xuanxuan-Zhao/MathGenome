import MathGenome.Internal.Specs.D05.M09.Gershgorin
import MathGenome.Internal.Specs.D05.M05.DetInvertible
import Mathlib.Analysis.Normed.Field.Basic

/-!
Independent specifications for K05.09.diagonal_dominance, paper.tex:1344–1345.
Norms are the real or complex absolute values. The erased index excludes the
single diagonal entry. Invertibility is existence of a two-sided inverse over
the matrix's original field, and the determinant is the shared paper determinant.
Every size, including zero, is allowed. The real-to-complex determinant bridge
makes scalar extension explicit; no eigenvalue is silently moved between fields.
-/

namespace Specs.D05.M09.DiagonalDominance

open D05.M05

/-- Strict row dominance excludes zero from each individual complex row disk. -/
def complex_row_disks_exclude_zero : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
    (∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖) →
      ∀ i, ¬ (‖(0 : ℂ) - A i i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖)

/-- The corresponding exclusion for complex column disks. -/
def complex_column_disks_exclude_zero : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
    (∀ i, ∑ j ∈ Finset.univ.erase i, ‖A j i‖ < ‖A i i‖) →
      ∀ i, ¬ (‖(0 : ℂ) - A i i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖A j i‖)

/-- Row dominance gives all the source conclusions over the complex field. -/
def complex_row : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
    (∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖) →
      ¬ Module.End.HasEigenvalue A.mulVecLin 0 ∧
      determinant A ≠ 0 ∧
      ∃ B : Matrix (Fin n) (Fin n) ℂ, B * A = 1 ∧ A * B = 1

/-- Column dominance gives the same conclusions over the complex field. -/
def complex_column : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
    (∀ i, ∑ j ∈ Finset.univ.erase i, ‖A j i‖ < ‖A i i‖) →
      ¬ Module.End.HasEigenvalue A.mulVecLin 0 ∧
      determinant A ≠ 0 ∧
      ∃ B : Matrix (Fin n) (Fin n) ℂ, B * A = 1 ∧ A * B = 1

/-- Complexification preserves the real determinant and detects its nonvanishing. -/
def real_complex_determinant : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    determinant (A.map (fun x => (x : ℂ))) = ((determinant A : ℝ) : ℂ) ∧
    (determinant (A.map (fun x => (x : ℂ))) ≠ 0 ↔ determinant A ≠ 0)

/-- The real row theorem concludes invertibility over the real field itself. -/
def real_row : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    (∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖) →
      ¬ Module.End.HasEigenvalue A.mulVecLin 0 ∧
      determinant A ≠ 0 ∧
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B * A = 1 ∧ A * B = 1

/-- The real column theorem, also with a real two-sided inverse. -/
def real_column : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    (∀ i, ∑ j ∈ Finset.univ.erase i, ‖A j i‖ < ‖A i i‖) →
      ¬ Module.End.HasEigenvalue A.mulVecLin 0 ∧
      determinant A ≠ 0 ∧
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B * A = 1 ∧ A * B = 1

/-- The all-ones matrix of size two is non-strictly dominant but singular.
The statement applies in particular over both real and complex scalars. -/
def nonstrict_counterexample : Prop :=
  ∀ (K : Type*) [NormedField K],
    let A : Matrix (Fin 2) (Fin 2) K := Matrix.of (fun _ _ => 1)
    (∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ‖A i i‖) ∧
    determinant A = 0 ∧
    ¬ (∃ B : Matrix (Fin 2) (Fin 2) K, B * A = 1 ∧ A * B = 1)

/-- The empty matrix has vacuous row and column conditions and is invertible. -/
def empty_matrix : Prop :=
  ∀ (K : Type*) [NormedField K] (A : Matrix (Fin 0) (Fin 0) K),
    (∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖) ∧
    (∀ i, ∑ j ∈ Finset.univ.erase i, ‖A j i‖ < ‖A i i‖) ∧
    determinant A = 1 ∧
    ∃ B : Matrix (Fin 0) (Fin 0) K, B * A = 1 ∧ A * B = 1

end Specs.D05.M09.DiagonalDominance
