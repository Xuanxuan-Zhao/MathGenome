import MathGenome.Internal.Specs.D05.M01.System
import MathGenome.Internal.Specs.D05.M05.DetInvertible
import MathGenome.Internal.Specs.D05.M05.DetUniqueness

/-!
Independent statements for paper.tex:886–889, K05.05.cramer.
Columns are indexed by `Fin n`; `A.updateCol j b` replaces precisely column
`j` by the right-hand side. The determinant is the shared column Leibniz
determinant, and solutions use the upstream matrix-equation predicate.
The column-combination identity works over any commutative ring. Division
and the inverse solution are asserted over fields with nonzero determinant.
All sizes include zero, without a positivity or characteristic assumption.
-/

namespace D05.Specs.Cramer

open D05.M05
open D05.M01.SystemSpec (IsSolutionValue)
open scoped Matrix

/-- Multilinearity and alternation retain only the coefficient of column `j`.
This identity needs neither a field nor a nonzero determinant. -/
def column_combination : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (x : Fin n → R) (j : Fin n),
    determinant (A.updateCol j (A *ᵥ x)) = x j * determinant A

/-- The undivided identity for every solution, including singular systems. -/
def replacement_of_solution : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (b x : Fin n → K), IsSolutionValue A b x → ∀ j : Fin n,
    determinant (A.updateCol j b) = x j * determinant A

/-- The designated solution exists and every solution equals it. -/
def solution_iff_inverse : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (b : Fin n → K), determinant A ≠ 0 → ∀ x : Fin n → K,
    IsSolutionValue A b x ↔ x = A⁻¹ *ᵥ b

/-- Nonzero determinant gives existence and uniqueness for every right-hand side. -/
def existsUnique_solution : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (b : Fin n → K), determinant A ≠ 0 →
    ∃! x : Fin n → K, IsSolutionValue A b x

/-- Cramer's coordinate formula for any solution under the nonvanishing hypothesis. -/
def cramer_coordinates : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (b x : Fin n → K), determinant A ≠ 0 → IsSolutionValue A b x →
    ∀ j : Fin n, x j = determinant (A.updateCol j b) / determinant A

/-- In particular, the coordinates of the inverse solution are the displayed ratios. -/
def inverse_coordinates : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (b : Fin n → K), determinant A ≠ 0 → ∀ j : Fin n,
    (A⁻¹ *ᵥ b) j = determinant (A.updateCol j b) / determinant A

/-- The empty determinant is one and the empty system has its unique empty solution.
The coordinate statements above quantify over `Fin 0`, so have no instances here. -/
def empty_system : Prop :=
  ∀ {K : Type*} [Field K] (A : Matrix (Fin 0) (Fin 0) K) (b : Fin 0 → K),
    determinant A = 1 ∧ ∃! x : Fin 0 → K, IsSolutionValue A b x

/-- A singular system can have multiple solutions or no solution, depending on
the right-hand side. Thus no existence/uniqueness claim is made by dividing by zero. -/
def singular_examples : Prop :=
  ∀ (K : Type*) [Field K],
    let A : Matrix (Fin 1) (Fin 1) K := 0
    determinant A = 0 ∧
      (∃ x y : Fin 1 → K,
        IsSolutionValue A 0 x ∧ IsSolutionValue A 0 y ∧ x ≠ y) ∧
      ¬ ∃ x : Fin 1 → K, IsSolutionValue A (fun _ => 1) x

end D05.Specs.Cramer
