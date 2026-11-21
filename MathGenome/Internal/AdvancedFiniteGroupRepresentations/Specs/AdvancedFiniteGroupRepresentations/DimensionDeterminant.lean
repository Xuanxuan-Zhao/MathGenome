import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CornerRecurrence
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-! FR-B07, Frobenius–Young dimension determinant, source lines 700–736.
The canonical row lengths include trailing zeros. Both matrix indices are zero
based, so their difference agrees with the printed one-based difference.
The entries and equality are rational; factorials with negative indices have
value zero. Padding is permitted for every `r ≥ length p`, including `r = 0`.
-/
noncomputable section
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Reciprocal factorial, with the explicit negative-index zero convention. -/
def factorialReciprocal (a : ℤ) : ℚ :=
  if 0 ≤ a then 1 / (a.toNat.factorial : ℚ) else 0

def factorialReciprocalType := ℤ → ℚ

/-- The `r` by `r` matrix in the Frobenius–Young formula. -/
def dimensionMatrix {n : ℕ} (p : Partition n) (r : ℕ) : Matrix (Fin r) (Fin r) ℚ :=
  fun i j => factorialReciprocal ((rowLength p i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ))

def dimensionMatrixType := {n : ℕ} → Partition n → (r : ℕ) → Matrix (Fin r) (Fin r) ℚ

def dimensionDeterminant {n : ℕ} (p : Partition n) (r : ℕ) : ℚ :=
  (dimensionMatrix p r).det

def dimensionDeterminantType := {n : ℕ} → Partition n → ℕ → ℚ

/-- Full formula, with every allowed number of padded rows. -/
def dimensionDeterminant_formulaType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (r : ℕ), length p ≤ r →
    (standardTableauCount p : ℚ) = (n.factorial : ℚ) * dimensionDeterminant p r

end Specs.AdvancedFiniteGroupRepresentations
