import MathGenome.Internal.Specs.D07.Ch08.MatrixRing
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
Independent statements for the matrix-ring counterexample in
K07.08.field_ideals, paper.tex:1414–1419. Multiplication and units are
those of the canonical square matrix ring. TwoSidedIdeal includes absorption
on both sides; no claim is made about arbitrary left ideals.
-/

universe u

namespace Specs.D07.Ch08.FieldIdealsMatrixRingSimplicity

/-- The matrix-unit extraction formula, written also as scalar multiplication
of Eₖₗ, for every choice of the four indices. -/
def MatrixUnitExtraction : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F)
    (i j k l : Fin n),
    Matrix.single k i (1 : F) * A * Matrix.single j l (1 : F) =
      A i j • Matrix.single k l (1 : F)

/-- An ideal containing one nonzero entry contains every matrix unit. -/
def MatrixUnitsInNonzeroIdeal : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ)
    (I : TwoSidedIdeal (Matrix (Fin n) (Fin n) F))
    (A : Matrix (Fin n) (Fin n) F) (i j : Fin n),
    A ∈ I → A i j ≠ 0 →
      ∀ k l : Fin n, Matrix.single k l (1 : F) ∈ I

/-- Every two-sided ideal of Mₙ(F), for positive n, is zero or the whole ring. -/
def Simplicity : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ), 0 < n →
    ∀ I : TwoSidedIdeal (Matrix (Fin n) (Fin n) F), I = ⊥ ∨ I = ⊤

/-- Two nonzero matrices with zero product, in every size at least two. -/
def HasZeroDivisors : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ), 2 ≤ n →
    ∃ A B : Matrix (Fin n) (Fin n) F, A ≠ 0 ∧ B ≠ 0 ∧ A * B = 0

/-- The defining division-ring property fails for the fixed matrix operations:
it is false that every nonzero matrix is a unit (has a two-sided inverse). -/
def NotDivisionRing : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ), 2 ≤ n →
    ¬ ∀ A : Matrix (Fin n) (Fin n) F, A ≠ 0 → IsUnit A

end Specs.D07.Ch08.FieldIdealsMatrixRingSimplicity
