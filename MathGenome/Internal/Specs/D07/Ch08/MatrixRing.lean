import MathGenome.Internal.Specs.D07.Ch08.RingDefinition
import Mathlib.Data.Matrix.Basis

/-!
Independent specifications for K07.08.matrix_ring, paper.tex:1257–1271.
`Matrix (Fin n) (Fin n) R` uses the same canonical `Matrix` type, entrywise
addition, and row-by-column multiplication as the accepted D05 matrix
conventions (D05.M04.MatrixProductSpec). We impose neither commutativity
nor nontriviality on `R` in the construction, formulas, or boundary cases.
The elementary matrices are exactly `Matrix.single i j 1`.
-/

universe u

namespace Specs.D07.Ch08.MatrixRing

open scoped BigOperators

/-- A ring structure retaining the specified entrywise additive group,
row-by-column multiplication, and diagonal identity. -/
def RingConstruction : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ),
    ∃ s : Ring (Matrix (Fin n) (Fin n) R),
      s.toAddCommGroup = Matrix.addCommGroup ∧
      s.toMul = (inferInstance : Mul (Matrix (Fin n) (Fin n) R)) ∧
      s.toOne = (inferInstance : One (Matrix (Fin n) (Fin n) R))

/-- The canonical operations, including the diagonal matrix identity. -/
def Entries : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) R) (i j : Fin n),
    (A + B) i j = A i j + B i j ∧
    (A * B) i j = ∑ k, A i k * B k j ∧
    (1 : Matrix (Fin n) (Fin n) R) i j = (if i = j then 1 else 0) ∧
    (0 : Matrix (Fin n) (Fin n) R) i j = 0 ∧
    (-A) i j = -(A i j)

/-- Both bracketings give the stated common double sum, in the original
factor order even when multiplication in `R` is noncommutative. -/
def TripleProductEntries : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ)
    (A B C : Matrix (Fin n) (Fin n) R) (i j : Fin n),
    ((A * B) * C) i j = ∑ k, ∑ l, (A i k * B k l) * C l j ∧
    (A * (B * C)) i j = ∑ k, ∑ l, (A i k * B k l) * C l j

/-- Associativity, distributivity on both sides, and both identity laws
hold for precisely the canonical operations. -/
def RingLaws : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ),
    RingDefinition.UnitalRingLaws (Matrix (Fin n) (Fin n) R)

/-- This conditional is the Kronecker-delta formula `Eᵢⱼ Eₖₗ = δⱼₖ Eᵢₗ`. -/
def MatrixUnitProduct : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ) (i j k l : Fin n),
    Matrix.single i j (1 : R) * Matrix.single k l (1 : R) =
      if j = k then Matrix.single i l (1 : R) else 0

/-- For any two distinct indices, the displayed `E₁₁,E₁₂,E₂₂`
calculations and the nonzero witnesses all hold. -/
def MatrixUnitExamples : Prop :=
  ∀ (R : Type u) [Ring R] [Nontrivial R] (n : ℕ) (i j : Fin n), i ≠ j →
    Matrix.single i i (1 : R) * Matrix.single i j (1 : R) =
      Matrix.single i j (1 : R) ∧
    Matrix.single i j (1 : R) ≠ 0 ∧
    Matrix.single i j (1 : R) * Matrix.single i i (1 : R) = 0 ∧
    Matrix.single i i (1 : R) * Matrix.single j j (1 : R) = 0 ∧
    Matrix.single i i (1 : R) ≠ 0 ∧ Matrix.single j j (1 : R) ≠ 0

/-- This includes every nontrivial commutative base ring. -/
def Noncommutative : Prop :=
  ∀ (R : Type u) [Ring R] [Nontrivial R] (n : ℕ), 2 ≤ n →
    ¬ ∀ A B : Matrix (Fin n) (Fin n) R, A * B = B * A

/-- Two nonzero matrices have zero product, exhibiting zero divisors in
the source's sense without assuming the base has zero divisors. -/
def HasZeroDivisors : Prop :=
  ∀ (R : Type u) [Ring R] [Nontrivial R] (n : ℕ), 2 ≤ n →
    ∃ A B : Matrix (Fin n) (Fin n) R, A ≠ 0 ∧ B ≠ 0 ∧ A * B = 0

/-- The isomorphism for size one is evaluation at the only entry;
its inverse sends a scalar to the constant one-by-one matrix. -/
def SizeOne : Prop :=
  ∀ (R : Type u) [Ring R],
    ∃ e : Matrix (Fin 1) (Fin 1) R ≃+* R,
      (∀ A, e A = A 0 0) ∧ (∀ r i j, e.symm r i j = r)

/-- The empty matrix ring has just one element and its zero equals one. -/
def SizeZero : Prop :=
  ∀ (R : Type u) [Ring R],
    Subsingleton (Matrix (Fin 0) (Fin 0) R) ∧
      (0 : Matrix (Fin 0) (Fin 0) R) = 1

end Specs.D07.Ch08.MatrixRing
