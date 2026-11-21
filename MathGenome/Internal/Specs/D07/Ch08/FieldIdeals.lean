import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import MathGenome.Internal.Specs.D07.Ch08.FieldIdealsMatrixRingSimplicity

/-!
Independent statements for K07.08.field_ideals, paper.tex:1405–1419.
Unqualified ideals are two-sided. In the field criterion nontriviality
is an explicit hypothesis, and the field structure must retain the given
ring operations. The matrix counterexample uses the canonical operations
and asserts failure of the division-ring unit property, not merely failure
of a particular choice of inverse.
-/

universe u

namespace Specs.D07.Ch08.FieldIdeals

/-- The unit version of the ideal condition, also valid in the zero ring. -/
def NonzeroUnitsIffTrivialIdeals : Prop :=
  ∀ (R : Type u) [CommRing R],
    (∀ a : R, a ≠ 0 → IsUnit a) ↔
      ∀ I : TwoSidedIdeal R, I = ⊥ ∨ I = ⊤

/-- A field structure for precisely the supplied commutative ring. -/
def FieldCriterion : Prop :=
  ∀ (R : Type u) (s : CommRing R) [Nontrivial R],
    (∃ f : Field R, f.toRing = s.toRing) ↔
      ∀ I : TwoSidedIdeal R, I = ⊥ ∨ I = ⊤

/-- For every field and every size at least two, the matrix ring is
nontrivial and has only trivial two-sided ideals, yet is noncommutative,
has zero divisors, and fails the defining unit property of a division ring.
The extraction and scalar-inversion arguments are supplied by the
upstream matrix-ring simplicity obligation. -/
def MatrixCounterexample : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ), 2 ≤ n →
    Nontrivial (Matrix (Fin n) (Fin n) F) ∧
    (∀ I : TwoSidedIdeal (Matrix (Fin n) (Fin n) F), I = ⊥ ∨ I = ⊤) ∧
    (¬ ∀ A B : Matrix (Fin n) (Fin n) F, A * B = B * A) ∧
    (∃ A B : Matrix (Fin n) (Fin n) F, A ≠ 0 ∧ B ≠ 0 ∧ A * B = 0) ∧
    ¬ ∀ A : Matrix (Fin n) (Fin n) F, A ≠ 0 → IsUnit A

end Specs.D07.Ch08.FieldIdeals
