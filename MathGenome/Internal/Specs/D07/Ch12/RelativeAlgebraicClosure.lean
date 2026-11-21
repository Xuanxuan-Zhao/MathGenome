import Mathlib.FieldTheory.AlgebraicClosure

/-!
Independent specification for K07.12.relative_algebraic_closure,
paper.tex:3663–3670 (chapters/M07.12.tex:122–129).

The chosen `Algebra K L` records the specified embedding. No finiteness or
algebraicity assumption is made on L/K. `IntermediateField K L` records
containment of the image of K and closure under all field operations.
The carrier characterization below uses nonzero polynomial annihilators,
and the greatest-element assertion includes algebraicity of the field itself.
The rational example records the source's warning that relative algebraic
closure need not be an algebraically closed field.
-/

universe u v

namespace Specs.D07.Ch12.RelativeAlgebraicClosure

def RelativeClosureType :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    IntermediateField K L

/-- Use the canonical relative closure, rather than an unrelated overfield. -/
noncomputable def relativeClosureValue : RelativeClosureType.{u, v} :=
  fun K L _ _ _ => algebraicClosure K L

/-- Exactly the source's algebraic elements, evaluated through the chosen map. -/
def Membership : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (x : L),
    x ∈ algebraicClosure K L ↔
      ∃ p : Polynomial K, p ≠ 0 ∧ Polynomial.aeval x p = 0

def AlgebraicExtension : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Algebra.IsAlgebraic K (algebraicClosure K L)

/-- Largest, not just maximal: every algebraic intermediate field is contained. -/
def LargestAlgebraicIntermediateField : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    IsGreatest {E : IntermediateField K L | Algebra.IsAlgebraic K E}
      (algebraicClosure K L)

/-- The complete assertion without presupposing any chosen closure object. -/
def AlgebraicElementsFormField : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    ∃ A : IntermediateField K L,
      (∀ x : L, x ∈ A ↔
        ∃ p : Polynomial K, p ≠ 0 ∧ Polynomial.aeval x p = 0) ∧
      IsGreatest {E : IntermediateField K L | Algebra.IsAlgebraic K E} A

/-- For the example L = K = Q, the carrier is all of Q. -/
def RationalRelativeClosure : Prop :=
  algebraicClosure ℚ ℚ = ⊤

def RationalRelativeClosureNotAlgClosed : Prop :=
  ¬ IsAlgClosed (algebraicClosure ℚ ℚ)

end Specs.D07.Ch12.RelativeAlgebraicClosure
