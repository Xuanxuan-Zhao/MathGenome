import MathGenome.Internal.Specs.D07.Ch19.ResultantDefinition
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The common-root criterion, K07.19.resultant_common_root, paper.tex:5343–5369.
The resultant is the ordinary, actual-degree determinant in the notes' convention.
Strict degree bounds use `degree`, so zero coefficients are permitted in a relation.
The chosen root field is an algebraic, algebraically closed extension with its
specified base-field embedding. There is no characteristic restriction. -/

universe u v
namespace Specs.D07.Ch19.ResultantCommonRoot
open Polynomial
open Specs.D07.Ch19.ResultantDefinition

def CommonDivisorCriterion : Prop :=
  ∀ (F : Type u) [Field F] (f g : F[X]),
    f ≠ 0 → g ≠ 0 → 0 < f.natDegree → 0 < g.natDegree →
    (ordinaryResultant f g = 0 ↔
      ∃ h : F[X], 0 < h.degree ∧ h ∣ f ∧ h ∣ g)

def CommonRootCriterion : Prop :=
  ∀ (F : Type u) (Ω : Type v) [Field F] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω] [IsAlgClosed Ω] (f g : F[X]),
    f ≠ 0 → g ≠ 0 → 0 < f.natDegree → 0 < g.natDegree →
    (ordinaryResultant f g = 0 ↔
      ∃ x : Ω, aeval x f = 0 ∧ aeval x g = 0)

def BoundedRelationCriterion : Prop :=
  ∀ (F : Type u) [Field F] (f g : F[X]),
    f ≠ 0 → g ≠ 0 → 0 < f.natDegree → 0 < g.natDegree →
    (ordinaryResultant f g = 0 ↔
      ∃ A B : F[X], A.degree < (g.natDegree : WithBot ℕ) ∧
        B.degree < (f.natDegree : WithBot ℕ) ∧
        (A ≠ 0 ∨ B ≠ 0) ∧ A * f + B * g = 0)

def RationalCounterexample : Prop :=
  ordinaryResultant (X ^ 2 + 1 : ℚ[X]) (X ^ 2 + 1) = 0 ∧
    ∀ x : ℚ, (X ^ 2 + 1 : ℚ[X]).eval x ≠ 0

end Specs.D07.Ch19.ResultantCommonRoot
