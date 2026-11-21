import MathGenome.Internal.Specs.D07.Ch12.RelativeAlgebraicClosure
import Mathlib.Algebra.Order.Field.Rat

/-!
Algebraic elements form an intermediate field and the largest algebraic
intermediate extension (K07.12.relative_algebraic_closure).

Mathlib constructs the canonical relative closure by upgrading the integral
closure to an intermediate field. Over the base field, integral and algebraic
elements coincide. Its carrier theorem supplies precisely the nonzero
annihilator predicate; its universal property gives containment of every
algebraic intermediate extension. No assumption is imposed on the ambient
extension's degree or algebraicity.
-/

universe u v

namespace D07.Ch12.RelativeAlgebraicClosure

open Specs.D07.Ch12.RelativeAlgebraicClosure

noncomputable abbrev relativeAlgebraicClosure : RelativeClosureType.{u, v} :=
  fun K L _ _ _ => algebraicClosure K L

theorem mem_relativeAlgebraicClosure_iff : Membership.{u, v} := by
  intro K L _ _ _ x
  exact mem_algebraicClosure_iff

theorem relative_algebraic_closure_is_algebraic : AlgebraicExtension.{u, v} := by
  intro K L _ _ _
  infer_instance

theorem largest_algebraic_intermediate_field :
    LargestAlgebraicIntermediateField.{u, v} := by
  intro K L _ _ _
  refine ⟨relative_algebraic_closure_is_algebraic K L, ?_⟩
  intro E hE
  exact (le_algebraicClosure_iff K L E).mpr hE

theorem algebraic_elements_form_field : AlgebraicElementsFormField.{u, v} := by
  intro K L _ _ _
  exact ⟨algebraicClosure K L, mem_relativeAlgebraicClosure_iff K L,
    largest_algebraic_intermediate_field K L⟩

theorem rational_relative_closure : RationalRelativeClosure := by
  apply top_unique
  intro x _
  exact mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (x : ℚ))

/-- An algebraically closed field would contain a square root of -1.
Its image in Q contradicts nonnegativity of rational squares. -/
theorem rational_relative_closure_not_algClosed :
    RationalRelativeClosureNotAlgClosed := by
  intro h
  let : IsAlgClosed (algebraicClosure ℚ ℚ) := h
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-1 : algebraicClosure ℚ ℚ) zero_lt_two
  have hz' := congrArg (fun x : algebraicClosure ℚ ℚ => (x : ℚ)) hz
  change (z : ℚ) ^ 2 = -1 at hz'
  have hn : (0 : ℚ) ≤ -1 := hz' ▸ sq_nonneg (z : ℚ)
  exact (not_le_of_gt (neg_lt_zero.mpr (zero_lt_one : (0 : ℚ) < 1))) hn

end D07.Ch12.RelativeAlgebraicClosure
