import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.Forms
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The representation-theoretic part of Gabriel's theorem for a positive
definite Tits form. -/

open CategoryTheory

universe u v w d

namespace RepTheorySurvey.Quiver.IndecomposableVectorsSpec

open FormsSpec

/-- Nonnegative integral vectors of Tits value one. -/
abbrev PositiveTitsVector (Q : Type u) [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)] :=
  {x : DimensionVector Q // (∀ i, 0 ≤ x i) ∧ titsForm x = 1}

/-- The vertex finranks give the bijection on isomorphism classes. -/
abbrev DimensionVectorBijection : Prop :=
  ∀ (k : Type w) (Q : Type u) [Field k] [IsAlgClosed k] [Quiver.{v} Q]
    [Fintype Q] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q → PositiveDefinite Q →
    ∃ e : IndecomposableClass.{u, v, w, max w d} k Q ≃ PositiveTitsVector Q,
      ∀ V : IndecomposableRepresentation.{u, v, w, max w d} k Q,
        (e (Quotient.mk _ V)).val = dimensionVector V.val

/-- Each indecomposable has the ground field as its endomorphism algebra. -/
abbrev EndomorphismAlgebra : Prop :=
  ∀ (k : Type w) (Q : Type u) [Field k] [IsAlgClosed k] [Quiver.{v} Q]
    [Fintype Q] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q → PositiveDefinite Q →
    ∀ V : IndecomposableRepresentation.{u, v, w, max w d} k Q,
      Nonempty (End V.val.obj ≃ₐ[k] k)

end RepTheorySurvey.Quiver.IndecomposableVectorsSpec
