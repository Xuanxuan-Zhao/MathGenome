import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.DynkinClassification
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.EulerExt
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.PositiveRoots
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Gabriel's theorem for finite acyclic quivers. -/

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

universe u v w d

namespace RepTheorySurvey.Quiver.GabrielSpec

open FormsSpec DynkinClassificationSpec PositiveRootsSpec PathResolutionSpec
open scoped EulerExtSpec

/-- Finite representation type is equivalent to Dynkin type. For a Dynkin
quiver, the dimension vector classifies the indecomposables by the positive
roots, and every indecomposable has scalar endomorphisms and vanishing
derived self-extensions in degree one. -/
abbrev GabrielsTheorem : Prop :=
  ∀ (k : Type w) (Q : Type u) [Field k] [IsAlgClosed k] [Quiver.{v} Q]
    [Fintype Q] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q →
    (FiniteRepresentationType.{u, v, w, max w d} k Q ↔ hasDynkinComponents Q) ∧
    (hasDynkinComponents Q →
      positiveRoots Q = {x : DimensionVector Q | (∀ i, 0 ≤ x i) ∧ titsForm x = 1} ∧
      (∃ e : IndecomposableClass.{u, v, w, max w d} k Q ≃ ↥(positiveRoots Q),
        ∀ V : IndecomposableRepresentation.{u, v, w, max w d} k Q,
          (e (Quotient.mk _ V)).val = dimensionVector V.val) ∧
      ∀ V : IndecomposableRepresentation.{u, v, w, max w d} k Q,
        Nonempty (End (Target V.val.obj) ≃ₐ[k] k) ∧
        Module.Finite k
          (Ext.{max u v w (max w d + 1)} (Target V.val.obj) (Target V.val.obj) 1) ∧
        Subsingleton (Ext.{max u v w (max w d + 1)} (Target V.val.obj) (Target V.val.obj) 1))

end RepTheorySurvey.Quiver.GabrielSpec
