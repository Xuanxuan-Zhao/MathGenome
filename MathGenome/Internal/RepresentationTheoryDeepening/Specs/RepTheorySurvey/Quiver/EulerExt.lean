import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.PathResolution
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! The Hom and derived Ext assertions of the two-term projective resolution. -/

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra TensorProduct

universe u v w d

namespace RepTheorySurvey.Quiver.EulerExtSpec

open RM03 PathResolutionSpec

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]

local notation "A" => PathAlgebra k Q

/-- Use the derived category of the original module category, in a universe
large enough even when the scalar and module universes are independent. -/
scoped instance : HasExt.{max u v w (d + 1)} (ModuleCat.{d} A) :=
  HasExt.standard _

/-- The Hom and Ext spaces and their Euler dimension over the ground field. -/
abbrev HomExtFormula (V W : FormsSpec.FiniteRepresentation.{u, v, w, d} k Q)
    [Fintype (Arrow Q)] : Prop :=
  Module.Finite k (Target V.obj ⟶ Target W.obj) ∧
  Module.Finite k (Ext.{max u v w (d + 1)} (Target V.obj) (Target W.obj) 1) ∧
  (Module.finrank k (Target V.obj ⟶ Target W.obj) : ℤ) -
      (Module.finrank k (Ext.{max u v w (d + 1)} (Target V.obj) (Target W.obj) 1) : ℤ) =
    FormsSpec.eulerForm (FormsSpec.dimensionVector V) (FormsSpec.dimensionVector W)

/-- Vanishing of the actual derived Ext groups in every degree at least two. -/
abbrev HigherExtVanishing (V W : FormsSpec.FiniteRepresentation.{u, v, w, d} k Q) : Prop :=
  ∀ n : ℕ, 2 ≤ n → Subsingleton (Ext.{max u v w (d + 1)} (Target V.obj) (Target W.obj) n)

/-- Evaluation at the source vertex idempotent on a projective tensor summand. -/
abbrev EvaluationAtVertex : Prop :=
  ∀ (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
    (V W : QuiverRepresentation.{u, v, w, d} k Q) (i j : Q),
    ∃ e : (VertexProjective k i ⊗[k] V.vertex j →ₗ[PathAlgebra k Q] Target W) ≃ₗ[k]
        (V.vertex j →ₗ[k] W.vertex i),
      ∀ f x, e f x = PathOperators.projection W i
        (QuiverModuleEquivalence.coordinates W (f (pathVector Quiver.Path.nil ⊗ₜ[k] x)))

/-- The explicit projective resolution, followed by its Euler and vanishing
consequences for all finite-dimensional representations. -/
abbrev TwoTermProjectiveResolution : Prop :=
  ∀ (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
    [Fintype (Arrow Q)], ¬ HasOrientedCycle Q →
      ∀ V : FormsSpec.FiniteRepresentation.{u, v, w, d} k Q,
        Nonempty (Resolution V.obj) ∧
        ∀ W : FormsSpec.FiniteRepresentation.{u, v, w, d} k Q,
          HomExtFormula V W ∧ HigherExtVanishing V W

end RepTheorySurvey.Quiver.EulerExtSpec
