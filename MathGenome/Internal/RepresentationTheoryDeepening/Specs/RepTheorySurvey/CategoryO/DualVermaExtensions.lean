import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.RestrictedDual
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The Hom dimension and Yoneda Ext¹ assertions for Verma and dual Verma modules. -/

open CategoryTheory
open scoped Classical ModuleCat.Algebra
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)

namespace Specs.RepTheorySurvey.CategoryO.DualVermaExtensions

universe u v

/-- The Hom space from a Verma to a dual Verma in the full subcategory O is
finite-dimensional, with the indicated dimension. -/
def HomDimensionType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (nu lam : D.Weight),
    let H := verma_value D nu ⟶ RestrictedDual.costandard_value D lam
    FiniteDimensional ℂ H ∧ Module.finrank ℂ H = (if nu = lam then 1 else 0)

/-- Every short exact sequence in O with these endpoints admits an enveloping-linear
section of its quotient map. Linear maps also allow the middle object's carrier to
lie in another universe. -/
def ExtensionSplittingType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (nu lam : D.Weight) (X : category_value.{u,v} D)
    (i : RestrictedDual.costandard_value D lam →ₗ[U g] X.obj)
    (p : X.obj →ₗ[U g] verma_value D nu),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    ∃ s : verma_value D nu →ₗ[U g] X.obj, p.comp s = LinearMap.id

end Specs.RepTheorySurvey.CategoryO.DualVermaExtensions
