import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.Category
import Mathlib.CategoryTheory.Simple

/-! The simple objects of the finite category O (the simple-object assertion of LO02). -/

noncomputable section

open CategoryTheory UniversalEnvelopingAlgebra
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient (quotientHighestVector)
open scoped ModuleCat.Algebra

namespace Specs.RepTheorySurvey.CategoryO.SimpleObjects

universe u v

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]

/-- A nonzero Cartan weight vector annihilated by the positive part and generating
the module under the enveloping action. -/
def IsHighestWeightGenerator (D : Setup g) (lam : D.Weight) (X : ModuleCat.{v} (U g))
    (x : X) : Prop :=
  x ≠ 0 ∧ x ∈ weightSpace_value D.cartan X lam ∧
    (∀ z : D.nPlus, (ι ℂ (z : g)) • x = 0) ∧
    Submodule.span (U g) {x} = ⊤

/-- Categorical simplicity in O agrees with simplicity over the enveloping algebra. -/
def SimpleIffIsSimpleModuleType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : category_value.{u, v} D),
    Simple X ↔ IsSimpleModule (U g) X.obj

/-- The pinned simple quotient belongs to O, is simple there, and has its
canonical highest-weight generator of weight `lam`. -/
def SimpleQuotientInOType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (lam : D.Weight),
    ∃ h : objects_value D (simpleQuotient_value D lam),
      Simple (⟨simpleQuotient_value D lam, h⟩ : category_value.{u, u} D) ∧
      IsHighestWeightGenerator D lam (simpleQuotient_value D lam)
        (quotientHighestVector D.cartan D.direction (character_value D lam))

/-- Isomorphic pinned simple quotients have equal labels. -/
def SimpleQuotientEquivIffType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (lam mu : D.Weight),
    Nonempty (simpleQuotient_value D lam ≃ₗ[U g] simpleQuotient_value D mu) ↔ lam = mu

/-- The simple objects are precisely the modules isomorphic to a uniquely
labeled simple quotient. Enveloping-linear equivalences express isomorphism
also when the module carriers are in different universes. -/
def ClassificationType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : category_value.{u, v} D),
    Simple X ↔ ∃! lam : D.Weight, Nonempty (X.obj ≃ₗ[U g] simpleQuotient_value D lam)

end Specs.RepTheorySurvey.CategoryO.SimpleObjects
