import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ComponentBounds
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.SimpleObjects
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.TruncatedProjectives

/-! Projective covers in finite category O and their realization inside truncated projectives. -/

noncomputable section

open CategoryTheory
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient (quotientHighestVector)
open scoped Classical ModuleCat.Algebra

namespace Specs.RepTheorySurvey.CategoryO.ProjectiveCovers

open ComponentProjectors (Index component coset projection)
open ComponentBounds (centralCharacter_value inComponent_value simpleLabels_value)
open RepTheorySurvey.CategoryO.TruncatedProjectives (P generatorP)

universe u v

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]

/-- An epimorphism from a projective with superfluous kernel. Since the morphisms
of O are the underlying enveloping-linear maps, surjectivity gives the epimorphism
condition. -/
def projectiveCover_value {D : Setup g} (X : category_value.{u, v} D)
    {Y : ModuleCat.{v} (U g)} (p : X.obj →ₗ[U g] Y) : Prop :=
  Projective X ∧ Function.Surjective p ∧
    ∀ J : Submodule (U g) X.obj, J ⊔ p.ker = ⊤ → J = ⊤

set_option linter.checkUnivs false in
def ProjectiveCoverType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    {D : Setup g} (X : category_value.{u, v} D)
    {Y : ModuleCat.{v} (U g)}, (X.obj →ₗ[U g] Y) → Prop

/-- Indecomposability expressed by complementary enveloping submodules. -/
def IsIndecomposable (X : ModuleCat.{v} (U g)) : Prop :=
  (⊥ : Submodule (U g) X) ≠ ⊤ ∧
    ∀ A B : Submodule (U g) X, IsCompl A B → A = ⊥ ∨ B = ⊥

/-- The joint index of the simple of highest weight `μ`. -/
def simpleIndex (D : Setup g) (μ : D.Weight) : Index D :=
  (centralCharacter_value D μ, coset D μ)

/-- A bound as in LO03, for the labels and all the weights of all objects in the
same joint component. -/
def IsComponentBound (D : Setup g) (k : Index D) (Λ : D.Weight) : Prop :=
  coset D Λ = k.2 ∧
    (∀ μ ∈ simpleLabels_value D k, weightLE_value D μ Λ) ∧
    ∀ X : category_value.{u, u} D, inComponent_value D X.obj k →
      ∀ ν : D.Weight, weightSpace_value D.cartan X.obj ν ≠ ⊥ → weightLE_value D ν Λ

/-- The full subcategory of O belonging to one joint index. -/
def componentObjects (D : Setup g) (k : Index D) :
    ObjectProperty (category_value.{u, u} D) :=
  fun X => inComponent_value D X.obj k

/-- The actual projected truncated projective inside the ambient enveloping module. -/
abbrev projectedModule (D : Setup g) (k : Index D) (μ Λ : D.Weight) :=
  ModuleCat.of (U g) (component D (P D μ Λ) k)

/-- Projectivity both in the indicated component and in the entire category O. -/
def ProjectedProjectiveType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (k : Index D) (μ Λ : D.Weight),
    weightLE_value D μ Λ → IsComponentBound D k Λ →
    ∃ (hO : objects_value D (projectedModule D k μ Λ))
      (hK : inComponent_value D (projectedModule D k μ Λ) k),
      Projective (⟨projectedModule D k μ Λ, hO⟩ : category_value.{u, u} D) ∧
      Projective (⟨⟨projectedModule D k μ Λ, hO⟩, hK⟩ :
        (componentObjects D k).FullSubcategory)

/-- The cover is the restriction to an indecomposable direct summand of the
projected truncation. Its map comes from representing the canonical highest
vector of the actual simple quotient. -/
def ExistenceType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (μ : D.Weight),
    let k := simpleIndex D μ
    ∃ (Λ : D.Weight) (_ : IsComponentBound D k Λ)
      (_ : weightLE_value D μ Λ)
      (h : DirectSum.IsInternal (component D (P D μ Λ)))
      (p₀ : projectedModule D k μ Λ →ₗ[U g] simpleQuotient_value D μ)
      (S T : Submodule (U g) (projectedModule D k μ Λ))
      (hS : objects_value D (ModuleCat.of (U g) S)),
      p₀ (projection D h k (generatorP D μ Λ)) =
        quotientHighestVector D.cartan D.direction (character_value D μ) ∧
      Function.Surjective p₀ ∧
      IsCompl S T ∧ IsIndecomposable (ModuleCat.of (U g) S) ∧
      projectiveCover_value (⟨ModuleCat.of (U g) S, hS⟩ : category_value.{u, u} D)
        (p₀.domRestrict S)

/-- Every indecomposable projective of O mapping onto a simple is its cover. -/
def CoverOfIndecomposableType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X Y : category_value.{u, v} D) (p : X.obj →ₗ[U g] Y.obj),
    Projective X → IsIndecomposable X.obj → Simple Y → Function.Surjective p →
    projectiveCover_value X p

/-- The kernel of a cover of a simple is its unique maximal proper submodule. -/
def UniqueMaximalSubmoduleType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X Y : category_value.{u, v} D) (p : X.obj →ₗ[U g] Y.obj),
    Simple Y → projectiveCover_value X p →
    IsCoatom p.ker ∧ ∀ J : Submodule (U g) X.obj, IsCoatom J → J = p.ker

/-- Any two covers of the same object are isomorphic over that object. -/
def UniquenessType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X X' Y : category_value.{u, v} D)
    (p : X.obj →ₗ[U g] Y.obj) (p' : X'.obj →ₗ[U g] Y.obj),
    projectiveCover_value X p → projectiveCover_value X' p' →
    ∃ e : X.obj ≃ₗ[U g] X'.obj, p'.comp e.toLinearMap = p

end Specs.RepTheorySurvey.CategoryO.ProjectiveCovers
