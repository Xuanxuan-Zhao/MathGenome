import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ComponentProjectors
import Mathlib.CategoryTheory.Simple
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CentralCharacters

/-! Simple labels and a common weight bound in each component of finite category O. -/

noncomputable section

open CategoryTheory
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights (weightWeylGroup)
open Specs.LieAlgebrasAndRepresentations.HarishChandraIsomorphism (rhoValue)
open scoped ModuleCat.Algebra

namespace Specs.RepTheorySurvey.CategoryO.ComponentBounds

open ComponentProjectors (Center CentralCharacter Index component coset)

universe u v

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]

/-- The central character is selected by the scalar action on the pinned Verma
module. Its existence and its agreement with the shifted Weyl action are proved
in `CentralCharacterSpecType`. -/
def centralCharacter_value (D : Setup g) (μ : D.Weight) : CentralCharacter g :=
  letI : Nonempty (CentralCharacter g) :=
    ⟨(_root_.Shared.Lie.augmentation ℂ g).comp (Center g).val⟩
  Classical.epsilon fun χ : CentralCharacter g =>
    ∀ (z : Center g) (x : verma_value D μ), z.val • x = χ z • x

/-- The joint component contains the whole module. -/
def inComponent_value (D : Setup g) (X : ModuleCat.{v} (U g)) (k : Index D) : Prop :=
  component D X k = ⊤

/-- The labels with the given central character and root-lattice coset. -/
def simpleLabels_value (D : Setup g) (k : Index D) : Set D.Weight :=
  {μ | centralCharacter_value D μ = k.1 ∧ coset D μ = k.2}

def CentralCharacterType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g), D.Weight → CentralCharacter g

set_option linter.checkUnivs false in
def InComponentType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g), ModuleCat.{v} (U g) → Index D → Prop

def SimpleLabelsType :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g), Index D → Set D.Weight

/-- The chosen character gives the scalar action on both highest-weight modules.
Character equality is equality of shifted Weyl orbits. -/
def CentralCharacterSpecType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g] (D : Setup g),
    (∀ (μ : D.Weight) (z : Center g),
      (∀ x : verma_value D μ, z.val • x = centralCharacter_value D μ z • x) ∧
      (∀ x : simpleQuotient_value D μ, z.val • x = centralCharacter_value D μ z • x)) ∧
    ∀ μ ν : D.Weight, centralCharacter_value D μ = centralCharacter_value D ν ↔
      ∃ w : weightWeylGroup D.cartan,
        ν + rhoValue D.cartan D.direction = w.val (μ + rhoValue D.cartan D.direction)

/-- The pinned simple quotient belongs to its indexed component exactly when
its highest weight belongs to the label set. -/
def SimpleQuotientMemComponentType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (k : Index D) (μ : D.Weight),
    inComponent_value D (simpleQuotient_value D μ) k ↔ μ ∈ simpleLabels_value D k

/-- The simple objects in the component are exactly the uniquely labeled
simple quotients, up to enveloping-linear isomorphism. -/
def SimpleClassificationType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (k : Index D) (X : category_value.{u, v} D),
    (Simple X ∧ inComponent_value D X.obj k) ↔
      ∃! μ : D.Weight, μ ∈ simpleLabels_value D k ∧
        Nonempty (X.obj ≃ₗ[U g] simpleQuotient_value D μ)

def FiniteSimpleLabelsType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (k : Index D), (simpleLabels_value D k).Finite

/-- One weight in the coset bounds every simple label and every weight of
every object of the component. This also applies when the label set is empty. -/
def CommonUpperBoundType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (k : Index D),
    ∃ Λ : D.Weight, coset D Λ = k.2 ∧
      (∀ μ ∈ simpleLabels_value D k, weightLE_value D μ Λ) ∧
      ∀ X : category_value.{u, v} D, inComponent_value D X.obj k →
        ∀ ν : D.Weight, weightSpace_value D.cartan X.obj ν ≠ ⊥ → weightLE_value D ν Λ

end Specs.RepTheorySurvey.CategoryO.ComponentBounds
