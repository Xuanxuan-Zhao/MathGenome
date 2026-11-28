import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.Category
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.BorelInduction

/-! Weight bounds for the finite category O. -/

noncomputable section

open CategoryTheory Module
open Specs.LieAlgebrasAndRepresentations.VermaModules (U highestVector_value)
open scoped ModuleCat.Algebra

namespace Specs.RepTheorySurvey.CategoryO.WeightBounds

open _root_.RepTheorySurvey.CategoryO.BorelInduction (inclusion restrictModule Induced induceTensor)

universe u v

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable (D : Setup g)

/-- The ordinary Cartan weights with a nonzero weight space. -/
def support (X : ModuleCat.{v} (U g)) : Set D.Weight :=
  {μ | weightSpace_value D.cartan X μ ≠ ⊥}

/-- A finite family of upper bounds for the weight support, and finite multiplicities. -/
def HasWeightBounds (X : ModuleCat.{v} (U g)) : Prop :=
  (∀ μ, FiniteDimensional ℂ (weightSpace_value D.cartan X μ)) ∧
  ∃ s : Finset D.Weight, ∀ μ ∈ support D X, ∃ lam ∈ s, weightLE_value D μ lam

def BoundsType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : ModuleCat.{v} (U g)), objects_value D X → HasWeightBounds D X

def FiniteUpwardType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (s : Finset D.Weight) (ν : D.Weight),
    {μ | weightLE_value D ν μ ∧ ∃ lam ∈ s, weightLE_value D μ lam}.Finite

/-- Restrict the enveloping action to the chosen Borel. -/
abbrev restrictedBorelAction (X : ModuleCat.{v} (U g)) : Module (U D.borel) X :=
  restrictModule (inclusion D.borel) X

abbrev restrictedBorelTower (X : ModuleCat.{v} (U g)) :
    letI := restrictedBorelAction D X
    IsScalarTower ℂ (U D.borel) X := by
  let := restrictedBorelAction D X
  apply IsScalarTower.of_algebraMap_smul
  intro c x
  change (inclusion D.borel) (algebraMap ℂ (U D.borel) c) • x = algebraMap ℂ (U g) c • x
  rw [AlgHom.commutes]

/-- The finite-dimensional inducing submodule, with its action restricted from the target. -/
def GeneratingBorelModuleType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : ModuleCat.{v} (U g)), objects_value D X →
    letI := restrictedBorelAction D X
    letI := restrictedBorelTower D X
    ∃ (n : ℕ) (x : Fin n → X) (μ : Fin n → D.Weight)
      (E : Submodule (U D.borel) X),
      (∀ j, x j ∈ weightSpace_value D.cartan X (μ j)) ∧
      Submodule.span (U g) (Set.range x) = ⊤ ∧
      E.restrictScalars ℂ = ⨆ j, orbit_value D.nPlus X (x j) ∧
      FiniteDimensional ℂ E ∧
      (∃ (m : ℕ) (b : Basis (Fin m) ℂ E) (η : Fin m → D.Weight),
        ∀ j, (b j : X) ∈ weightSpace_value D.cartan X (η j)) ∧
      (∃ q : Induced (inclusion D.borel) E →ₗ[U g] X,
        Function.Surjective q ∧
        ∀ a e, q (induceTensor (inclusion D.borel) a e) = a • (e : X))

def InducedBoundsType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (X : ModuleCat.{v} (U g)),
    letI := restrictedBorelAction D X
    letI := restrictedBorelTower D X
    ∀ (E : Submodule (U D.borel) X) {m : ℕ}
      (b : Basis (Fin m) ℂ E) (η : Fin m → D.Weight),
      (∀ j, (b j : X) ∈ weightSpace_value D.cartan X (η j)) →
      HasWeightBounds D (ModuleCat.of (U g) (Induced (inclusion D.borel) E))

def VermaType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (lam : D.Weight),
    let X := verma_value D lam
    let w : X := highestVector_value D.cartan D.direction (character_value D lam)
    objects_value D X ∧
    w ≠ 0 ∧ Submodule.span (U g) {w} = ⊤ ∧
    (∀ μ, FiniteDimensional ℂ (weightSpace_value D.cartan X μ)) ∧
    (∀ μ, μ ∈ support D X ↔ weightLE_value D μ lam) ∧
    weightSpace_value D.cartan X lam = ℂ ∙ w

end Specs.RepTheorySurvey.CategoryO.WeightBounds
