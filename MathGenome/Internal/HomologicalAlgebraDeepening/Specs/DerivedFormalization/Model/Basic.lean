import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra

universe w v u

namespace DerivedFormalization

/-- The model categories of Q01 have all small limits and colimits and admit
functorial factorizations for both lifting pairs. All fields use the same
underlying model structure. -/
class FunctorialModelCategory (C : Type u) [Category.{v} C] where
  [toModelCategory : ModelCategory C]
  [hasLimits : HasLimits C]
  [hasColimits : HasColimits C]
  [cofibrationFactorization :
    HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [fibrationFactorization :
    HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

attribute [instance_reducible] FunctorialModelCategory.toModelCategory
attribute [instance] FunctorialModelCategory.toModelCategory FunctorialModelCategory.hasLimits
  FunctorialModelCategory.hasColimits FunctorialModelCategory.cofibrationFactorization
  FunctorialModelCategory.fibrationFactorization

namespace Specs.ModelBasic

set_option linter.checkUnivs false in
/-- Packaging an existing Mathlib model structure and the extra Q01 hypotheses. -/
def ofInstancesType :=
  ∀ (C : Type u) [Category.{v} C] [ModelCategory C] [HasLimits C] [HasColimits C]
    [HasFunctorialFactorization (cofibrations C) (fibrations C ⊓ weakEquivalences C)]
    [HasFunctorialFactorization (cofibrations C ⊓ weakEquivalences C) (fibrations C)],
    FunctorialModelCategory C

def ofInstancesValue : ofInstancesType.{v, u} :=
  fun C _ model limits colimits left right ↦
    @FunctorialModelCategory.mk C _ model limits colimits left right

def liftingType : Prop :=
  ∀ {C : Type u} [Category.{v} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y),
    HasLiftingProperty i p ↔
      ∀ (a : A ⟶ X) (b : B ⟶ Y), a ≫ p = i ≫ b →
        ∃ d : B ⟶ X, i ≫ d = a ∧ d ≫ p = b

def arrowRetractType : Prop :=
  ∀ {C : Type u} [Category.{v} C] {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y),
    Nonempty (RetractArrow f g) ↔
      ∃ (s₀ : A ⟶ X) (s₁ : B ⟶ Y) (r₀ : X ⟶ A) (r₁ : Y ⟶ B),
        s₀ ≫ g = f ≫ s₁ ∧ r₀ ≫ f = g ≫ r₁ ∧
          s₀ ≫ r₀ = 𝟙 A ∧ s₁ ≫ r₁ = 𝟙 B

def isomorphismsType : Prop :=
  ∀ (C : Type u) [Category.{v} C] [ModelCategory C],
    isomorphisms C ≤ weakEquivalences C ∧
      isomorphisms C ≤ cofibrations C ∧ isomorphisms C ≤ fibrations C

def cofibrantType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] (A : C),
    IsCofibrant A ↔ cofibrations C (initial.to A)

def fibrantType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [ModelCategory C] (A : C),
    IsFibrant A ↔ fibrations C (terminal.from A)

def liftingClassesType : Prop :=
  ∀ (C : Type u) [Category.{v} C] [ModelCategory C],
    (fibrations C ⊓ weakEquivalences C).llp = cofibrations C ∧
      (cofibrations C).rlp = fibrations C ⊓ weakEquivalences C ∧
      (fibrations C).llp = cofibrations C ⊓ weakEquivalences C ∧
      (cofibrations C ⊓ weakEquivalences C).rlp = fibrations C

/-- Pushouts, composition, arrow retracts and ordinal-indexed composites. -/
def LeftClassClosed {C : Type u} [Category.{v} C] (L : MorphismProperty C) : Prop :=
  L.IsStableUnderCobaseChange ∧ L.IsStableUnderComposition ∧
    L.IsStableUnderRetracts ∧ IsStableUnderTransfiniteComposition.{w} L

/-- Pullbacks, composition, arrow retracts and inverse transfinite composites.
The last condition uses well-ordered inverse systems, continuous by limits
at the limit stages, via transfinite composition in the opposite category. -/
def RightClassClosed {C : Type u} [Category.{v} C] (R : MorphismProperty C) : Prop :=
  R.IsStableUnderBaseChange ∧ R.IsStableUnderComposition ∧
    R.IsStableUnderRetracts ∧ IsStableUnderTransfiniteComposition.{w} R.op

def closureType : Prop :=
  ∀ (C : Type u) [Category.{v} C] [ModelCategory C],
    LeftClassClosed.{w} (cofibrations C) ∧
      RightClassClosed.{w} (fibrations C ⊓ weakEquivalences C) ∧
      LeftClassClosed.{w} (cofibrations C ⊓ weakEquivalences C) ∧
      RightClassClosed.{w} (fibrations C)

end Specs.ModelBasic
end DerivedFormalization
