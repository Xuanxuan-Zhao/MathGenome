import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

open CategoryTheory HomotopicalAlgebra

universe v₁ v₂ u₁ u₂

namespace DerivedFormalization.Specs.QuillenAdjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [ModelCategory C] [ModelCategory D] {L : C ⥤ D} {U : D ⥤ C}

set_option linter.checkUnivs false in
/-- The Quillen predicate is defined on a given adjunction of model categories. -/
def isQuillenType :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [ModelCategory C] [ModelCategory D] {L : C ⥤ D} {U : D ⥤ C}, (L ⊣ U) → Prop

/-- The left adjoint preserves cofibrations and trivial cofibrations. -/
def isQuillenValue (_adj : L ⊣ U) : Prop :=
  (∀ ⦃A B : C⦄ (i : A ⟶ B), cofibrations C i → cofibrations D (L.map i)) ∧
  (∀ ⦃A B : C⦄ (i : A ⟶ B), (cofibrations C ⊓ weakEquivalences C) i →
    (cofibrations D ⊓ weakEquivalences D) (L.map i))

def iffRightType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [ModelCategory C] [ModelCategory D] {L : C ⥤ D} {U : D ⥤ C} (adj : L ⊣ U),
    isQuillenValue adj ↔
      (∀ ⦃X Y : D⦄ (p : X ⟶ Y), fibrations D p → fibrations C (U.map p)) ∧
      (∀ ⦃X Y : D⦄ (p : X ⟶ Y), (fibrations D ⊓ weakEquivalences D) p →
        (fibrations C ⊓ weakEquivalences C) (U.map p))

def cofibrantType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [ModelCategory C] [ModelCategory D] {L : C ⥤ D} {U : D ⥤ C} {adj : L ⊣ U},
    isQuillenValue adj → ∀ {X : C}, IsCofibrant X → IsCofibrant (L.obj X)

def fibrantType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [ModelCategory C] [ModelCategory D] {L : C ⥤ D} {U : D ⥤ C} {adj : L ⊣ U},
    isQuillenValue adj → ∀ {Y : D}, IsFibrant Y → IsFibrant (U.obj Y)

end DerivedFormalization.Specs.QuillenAdjunction
