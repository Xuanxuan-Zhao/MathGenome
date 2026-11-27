import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant

open CategoryTheory HomotopicalAlgebra

universe v₁ u₁ v₂ u₂

namespace DerivedFormalization.Specs.ModelBrown

/-- Brown's lemma for a functor on the full subcategory of cofibrant objects. -/
def cofibrantType : Prop :=
  ∀ {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] (W : MorphismProperty D) [W.HasTwoOutOfThreeProperty]
    (F : CofibrantObject C ⥤ D),
    (∀ ⦃X Y : CofibrantObject C⦄ (f : X ⟶ Y),
      trivialCofibrations C (CofibrantObject.ι.map f) → W (F.map f)) →
    ∀ ⦃X Y : CofibrantObject C⦄ (f : X ⟶ Y),
      weakEquivalences C (CofibrantObject.ι.map f) → W (F.map f)

/-- Brown's lemma for a functor on the full subcategory of fibrant objects. -/
def fibrantType : Prop :=
  ∀ {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] (W : MorphismProperty D) [W.HasTwoOutOfThreeProperty]
    (F : FibrantObject C ⥤ D),
    (∀ ⦃X Y : FibrantObject C⦄ (f : X ⟶ Y),
      trivialFibrations C (FibrantObject.ι.map f) → W (F.map f)) →
    ∀ ⦃X Y : FibrantObject C⦄ (f : X ⟶ Y),
      weakEquivalences C (FibrantObject.ι.map f) → W (F.map f)

end DerivedFormalization.Specs.ModelBrown
