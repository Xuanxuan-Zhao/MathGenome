import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.DerivedAdjunction

open CategoryTheory HomotopicalAlgebra

universe v₁ v₂ u₁ u₂

namespace DerivedFormalization.Specs.ModelQuillenEquivalence

open Model QuillenAdjunction

/-- The derived adjunction is an equivalence exactly when ordinary adjunction
preserves and reflects weak equivalences on maps from the left adjoint of a
cofibrant object to a fibrant object. -/
def criterionType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [FunctorialModelCategory C] [FunctorialModelCategory D]
    {L : C ⥤ D} {U : D ⥤ C} {adj : L ⊣ U}
    {c : Replacement C} {d : Replacement D}, isQuillenValue adj →
    ∀ (a : DerivedAdjunctionData adj c d),
      a.left.IsEquivalence ↔
        ∀ (X : C) (Y : D) [IsCofibrant X] [IsFibrant Y] (f : L.obj X ⟶ Y),
          weakEquivalences D f ↔ weakEquivalences C (adj.homEquiv X Y f)

end DerivedFormalization.Specs.ModelQuillenEquivalence
