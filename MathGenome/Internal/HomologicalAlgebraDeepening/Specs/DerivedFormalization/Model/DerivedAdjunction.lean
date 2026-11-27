import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Localization
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.QuillenAdjunction

open CategoryTheory HomotopicalAlgebra

universe v₁ v₂ u₁ u₂

namespace DerivedFormalization.Model

open Specs.ModelLocalization Specs.QuillenAdjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [FunctorialModelCategory C] [FunctorialModelCategory D]
  {L : C ⥤ D} {U : D ⥤ C}

/-- The derived adjunction with its comparisons to the replacement composites.
The representative law uses the ordinary adjunction on `L(QX) ⟶ RY`. -/
structure DerivedAdjunctionData (adj : L ⊣ U) (c : Replacement C) (d : Replacement D) where
  left : homotopyCategoryValue C ⥤ homotopyCategoryValue D
  right : homotopyCategoryValue D ⥤ homotopyCategoryValue C
  leftComparison : localizationFunctorValue c ⋙ left ≅ (c.Q ⋙ L) ⋙ localizationFunctorValue d
  rightComparison : localizationFunctorValue d ⋙ right ≅ (d.R ⋙ U) ⋙ localizationFunctorValue c
  adjunction : left ⊣ right
  homEquiv_representative (X : C) (Y : D) (f : L.obj (c.Q.obj X) ⟶ d.R.obj Y)
      (k : left.obj ((localizationFunctorValue c).obj X) ⟶ (localizationFunctorValue d).obj Y)
      (hk : k ≫ (localizationFunctorValue d).map (d.i.app Y) =
        leftComparison.hom.app X ≫ (localizationFunctorValue d).map f) :
      (localizationFunctorValue c).map (c.p.app X) ≫
        adjunction.homEquiv ((localizationFunctorValue c).obj X)
          ((localizationFunctorValue d).obj Y) k ≫ rightComparison.hom.app Y =
        (localizationFunctorValue c).map (adj.homEquiv (c.Q.obj X) (d.R.obj Y) f)

end DerivedFormalization.Model

namespace DerivedFormalization.Specs.ModelDerivedAdjunction

open Model ModelLocalization QuillenAdjunction ModelHomotopy

def leftCompositeType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [ModelCategory C] [ModelCategory D] {L : C ⥤ D} {U : D ⥤ C}
    {adj : L ⊣ U}, isQuillenValue adj → ∀ (c : Replacement C) {X X' : C}
    (f : X ⟶ X'), weakEquivalences C f → weakEquivalences D (L.map (c.Q.map f))

def rightCompositeType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [ModelCategory C] [ModelCategory D] {L : C ⥤ D} {U : D ⥤ C}
    {adj : L ⊣ U}, isQuillenValue adj → ∀ (d : Replacement D) {Y Y' : D}
    (f : Y ⟶ Y'), weakEquivalences D f → weakEquivalences C (U.map (d.R.map f))

def homotopyType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [ModelCategory C] [ModelCategory D] {L : C ⥤ D} {U : D ⥤ C}
    {adj : L ⊣ U}, isQuillenValue adj → ∀ {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y]
    (f g : L.obj X ⟶ Y),
    leftHomotopicValue f g ↔ leftHomotopicValue (adj.homEquiv X Y f) (adj.homEquiv X Y g)

def derivedAdjunctionType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [FunctorialModelCategory C] [FunctorialModelCategory D] {L : C ⥤ D} {U : D ⥤ C}
    {adj : L ⊣ U}, isQuillenValue adj → ∀ (c : Replacement C) (d : Replacement D),
    Nonempty (DerivedAdjunctionData adj c d)

def leftMapType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [FunctorialModelCategory C] [FunctorialModelCategory D] {L : C ⥤ D} {U : D ⥤ C}
    {adj : L ⊣ U} {c : Replacement C} {d : Replacement D}
    (a : DerivedAdjunctionData adj c d) {X X' : C} (f : X ⟶ X'),
    a.left.map ((localizationFunctorValue c).map f) =
      a.leftComparison.hom.app X ≫ (localizationFunctorValue d).map (L.map (c.Q.map f)) ≫
        a.leftComparison.inv.app X'

def rightMapType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [FunctorialModelCategory C] [FunctorialModelCategory D] {L : C ⥤ D} {U : D ⥤ C}
    {adj : L ⊣ U} {c : Replacement C} {d : Replacement D}
    (a : DerivedAdjunctionData adj c d) {Y Y' : D} (f : Y ⟶ Y'),
    a.right.map ((localizationFunctorValue d).map f) =
      a.rightComparison.hom.app Y ≫ (localizationFunctorValue c).map (U.map (d.R.map f)) ≫
        a.rightComparison.inv.app Y'

def cofibrantComparisonIsoType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [FunctorialModelCategory C] [FunctorialModelCategory D] {L : C ⥤ D} {U : D ⥤ C}
    {adj : L ⊣ U} {c : Replacement C} {d : Replacement D}
    (a : DerivedAdjunctionData adj c d), isQuillenValue adj → ∀ (X : C) [IsCofibrant X],
    IsIso (a.leftComparison.hom.app X ≫ (localizationFunctorValue d).map (L.map (c.p.app X)))

def fibrantComparisonIsoType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [FunctorialModelCategory C] [FunctorialModelCategory D] {L : C ⥤ D} {U : D ⥤ C}
    {adj : L ⊣ U} {c : Replacement C} {d : Replacement D}
    (a : DerivedAdjunctionData adj c d), isQuillenValue adj → ∀ (Y : D) [IsFibrant Y],
    IsIso ((localizationFunctorValue c).map (U.map (d.i.app Y)) ≫ a.rightComparison.inv.app Y)

def unitType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [FunctorialModelCategory C] [FunctorialModelCategory D] {L : C ⥤ D} {U : D ⥤ C}
    {adj : L ⊣ U} {c : Replacement C} {d : Replacement D}
    (a : DerivedAdjunctionData adj c d) (X : C) [IsCofibrant X],
    a.adjunction.unit.app ((localizationFunctorValue c).obj X) ≫
        a.right.map (a.leftComparison.hom.app X ≫
          (localizationFunctorValue d).map (L.map (c.p.app X))) ≫
        a.rightComparison.hom.app (L.obj X) =
      (localizationFunctorValue c).map (adj.homEquiv X (d.R.obj (L.obj X)) (d.i.app (L.obj X)))

def counitType : Prop :=
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [FunctorialModelCategory C] [FunctorialModelCategory D] {L : C ⥤ D} {U : D ⥤ C}
    {adj : L ⊣ U} {c : Replacement C} {d : Replacement D}
    (a : DerivedAdjunctionData adj c d) (Y : D) [IsFibrant Y],
    a.left.map ((localizationFunctorValue c).map (U.map (d.i.app Y)) ≫
        a.rightComparison.inv.app Y) ≫ a.adjunction.counit.app ((localizationFunctorValue d).obj Y) =
      a.leftComparison.hom.app (U.obj Y) ≫
        (localizationFunctorValue d).map
          ((adj.homEquiv (c.Q.obj (U.obj Y)) Y).symm (c.p.app (U.obj Y)))

end DerivedFormalization.Specs.ModelDerivedAdjunction
