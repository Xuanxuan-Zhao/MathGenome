import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! HA-R10, source lines 2041–2057. Exact means additive and preserving finite
limits and colimits. The unbounded assertions have no resolution hypotheses.
The bounded identifications use the comparison-inclusive HA-R05 interfaces. -/
set_option linter.checkUnivs false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty

namespace Specs.AdvancedHomologicalAlgebra.ExactFunctorLocalization

section
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

def descendedType := _root_.DerivedCategory A ⥤ _root_.DerivedCategory B
noncomputable abbrev descendedValue : descendedType (A := A) (B := B) := F.mapDerivedCategory

def factorsType := _root_.DerivedCategory.Qh ⋙ descendedValue F ≅
  F.mapHomotopyCategory (.up ℤ) ⋙ _root_.DerivedCategory.Qh
noncomputable def factorsValue : factorsType F := F.mapDerivedCategoryFactorsh

def exactType : Prop := (descendedValue F).Additive ∧ (descendedValue F).IsTriangulated

def cohomologyType : Prop := ∀ n : ℤ, Nonempty
  (descendedValue F ⋙ _root_.DerivedCategory.homologyFunctor B n ≅
    _root_.DerivedCategory.homologyFunctor A n ⋙ F)

/-- Both bounded restrictions, with their invertible comparisons. The comparison
universal properties quantify over all functors, as in HA-R05. The unique
identifications explicitly preserve the unit or counit of any given RF or LF. -/
structure BoundedDescent where
  right : RightData (_root_.DerivedCategory.Plus.Qh (C := A)) (plusUValue F)
  rightRestriction : right.functor ⋙ _root_.DerivedCategory.Plus.ι ≅
    _root_.DerivedCategory.Plus.ι ⋙ descendedValue F
  rightShift : right.functor.CommShift ℤ
  rightExact : letI := rightShift; right.functor.IsTriangulated
  rightCompatibility : ∀ X : HomotopyCategory.Plus A,
    _root_.DerivedCategory.Plus.ι.map (right.unit.app X) ≫
      rightRestriction.hom.app (_root_.DerivedCategory.Plus.Qh.obj X) =
        F.mapDerivedCategoryFactorsh.inv.app X.obj
  rightComparison : IsIso right.unit
  rightIdentification : ∀ R : rightDerivedDataValue.{u, v, u', v', w, w'} F,
    ∃! e : R.functor ≅ right.functor,
      R.unit ≫ whiskerLeft _root_.DerivedCategory.Plus.Qh e.hom = right.unit
  left : LeftData (QMinus A) (minusUValue F)
  leftRestriction : left.functor ⋙ _root_.DerivedCategory.Minus.ι ≅
    _root_.DerivedCategory.Minus.ι ⋙ descendedValue F
  leftShift : left.functor.CommShift ℤ
  leftExact : letI := leftShift; left.functor.IsTriangulated
  leftCompatibility : ∀ X : KMinus A,
    leftRestriction.inv.app ((QMinus A).obj X) ≫
      _root_.DerivedCategory.Minus.ι.map (left.counit.app X) =
        F.mapDerivedCategoryFactorsh.hom.app X.obj
  leftComparison : IsIso left.counit
  leftIdentification : ∀ R : leftDerivedDataValue.{u, v, u', v', w, w'} F,
    ∃! e : R.functor ≅ left.functor,
      whiskerLeft (QMinus A) e.hom ≫ left.counit = R.counit

def boundedType : Prop := Nonempty (BoundedDescent F)
end


/-- Closed types for the public declarations. -/
def descendedDeclarationType := ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F],
  descendedType (A := A) (B := B)
noncomputable def descendedDeclarationValue : descendedDeclarationType :=
  by
    intro A B _ _ _ _ _ _ F _ _ _
    exact descendedValue F

def factorsDeclarationType := ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F],
  factorsType F
noncomputable def factorsDeclarationValue : factorsDeclarationType :=
  by
    intro A B _ _ _ _ _ _ F _ _ _
    exact factorsValue F

def exactDeclarationType : Prop := ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F],
  exactType F

def cohomologyDeclarationType : Prop := ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F],
  cohomologyType F

def boundedDeclarationType : Prop := ∀ {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F],
  boundedType F

end Specs.AdvancedHomologicalAlgebra.ExactFunctorLocalization
