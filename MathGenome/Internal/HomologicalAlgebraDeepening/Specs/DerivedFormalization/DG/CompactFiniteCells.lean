import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CompactRepresentables
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedCoefficientLift
import Mathlib.CategoryTheory.Retract

open CategoryTheory
open _root_.DerivedFormalization

universe u v w j t s z

namespace Specs.DerivedFormalization.DG.CompactFiniteCells

open AmbientDerived (category strictInput)
open CoefficientLift (liftCategory liftFunctor)
open CompactRepresentables (IsCompact LocalizationMapAdditive)
open Derived (HomotopyCategoryLaws derivedCategory quotient)
open DerivedCoefficientLift (Descent strictTransition)
open DerivedKProjective (derivedCategoryInstance)

noncomputable section

variable {k : Type u} [CommRing k]
variable {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,z,w} k}

/-- A retract in the fixed localization, with its finite-cell model over
the original category of the specified strict input. -/
def IsFiniteCellRetract (U : RightDGModuleModel A ⥤ RightDGModuleModel B)
    (h : HomotopyCategoryLaws B) (X : derivedCategory B h) : Prop :=
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  ∃ P : RightDGModuleModel A, IndexedSemiFree.finiteCell P ∧
    Nonempty (Retract X ((quotient B h).obj (U.obj P)))

/-- Compactness uses the additive structure of the specified localization. -/
abbrev CompactAt (h : HomotopyCategoryLaws B)
    (S : letI := derivedCategoryInstance B h; Preadditive (derivedCategory B h))
    (X : derivedCategory B h) : Prop :=
  letI := derivedCategoryInstance B h
  letI := S
  IsCompact.{j,_,_} X

/-- At an adequate native bound, compactness for coproducts indexed in that
bound characterizes finite-cell retracts. Such retracts are compact for every
existing coproduct, including those indexed in a separately specified universe. -/
def NativeCompactFiniteCells : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w,w} k)
    (h : HomotopyCategoryLaws A),
    letI := derivedCategoryInstance A h
    ∀ S : Preadditive (derivedCategory A h),
      LocalizationMapAdditive h S →
      ∀ X : derivedCategory A h,
        let R := IsFiniteCellRetract (𝟭 (RightDGModuleModel A)) h X
        (CompactAt.{u,w,max v w,max v w} h S X ↔ R) ∧
          (R → CompactAt.{u,w,j,max v w} h S X)

/-- In the common adequate localization of an arbitrary original category,
the finite-cell representative can be taken over the original category.
The retract maps lie in the common localization. -/
def OriginalCompactFiniteCells : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    let B := category.{u,v,w,t} A
    let U := strictInput.{u,v,w,t} A
    ∀ h : HomotopyCategoryLaws B,
      letI := derivedCategoryInstance B h
      ∀ S : Preadditive (derivedCategory B h),
        LocalizationMapAdditive h S →
        ∀ X : derivedCategory B h,
          let R := IsFiniteCellRetract U h X
          (CompactAt.{u,w,max v w t,max v w t} h S X ↔ R) ∧
            (R → CompactAt.{u,w,j,max v w t} h S X)

/-- Compactness is preserved and reflected by the specified fully faithful
transition between adequate bounds for the original dg category. -/
def AmbientCompactnessComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    let B := category.{u,v,w,t} A
    let C := category.{u,v,w,max t s} A
    ∀ (h : HomotopyCategoryLaws B) (h' : HomotopyCategoryLaws C),
      letI := derivedCategoryInstance B h
      letI := derivedCategoryInstance C h'
      ∃ d : Descent h h' (strictTransition.{u,v,w,t,s} A),
        d.FullyFaithful ∧
        ∀ (S : Preadditive (derivedCategory B h)) (S' : Preadditive (derivedCategory C h')),
          LocalizationMapAdditive h S → LocalizationMapAdditive h' S' →
          ∀ X : derivedCategory B h,
            CompactAt.{u,w,max v w t,max v w t} h S X ↔
              CompactAt.{u,w,max v w t s,max v w t s} h' S' (d.D.obj X)

/-- The same compactness comparison when the lower coefficient bound is
already adequate and the upper model uses a single native coefficient lift. -/
def NativeCompactnessComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w,w} k),
    let B := liftCategory.{u,max v w,w,s} A
    ∀ (h : HomotopyCategoryLaws A) (h' : HomotopyCategoryLaws B),
      letI := derivedCategoryInstance A h
      letI := derivedCategoryInstance B h'
      ∃ d : Descent h h' (liftFunctor.{u,max v w,w,s} A),
        d.FullyFaithful ∧
        ∀ (S : Preadditive (derivedCategory A h)) (S' : Preadditive (derivedCategory B h')),
          LocalizationMapAdditive h S → LocalizationMapAdditive h' S' →
          ∀ X : derivedCategory A h,
            CompactAt.{u,w,max v w,max v w} h S X ↔
              CompactAt.{u,w,max v w s,max v w s} h' S' (d.D.obj X)

end

end Specs.DerivedFormalization.DG.CompactFiniteCells
