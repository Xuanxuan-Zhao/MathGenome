import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CompactRepresentables
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedTriangles

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w t j

namespace Specs.DerivedFormalization.DG.CompactGenerators

open _root_.DerivedFormalization
open AmbientDerived (category)
open CompactRepresentables (RepresentableCompact ShiftedRepresentableHom)
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open DerivedTriangles (coneTriangle)
open HomComplex (homotopyCategory)
open SemiFree (cell)
open ShiftCone (shift)
open Yoneda (representable)

noncomputable section

/-- Closure under coproducts indexed in the indicated universe, using every
colimiting cofan with summands in the full subcategory. -/
def CoproductClosed.{i, o, m} {C : Type o} [Category.{m} C]
    (P : ObjectProperty C) : Prop :=
  ∀ {I : Type i} {F : I → C} (c : Cofan F), IsColimit c →
    (∀ a, P (F a)) → P c.pt

/-- Generation in the cone triangulation at an adequate bound.
Coproducts of the size of the coefficient universe suffice, so the conclusion
also applies to any full triangulated subcategory closed under all small coproducts. -/
def RepresentablesGenerate : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A)),
    let B := category.{u,v,w,t} A
    let K := homotopyCategory B
    let D := Derived.derivedCategory B h
    letI := Derived.homotopyCategory B h
    letI := derivedCategoryInstance B h
    let Q : K ⥤ D := Derived.quotient B h
    ∃ (SK : HasShift K ℤ) (SD : HasShift D ℤ) (AD : Preadditive D) (ZD : HasZeroObject D),
      letI := SK
      letI := SD
      letI := AD
      letI := ZD
      ∃ (hS : ∀ (M : K) (n : ℤ), (shiftFunctor K n).obj M = shift M n)
        (qS : Q.CommShift ℤ) (LD : ∀ n : ℤ, (shiftFunctor D n).Additive)
        (TD : Pretriangulated D),
        letI := qS
        letI := LD
        letI := TD
        IsTriangulated D ∧
          (∀ T : Triangle D, T ∈ distTriang D ↔
            ∃ (M N : RightDGModuleModel B)
              (_ : KProjective.isKProjective M) (_ : KProjective.isKProjective N) (f : M ⟶ N),
              Nonempty (T ≅ Q.mapTriangle.obj (coneTriangle h SK (hS M 1) f))) ∧
          (∀ {M N : RightDGModuleModel B} (f : M ⟶ N),
            Q.mapTriangle.obj (coneTriangle h SK (hS M 1) f) ∈ distTriang D) ∧
          ∀ (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms] [P.IsTriangulated],
            CoproductClosed.{max v w t,_,_} P →
            (∀ a : A.Obj, P (Q.obj (representable (A := B) a))) → ∀ X, P X

/-- Vanishing of the groups of maps out of the shifted representables detects
zero on the whole derived category, including every localized original input. -/
def ShiftedRepresentablesDetectZero : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A)),
    let B := category.{u,v,w,t} A
    letI := Derived.homotopyCategory B h
    letI := derivedCategoryInstance B h
    let Q := Derived.quotient B h
    ∀ X : Derived.derivedCategory B h,
      IsZero X ↔ ∀ (a : A.Obj) (n : ℤ),
        Subsingleton (Q.obj (cell (A := B) a n) ⟶ X)

/-- Representables are compact generators, with the shifted Hom computation
and its original-coefficient comparison. -/
def RepresentableCompactGenerators : Prop :=
  ShiftedRepresentableHom.{u,v,w,t} ∧ RepresentableCompact.{u,v,w,t,j} ∧
    RepresentablesGenerate.{u,v,w,t} ∧ ShiftedRepresentablesDetectZero.{u,v,w,t}

end

end Specs.DerivedFormalization.DG.CompactGenerators
