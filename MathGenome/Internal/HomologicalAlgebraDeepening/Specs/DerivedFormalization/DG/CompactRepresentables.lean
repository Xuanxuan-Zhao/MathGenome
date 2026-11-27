import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedKProjective

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum
open _root_.DerivedFormalization

universe u v w t j o m

namespace Specs.DerivedFormalization.DG.CompactRepresentables

open AmbientDerived (category strictInput)
open CoefficientLiftComparison (evaluateHomology)
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open HomComplex (homotopyClass)
open SemiFree (cell generator)
open Yoneda (representable)

noncomputable section

section Compactness

variable {C : Type o} [Category.{m} C] [Preadditive C] {I : Type j} {F : I → C}

/-- The canonical map from the direct sum of the morphism groups, induced by
the inclusions of a cofan. -/
def coproductHomMap (P : C) (c : Cofan F) :
    (⨁ i : I, P ⟶ F i) →+ (P ⟶ c.pt) := by
  classical
  exact DirectSum.toAddMonoid (fun i => Preadditive.rightComp P (c.inj i))

/-- Compactness for coproducts indexed in universe `j`. At any bound the
condition is on every coproduct that exists there. -/
def IsCompact (P : C) : Prop :=
  ∀ {I : Type j} {F : I → C} (c : Cofan F), IsColimit c →
    Function.Bijective (coproductHomMap P c)

end Compactness

/-- Additivity of the localization for the quotient-group addition on Hom in
the homotopy category. -/
def LocalizationMapAdditive {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,w} k}
    (h : HomotopyCategoryLaws B)
    (S : letI := derivedCategoryInstance B h; Preadditive (Derived.derivedCategory B h)) : Prop :=
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  letI := S
  let Q : HomComplex.homotopyCategory B ⥤ Derived.derivedCategory B h := Derived.quotient B h
  ∀ (M N : RightDGModuleModel B) (f g : Basic.h0Hom (HomComplex.homComplex M N)),
    (Q.map (f + g) : Q.obj M ⟶ Q.obj N) = Q.map f + Q.map g

/-- Evaluation on the shifted identity gives the derived Hom formula. For
original modules the target group is the cohomology of the original complex,
via the canonical coefficient comparison. -/
def ShiftedRepresentableHom : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A)),
    let B := category.{u,v,w,t} A
    let L := strictInput.{u,v,w,t} A
    letI := Derived.homotopyCategory B h
    letI := derivedCategoryInstance B h
    let Q : HomComplex.homotopyCategory B ⥤ Derived.derivedCategory B h := Derived.quotient B h
    ∃ S : Preadditive (Derived.derivedCategory B h),
      letI := S
      LocalizationMapAdditive h S ∧
      ∀ (a : A.Obj) (n : ℤ),
        L.obj (representable (A := A) a) = representable (A := B) a ∧
        ∃ (s : L.obj (cell (A := A) a n) ≅ cell (A := B) a n)
          (e : ∀ N : RightDGModuleModel B,
            (Q.obj (cell (A := B) a n) ⟶ Q.obj N) ≃+ (N.complex a).homology n)
          (e₀ : ∀ N : RightDGModuleModel A,
            (Q.obj (L.obj (cell (A := A) a n)) ⟶ Q.obj (L.obj N)) ≃+ (N.complex a).homology n),
          (∀ (b : A.Obj) (i : ℤ) (x : ((L.obj (cell (A := A) a n)).complex b).X i),
            ((s.hom.app b).f i x).down = x.down) ∧
          (∀ {N : RightDGModuleModel B} (f : cell (A := B) a n ⟶ N),
            ∃ x : (N.complex a).cycles n,
              (N.complex a).iCycles n x = (f.app a).f n (generator (A := B) a n) ∧
              e N (Q.map (homotopyClass f)) = (N.complex a).homologyπ n x) ∧
          (∀ {N T : RightDGModuleModel B} (f : N ⟶ T)
            (g : Q.obj (cell (A := B) a n) ⟶ Q.obj N),
            e T (g ≫ Q.map (homotopyClass f)) = homologyMap (f.app a) n (e N g)) ∧
          (∀ (N : RightDGModuleModel A)
            (g : Q.obj (L.obj (cell (A := A) a n)) ⟶ Q.obj (L.obj N)),
            e₀ N g = evaluateHomology (𝟙 (L.obj N)) a n
              (e (L.obj N) (Q.map (homotopyClass s.inv) ≫ g))) ∧
          ∀ {N T : RightDGModuleModel A} (f : N ⟶ T)
            (g : Q.obj (L.obj (cell (A := A) a n)) ⟶ Q.obj (L.obj N)),
            e₀ T (g ≫ Q.map (homotopyClass (L.map f))) = homologyMap (f.app a) n (e₀ N g)

/-- The represented Yoneda module is compact for all existing coproducts at
each adequate coefficient bound. For an arbitrary family the bound can
include its index universe. The additive structure is compatible with the
localization as in `ShiftedRepresentableHom`. -/
def RepresentableCompact : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A)),
    let B := category.{u,v,w,t} A
    letI := Derived.homotopyCategory B h
    letI := derivedCategoryInstance B h
    let Q : HomComplex.homotopyCategory B ⥤ Derived.derivedCategory B h := Derived.quotient B h
    ∀ (S : Preadditive (Derived.derivedCategory B h)),
      letI := S
      LocalizationMapAdditive h S →
      ∀ a : A.Obj, IsCompact.{j,_,_} (Q.obj (representable (A := B) a))

end

end Specs.DerivedFormalization.DG.CompactRepresentables
