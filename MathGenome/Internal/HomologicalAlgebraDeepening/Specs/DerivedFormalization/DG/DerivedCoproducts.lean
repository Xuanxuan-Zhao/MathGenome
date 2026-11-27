import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedSums
import Mathlib.LinearAlgebra.Pi

open CategoryTheory CategoryTheory.Limits
open _root_.DerivedFormalization

universe u v w j t s z v'

namespace Specs.DerivedFormalization.DG.DerivedCoproducts

open AmbientDerived (category strictInput)
open Basic (cyclesZero classOf h0Hom)
open Derived (HomotopyCategoryLaws)
open DerivedCoefficientLift (Descent strictTransition)
open DerivedKProjective (derivedCategoryInstance)
open HomComplex (homComplex homotopyClass)
open IndexedSemiFree (StrictSum)

noncomputable section

variable {k : Type u} [CommRing k] {I : Type j}

/-- Product of cochain complexes with degreewise product terms and differential. -/
def productComplex (C : I → ModuleCochain.{u,z} k) : ModuleCochain.{u,max z j} k where
  X n := ModuleCat.of k (∀ i, (C i).X n)
  d n m := ModuleCat.ofHom (LinearMap.pi fun i => ((C i).d n m).hom.comp (LinearMap.proj i))
  shape n m h := by
    ext x i
    have e := (C i).shape n m h
    change (C i).d n m (x i) = 0
    rw [e]
    rfl
  d_comp_d' l m n _ _ := by
    ext x i
    have e := (C i).d_comp_d l m n
    change (C i).d m n ((C i).d l m (x i)) = 0
    exact congrArg (fun f : (C i).X l ⟶ (C i).X n => f (x i)) e

/-- Projection of a degree-zero cocycle in the product. -/
def productCycle (C : I → ModuleCochain.{u,z} k)
    (x : cyclesZero (productComplex C)) (i : I) : cyclesZero (C i) :=
  ⟨x.val i, congrFun x.property i⟩

/-- The projection map on degree-zero cohomology of a product is a linear isomorphism. -/
def ProductH0 : Prop :=
  ∀ {k : Type u} [CommRing k] {I : Type j} (C : I → ModuleCochain.{u,z} k),
    ∃ e : h0Hom (productComplex C) ≃ₗ[k] (∀ i, h0Hom (C i)),
      ∀ (x : cyclesZero (productComplex C)) (i : I),
        e (classOf x) i = classOf (productCycle C x i)

section Strict

variable {A : DGCategoryModel.{u,v,w} k}
variable {F : I → RightDGModuleModel A} {S : RightDGModuleModel A}

/-- The derived cofan with the images of the actual strict inclusions. -/
def derivedCofan (h : HomotopyCategoryLaws A) (b : StrictSum F S) :
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    Cofan (fun i => (Derived.quotient A h).obj (F i)) := by
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  exact Cofan.mk ((Derived.quotient A h).obj S)
    (fun i => (Derived.quotient A h).map (homotopyClass (b.inclusion i)))

/-- The family of native semi-free resolutions, their strict sum and its
augmentation to the given strict sum. -/
def ResolutionSum (b : StrictSum F S) : Prop :=
  ∃ (P : I → RightDGModuleModel A) (p : ∀ i, P i ⟶ F i),
    (∀ i, IndexedSemiFree.semiFree (P i) ∧ Module.degreewiseSurjective (p i) ∧
      Module.quasiIsomorphism (p i)) ∧
    ∃ (U : RightDGModuleModel A) (a : StrictSum P U) (q : U ⟶ S),
      KProjective.isKProjective U ∧ Module.quasiIsomorphism q ∧
      ∀ i, a.inclusion i ≫ q = p i ≫ b.inclusion i

end Strict

/-- Restriction to the inclusions identifies the Hom complex out of a strict
sum with the product of the Hom complexes. On cohomology it is precomposition
by the classes of the same strict inclusions. -/
def HomFromStrictSum : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} {F : I → RightDGModuleModel A}
    {S : RightDGModuleModel A} (b : StrictSum F S) (N : RightDGModuleModel A),
    let H := homComplex S N
    let C := productComplex (fun i => homComplex (F i) N)
    (∃ e : ∀ r, H.X r ≃ₗ[k] C.X r,
      (∀ (r q : ℤ) (g : H.X r), e q (H.d r q g) = C.d r q (e r g)) ∧
      ∀ (r : ℤ) (g : H.X r) (i : I) (a : A.Obj)
        (n m : ℤ) (hn : n + r = m) (x : ((F i).complex a).X n),
        HomComplex.component (e r g i) a n m hn x =
          HomComplex.component g a n m hn ((b.inclusion i).app a |>.f n x)) ∧
    ∃ e : h0Hom H ≃ₗ[k] (∀ i, h0Hom (homComplex (F i) N)),
      ∀ (g : h0Hom H) (i : I),
        e g i = Basic.h0Comp (HomComplex.dgModuleCategory A) g (homotopyClass (b.inclusion i))

/-- A componentwise quasi-isomorphism induces a quasi-isomorphism on the
realized sums with the specified component maps. -/
def SumQuasiIsomorphism : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type j} {F G : I → RightDGModuleModel A} {S T : RightDGModuleModel A}
    (b : StrictSum F S) (c : StrictSum G T) (p : ∀ i, F i ⟶ G i),
    (∀ i, Module.quasiIsomorphism (p i)) →
    ∃ q : S ⟶ T, Module.quasiIsomorphism q ∧
      ∀ i, b.inclusion i ≫ q = p i ≫ c.inclusion i

/-- At an adequate native coefficient level containing the index, any
realization computes the derived coproduct via a sum of native resolutions. -/
def NativeDerivedCoproduct : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w j,w} k}
    (h : HomotopyCategoryLaws A) {I : Type j} {F : I → RightDGModuleModel A}
    {S : RightDGModuleModel A} (b : StrictSum F S),
    letI := derivedCategoryInstance A h
    ResolutionSum b ∧ Nonempty (IsColimit (derivedCofan h b))

/-- Every original family has a realized finite-support coproduct of its
represented modules at a common bound containing coefficients, objects and index. -/
def OriginalDerivedCoproduct : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,max j t} A))
    {I : Type j} (F : I → RightDGModuleModel A),
    let B := category.{u,v,w,max j t} A
    let L := strictInput.{u,v,w,max j t} A
    letI := derivedCategoryInstance B h
    ∃ (S : RightDGModuleModel B) (b : StrictSum (fun i => L.obj (F i)) S),
      ResolutionSum b ∧ Nonempty (IsColimit (derivedCofan h b))

/-- When the original family already has a realized pointwise sum, its
actual inclusions represent a coproduct at every adequate bound, even
when the index itself exceeds that bound. -/
def OriginalExistingDerivedCoproduct : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A))
    {I : Type j} {F : I → RightDGModuleModel A} {S : RightDGModuleModel A}
    (b : StrictSum F S),
    let B := category.{u,v,w,t} A
    let L := strictInput.{u,v,w,t} A
    letI := derivedCategoryInstance B h
    ∃ c : StrictSum (fun i => L.obj (F i)) (L.obj S),
      (∀ i, c.inclusion i = L.map (b.inclusion i)) ∧
      (∀ a n x i, (c.coordinates a n x i).down = b.coordinates a n x.down i) ∧
      Nonempty (IsColimit (derivedCofan h c))

/-- The G02 strict coproduct in its original range agrees with the
finite-support realization, compatibly with inclusions and coordinates. -/
def G02SumComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type v} {F : I → RightDGModuleModel A}
    (c : Cofan F) (_hc : IsColimit c) {S : RightDGModuleModel A} (b : StrictSum F S),
    ∃ (a : StrictSum F c.pt) (e : c.pt ≅ S),
      (∀ i, a.inclusion i = c.inj i) ∧
      (∀ i, c.inj i ≫ e.hom = b.inclusion i) ∧
      ∀ x n y, b.coordinates x n ((e.hom.app x).f n y) = a.coordinates x n y

section Comparison

variable {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v',w} k}
variable {h : HomotopyCategoryLaws A} {h' : HomotopyCategoryLaws B}
variable {T : RightDGModuleModel A ⥤ RightDGModuleModel B}
variable {F : I → RightDGModuleModel A} {S : RightDGModuleModel A}

/-- The represented-object isomorphisms for a transition compare both the
inclusions and the maps out of the coproduct to a transitioned target. -/
def TransitionMaps (d : Descent h h' T) (b : StrictSum F S)
    (c : StrictSum (fun i => T.obj (F i)) (T.obj S)) : Prop :=
  letI := Derived.homotopyCategory A h
  letI := Derived.homotopyCategory B h'
  letI := derivedCategoryInstance A h
  letI := derivedCategoryInstance B h'
  (∀ i, d.D.map ((derivedCofan h b).inj i) ≫ (d.representedIso S).hom =
    (d.representedIso (F i)).hom ≫ (derivedCofan h' c).inj i) ∧
  ∀ (hb : IsColimit (derivedCofan h b)) (hc : IsColimit (derivedCofan h' c))
    {X : Derived.derivedCategory A h} (f : ∀ i, (Derived.quotient A h).obj (F i) ⟶ X),
    d.D.map (Cofan.IsColimit.desc hb f) =
      (d.representedIso S).hom ≫ Cofan.IsColimit.desc hc
        (fun i => (d.representedIso (F i)).inv ≫ d.D.map (f i))

end Comparison

/-- Along a further enlargement, an already realized sum is still pointwise
the same finite-support sum with lifted coefficients. The fully faithful
transition matches the coproduct maps, for arbitrary indices at the lower
bound where the sum already exists. -/
def AmbientCoproductTransition : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A))
    (h' : HomotopyCategoryLaws (category.{u,v,w,max t s} A))
    {I : Type j} {F : I → RightDGModuleModel (category.{u,v,w,t} A)}
    {S : RightDGModuleModel (category.{u,v,w,t} A)} (b : StrictSum F S),
    let B := category.{u,v,w,t} A
    let C := category.{u,v,w,max t s} A
    let T := strictTransition.{u,v,w,t,s} A
    letI := derivedCategoryInstance B h
    letI := derivedCategoryInstance C h'
    ∃ (d : Descent h h' T) (c : StrictSum (fun i => T.obj (F i)) (T.obj S)),
      d.FullyFaithful ∧
      (∀ i, c.inclusion i = T.map (b.inclusion i)) ∧
      (∀ a n x i, (c.coordinates a n x i).down = b.coordinates a n x.down i) ∧
      Nonempty (IsColimit (derivedCofan h b)) ∧
      Nonempty (IsColimit (derivedCofan h' c)) ∧
      TransitionMaps d b c

/-- The same derived property for native coefficient categories that already
contain the object type, with every realized index size. -/
def NativeExistingDerivedCoproduct : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w,w} k}
    (h : HomotopyCategoryLaws A) {I : Type j} {F : I → RightDGModuleModel A}
    {S : RightDGModuleModel A} (b : StrictSum F S),
    letI := derivedCategoryInstance A h
    Nonempty (IsColimit (derivedCofan h b))

end

end Specs.DerivedFormalization.DG.DerivedCoproducts
