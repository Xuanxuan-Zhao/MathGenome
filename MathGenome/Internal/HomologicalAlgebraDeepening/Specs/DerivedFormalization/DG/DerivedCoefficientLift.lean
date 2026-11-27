import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedKProjective

open CategoryTheory
open _root_.DerivedFormalization

universe u v w t s r v' v''

namespace Specs.DerivedFormalization.DG.DerivedCoefficientLift

open AmbientDerived (category strictInput)
open CoefficientLift (liftCategory liftFunctor)
open CoefficientLiftComparison (restrictModule restrictMap)
open DerivedKProjective (derivedCategoryInstance)
open HomComplex (homotopyCategory homotopyClass)
open KProjective (isKProjective)

noncomputable section

variable {k : Type u} [CommRing k]

/-- The inverse arrow identification from the one-step lift to the two-step lift.
It fixes objects and substitutes two `up`s for one. -/
@[reducible] def unflatten (A : DGCategoryModel.{u,v,w} k) :
    DGFunctorModel (category.{u,v,w,max t s} A)
      (liftCategory.{u,max v w t,w,s} (category.{u,v,w,t} A)) where
  obj := id
  map _ _ := HomologicalComplex.Hom.isoOfComponents
    (fun _ => (show _ ≃ₗ[k] _ from
      ULift.moduleEquiv.trans (ULift.moduleEquiv.symm.trans ULift.moduleEquiv.symm)).toModuleIso)
    (fun _ _ _ => rfl) |>.hom
  map_id _ := rfl
  map_comp _ _ _ _ _ _ := rfl

/-- First enlarge the terms, then pull the lifted action back along the inverse
arrow identification. The output lives over the common one-step category. -/
@[reducible] def strictTransition (A : DGCategoryModel.{u,v,w} k) :
    RightDGModuleModel (category.{u,v,w,t} A) ⥤
      RightDGModuleModel (category.{u,v,w,max t s} A) where
  obj M := restrictModule (unflatten.{u,v,w,t,s} A)
    ((liftFunctor.{u,max v w t,w,s} _).obj M)
  map f := restrictMap (unflatten.{u,v,w,t,s} A)
    ((liftFunctor.{u,max v w t,w,s} _).map f)
  map_id _ := RightDGModuleModel.hom_ext fun _ => rfl
  map_comp _ _ := RightDGModuleModel.hom_ext fun _ => rfl

section Transition

variable {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v',w} k}

/-- A strict functor together with its specified action on homotopy classes and
the localization square. The equalities on representatives fix the functors on
the represented modules and maps. -/
structure Descent (h : Derived.HomotopyCategoryLaws A) (h' : Derived.HomotopyCategoryLaws B)
    (T : RightDGModuleModel A ⥤ RightDGModuleModel B) where
  H : @CategoryTheory.Functor _ (Derived.homotopyCategory A h) _ (Derived.homotopyCategory B h')
  D : @CategoryTheory.Functor _ (derivedCategoryInstance A h) _ (derivedCategoryInstance B h')
  obj (M : RightDGModuleModel A) :
    letI := Derived.homotopyCategory A h
    letI := Derived.homotopyCategory B h'
    H.obj M = T.obj M
  map {M N : RightDGModuleModel A} (f : M ⟶ N) :
    letI := Derived.homotopyCategory A h
    letI := Derived.homotopyCategory B h'
    HEq (H.map (homotopyClass f)) (homotopyClass (T.map f))
  square :
    letI := Derived.homotopyCategory A h
    letI := Derived.homotopyCategory B h'
    letI := derivedCategoryInstance A h
    letI := derivedCategoryInstance B h'
    Derived.quotient A h ⋙ D ≅ H ⋙ Derived.quotient B h'

def Descent.FullyFaithful {h : Derived.HomotopyCategoryLaws A}
    {h' : Derived.HomotopyCategoryLaws B} {T : RightDGModuleModel A ⥤ RightDGModuleModel B}
    (d : Descent h h' T) : Prop :=
  letI := Derived.homotopyCategory A h
  letI := Derived.homotopyCategory B h'
  letI := derivedCategoryInstance A h
  letI := derivedCategoryInstance B h'
  Nonempty d.H.FullyFaithful ∧ Nonempty d.D.FullyFaithful

variable {h : Derived.HomotopyCategoryLaws A} {h' : Derived.HomotopyCategoryLaws B}
  {T : RightDGModuleModel A ⥤ RightDGModuleModel B} (d : Descent h h' T)

/-- The homotopy map with its endpoints expressed as strict coefficient lifts. -/
def Descent.classMap {P N : RightDGModuleModel A} :
    Basic.h0Hom (HomComplex.homComplex P N) →
      Basic.h0Hom (HomComplex.homComplex (T.obj P) (T.obj N)) := by
  letI := Derived.homotopyCategory A h
  letI := Derived.homotopyCategory B h'
  intro g
  exact eqToHom (d.obj P).symm ≫ d.H.map (g : @Quiver.Hom (homotopyCategory A) _ P N) ≫
    eqToHom (d.obj N)

/-- On each pair of represented modules the homotopy map is the linear
comparison on degree-zero Hom cohomology. -/
def Descent.LinearOnClasses : Prop :=
  ∀ (P N : RightDGModuleModel A),
    ∃ E : Basic.h0Hom (HomComplex.homComplex P N) ≃ₗ[k]
        Basic.h0Hom (HomComplex.homComplex (T.obj P) (T.obj N)),
      ∀ g, E g = d.classMap g

/-- The isomorphism on the derived objects represented by strict modules. -/
def Descent.representedIso (M : RightDGModuleModel A) :
    letI := Derived.homotopyCategory A h
    letI := Derived.homotopyCategory B h'
    letI := derivedCategoryInstance A h
    letI := derivedCategoryInstance B h'
    d.D.obj ((Derived.quotient A h).obj M) ≅ (Derived.quotient B h').obj (T.obj M) := by
  letI := Derived.homotopyCategory A h
  letI := Derived.homotopyCategory B h'
  letI := derivedCategoryInstance A h
  letI := derivedCategoryInstance B h'
  exact d.square.app M ≪≫ eqToIso (congrArg (Derived.quotient B h').obj (d.obj M))

/-- The localization square identifies the derived Hom formulas for a
replacement and its lift via the transition on degree-zero Hom cohomology. -/
def Descent.ReplacementCompatible : Prop :=
  letI := Derived.homotopyCategory A h
  letI := Derived.homotopyCategory B h'
  letI := derivedCategoryInstance A h
  letI := derivedCategoryInstance B h'
  ∀ {P M : RightDGModuleModel A} (p : P ⟶ M) (hp : Module.quasiIsomorphism p),
    ∃ hp' : Module.quasiIsomorphism (T.map p),
      ∀ {N : RightDGModuleModel A} (g : Basic.h0Hom (HomComplex.homComplex P N)),
        d.D.map (DerivedKProjective.homComparisonMap h p hp g) ≫ (d.representedIso N).hom =
          (d.representedIso M).hom ≫
            DerivedKProjective.homComparisonMap h' (T.map p) hp' (d.classMap g)

end Transition

/-- A specified strict comparison induces the homotopy comparison componentwise
and the derived comparison through the three localization squares. -/
def CompositionComparison
    {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v',w} k}
    {C : DGCategoryModel.{u,v'',w} k}
    {hA : Derived.HomotopyCategoryLaws A} {hB : Derived.HomotopyCategoryLaws B}
    {hC : Derived.HomotopyCategoryLaws C}
    {F : RightDGModuleModel A ⥤ RightDGModuleModel B}
    {G : RightDGModuleModel B ⥤ RightDGModuleModel C}
    {J : RightDGModuleModel A ⥤ RightDGModuleModel C}
    (dF : Descent hA hB F) (dG : Descent hB hC G) (dJ : Descent hA hC J)
    (alpha : F ⋙ G ≅ J) : Prop :=
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := Derived.homotopyCategory C hC
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  letI := derivedCategoryInstance C hC
  ∃ eta : dF.H ⋙ dG.H ≅ dJ.H,
    (∀ M : RightDGModuleModel A,
      HEq (eta.hom.app M) (homotopyClass (alpha.hom.app M))) ∧
    ∃ theta : dF.D ⋙ dG.D ≅ dJ.D,
      ∀ M : homotopyCategory A,
        theta.hom.app ((Derived.quotient A hA).obj M) ≫ dJ.square.hom.app M =
          dG.D.map (dF.square.hom.app M) ≫ dG.square.hom.app (dF.H.obj M) ≫
            (Derived.quotient C hC).map (eta.hom.app M)

/-- The whole adequately sized homotopy and derived categories admit the
transition, and it induces bijections of morphisms between all represented
objects. The square identifies its derived action with the homotopy action. -/
def AmbientTransition : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A))
    (h' : Derived.HomotopyCategoryLaws (category.{u,v,w,max t s} A)),
    ∃ d : Descent h h' (strictTransition.{u,v,w,t,s} A),
      d.FullyFaithful ∧ d.LinearOnClasses ∧ d.ReplacementCompatible

/-- K-projectivity at the lower adequate bound is preserved against all acyclic
modules at the upper bound. -/
def KProjectiveTransition : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (P : RightDGModuleModel (category.{u,v,w,t} A)),
    isKProjective P → isKProjective ((strictTransition.{u,v,w,t,s} A).obj P)

/-- Native coefficients already containing the objects give the same
fully faithful transition property without a preliminary ambient lift. -/
def NativeTransition : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w,w} k)
    (h : Derived.HomotopyCategoryLaws A)
    (h' : Derived.HomotopyCategoryLaws (liftCategory.{u,max v w,w,s} A)),
    let T := liftFunctor.{u,max v w,w,s} A
    (∃ d : Descent h h' T, d.FullyFaithful ∧ d.LinearOnClasses ∧ d.ReplacementCompatible) ∧
    ∀ P : RightDGModuleModel A, isKProjective P → isKProjective (T.obj P)

/-- Sending an original module into the common derived category agrees with
first sending it to the lower bound and then enlarging. The strict comparison
flattens the two lifts on every coefficient. -/
def OriginalInputCompatibility : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws A)
    (h' : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A))
    (h'' : Derived.HomotopyCategoryLaws (category.{u,v,w,max t s} A)),
    let I := strictInput.{u,v,w,t} A
    let J := strictInput.{u,v,w,max t s} A
    let T := strictTransition.{u,v,w,t,s} A
    ∃ alpha : I ⋙ T ≅ J,
      (∀ (M : RightDGModuleModel A) (a : A.Obj) (i : ℤ)
          (x : ((T.obj (I.obj M)).complex a).X i),
        ((alpha.hom.app M).app a).f i x = ULift.up x.down.down) ∧
      ∀ (dI : Descent h h' I) (dT : Descent h' h'' T) (dJ : Descent h h'' J),
        CompositionComparison dI dT dJ alpha

/-- Starting with adequate native coefficients, the native lift to the upper
bound agrees with the ambient transition after the native equivalence.
The lower ambient category uses the same coefficient level as the native one. -/
def NativeAmbientCompatibility : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w,w} k)
    (h : Derived.HomotopyCategoryLaws A)
    (h' : Derived.HomotopyCategoryLaws (category.{u,max v w,w,0} A))
    (h'' : Derived.HomotopyCategoryLaws (category.{u,max v w,w,s} A)),
    let I := AmbientDerived.transportToAmbient.{u,v,w,0} A
    let T := strictTransition.{u,max v w,w,0,s} A
    let J := liftFunctor.{u,max v w,w,max w s} A
    ∃ alpha : I ⋙ T ≅ J,
      (∀ (M : RightDGModuleModel A) (a : A.Obj) (i : ℤ)
          (x : ((T.obj (I.obj M)).complex a).X i),
        ((alpha.hom.app M).app a).f i x = ULift.up x.down) ∧
      ∀ (dI : Descent h h' I) (dT : Descent h' h'' T) (dJ : Descent h h'' J),
        CompositionComparison dI dT dJ alpha

/-- Two successive enlargements agree with the single enlargement to the last
bound. The isomorphisms compare the specified strict action, homotopy classes,
and the localization squares. -/
def SuccessiveCompatibility : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A))
    (h' : Derived.HomotopyCategoryLaws (category.{u,v,w,max t s} A))
    (h'' : Derived.HomotopyCategoryLaws (category.{u,v,w,max t s r} A)),
    let F := strictTransition.{u,v,w,t,s} A
    let G := strictTransition.{u,v,w,max t s,r} A
    let J := strictTransition.{u,v,w,t,max s r} A
    ∃ alpha : F ⋙ G ≅ J,
      (∀ (M : RightDGModuleModel (category.{u,v,w,t} A)) (a : A.Obj) (i : ℤ)
          (x : ((G.obj (F.obj M)).complex a).X i),
        ((alpha.hom.app M).app a).f i x = ULift.up x.down.down) ∧
      ∀ (dF : Descent h h' F) (dG : Descent h' h'' G) (dJ : Descent h h'' J),
        CompositionComparison dF dG dJ alpha

/-- Coefficient identifications for the finite operations on represented
modules, including the maps in the cone of a strict morphism. -/
def FiniteOperations : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    let B := category.{u,v,w,t} A
    let C := category.{u,v,w,max t s} A
    let T := strictTransition.{u,v,w,t,s} A
    (∀ a : A.Obj,
      ∃ e : T.obj (Yoneda.representable (A := B) a) ≅ Yoneda.representable (A := C) a,
        ∀ (b : A.Obj) (i : ℤ)
          (x : ((T.obj (Yoneda.representable (A := B) a)).complex b).X i),
          (e.hom.app b).f i x = ULift.up x.down.down) ∧
    (∀ Z : RightDGModuleModel B, Limits.IsZero Z ↔ Limits.IsZero (T.obj Z)) ∧
    (∀ (n : ℕ) (F : Fin n → RightDGModuleModel B) {S : RightDGModuleModel B}
        (b : IndexedSemiFree.StrictSum F S),
      ∃ c : IndexedSemiFree.StrictSum (fun i => T.obj (F i)) (T.obj S),
        (∀ i, c.inclusion i = T.map (b.inclusion i)) ∧
        ∀ a j x i, (c.coordinates a j x i).down = b.coordinates a j x.down i) ∧
    ∃ S : ∀ (M : RightDGModuleModel B) (n : ℤ),
        T.obj (ShiftCone.shift M n) ≅ ShiftCone.shift (T.obj M) n,
      (∀ (M : RightDGModuleModel B) (n : ℤ) (a : A.Obj) (i : ℤ)
        (x : ((T.obj (ShiftCone.shift M n)).complex a).X i),
        (((S M n).hom.app a).f i x).down = x.down) ∧
      (∀ {M N : RightDGModuleModel B} (f : M ⟶ N) (n : ℤ),
        T.map (ShiftCone.shiftMap n f) ≫ (S N n).hom =
          (S M n).hom ≫ ShiftCone.shiftMap n (T.map f)) ∧
      ∃ E : ∀ {M N : RightDGModuleModel B} (f : M ⟶ N),
          T.obj (ShiftCone.cone f) ≅ ShiftCone.cone (T.map f),
        (∀ {M N : RightDGModuleModel B} (f : M ⟶ N) (a : A.Obj) (i : ℤ)
          (x : ((T.obj (ShiftCone.cone f)).complex a).X i),
          ((E f).hom.app a).f i x = (ULift.up x.down.1, ULift.up x.down.2)) ∧
        (∀ {M N : RightDGModuleModel B} (f : M ⟶ N),
          T.map (ShiftCone.coneInclusion f) ≫ (E f).hom =
            ShiftCone.coneInclusion (T.map f) ∧
          T.map (ShiftCone.coneProjection f) ≫ (S M 1).hom =
            (E f).hom ≫ ShiftCone.coneProjection (T.map f)) ∧
        ∀ {M N M' N' : RightDGModuleModel B} {f : M ⟶ N} {g : M' ⟶ N'}
          (p : M ⟶ M') (q : N ⟶ N') (e : f ≫ q = p ≫ g),
          T.map (CoefficientLiftComparison.coneMap p q e) ≫ (E g).hom =
            (E f).hom ≫ CoefficientLiftComparison.coneMap (T.map p) (T.map q) (by
              rw [← T.map_comp, ← T.map_comp, e])

end

end Specs.DerivedFormalization.DG.DerivedCoefficientLift
