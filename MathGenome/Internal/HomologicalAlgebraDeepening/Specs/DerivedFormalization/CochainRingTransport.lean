import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedRestriction
import Mathlib.Algebra.Ring.Shrink
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.RingTheory.Flat.Basic

/-! Change of ring representative at a fixed module universe. -/

namespace Specs.DerivedFormalization.CochainRingTransport

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.DerivedFormalization.Cochains
open Specs.DerivedFormalization.DerivedRestriction
open scoped ChangeOfRings

universe a u s t

attribute [local instance] HasDerivedCategory.standard
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

noncomputable section

section Rings

variable {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A)

def moduleEquivalenceType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (_ : R ≃+* A),
    ModuleCat.{a} R ≌ ModuleCat.{a} A

abbrev moduleEquivalenceValue : ModuleCat.{a} R ≌ ModuleCat.{a} A :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm

def uliftRingEquivType := ∀ (R : Type u) [Ring R], R ≃+* ULift.{a} R

abbrev uliftRingEquivValue (R : Type u) [Ring R] : R ≃+* ULift.{a} R :=
  ULift.ringEquiv.symm

def shrinkRingEquivType := ∀ (R : Type u) [Ring R] [Small.{a} R], R ≃+* Shrink.{a} R

abbrev shrinkRingEquivValue (R : Type u) [Ring R] [Small.{a} R] :
    R ≃+* Shrink.{a} R := (Shrink.ringEquiv R).symm

def moduleActionType : Prop :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A)
    (M : ModuleCat.{a} R) (r : A) (x : (moduleEquivalenceValue e).functor.obj M),
    r • x = e.symm r • (show M from x)

def moduleMapType : Prop :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A)
    {M N : ModuleCat.{a} R} (g : M ⟶ N) (x : M),
    (moduleEquivalenceValue e).functor.map g x = g x

def moduleExactType : Prop :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A),
    (moduleEquivalenceValue e).functor.Additive ∧
    PreservesFiniteLimits (moduleEquivalenceValue e).functor ∧
    PreservesFiniteColimits (moduleEquivalenceValue e).functor ∧
    ∀ C : ShortComplex (ModuleCat.{a} R), (C.map (moduleEquivalenceValue e).functor).Exact ↔ C.Exact

def complexEquivalenceType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (_ : R ≃+* A),
    compValue.{a} R ≌ compValue.{a} A

abbrev complexEquivalenceValue : compValue.{a} R ≌ compValue.{a} A :=
  (moduleEquivalenceValue e).mapHomologicalComplex (.up ℤ)

def complexFunctorType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A], (R ≃+* A) →
    compValue.{a} R ⥤ compValue.{a} A

abbrev complexFunctorValue : compValue.{a} R ⥤ compValue.{a} A :=
  (moduleEquivalenceValue e).functor.mapHomologicalComplex (.up ℤ)

abbrev homotopyFunctorValue : homotopyValue.{a} R ⥤ homotopyValue.{a} A :=
  (moduleEquivalenceValue e).functor.mapHomotopyCategory (.up ℤ)

abbrev derivedFunctorValue : derivedValue.{a} R ⥤ derivedValue.{a} A :=
  (moduleEquivalenceValue e).functor.mapDerivedCategory

def homotopyFunctorType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A], (R ≃+* A) →
    homotopyValue.{a} R ⥤ homotopyValue.{a} A

def derivedFunctorType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A], (R ≃+* A) →
    derivedValue.{a} R ⥤ derivedValue.{a} A

def inducedEquivalencesType : Prop :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A),
    (∃ E : homotopyValue.{a} R ≌ homotopyValue.{a} A,
      E.functor = homotopyFunctorValue e ∧
      E.inverse = (moduleEquivalenceValue e).inverse.mapHomotopyCategory (.up ℤ)) ∧
    (∃ E : derivedValue.{a} R ≌ derivedValue.{a} A,
      E.functor = derivedFunctorValue e ∧
      E.inverse = (moduleEquivalenceValue e).inverse.mapDerivedCategory) ∧
    (homotopyFunctorValue e).IsTriangulated ∧ (derivedFunctorValue e).IsTriangulated

def homotopyFactorsType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A),
    quotientValue.{a} R ⋙ (homotopyFunctorValue e) ≅ (complexFunctorValue e) ⋙ quotientValue.{a} A

def homotopyFactorsValue : quotientValue.{a} R ⋙ (homotopyFunctorValue e) ≅ (complexFunctorValue e) ⋙ quotientValue.{a} A :=
  (moduleEquivalenceValue e).functor.mapHomotopyCategoryFactors (.up ℤ)

def derivedFactorsType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A),
    qValue.{a} R ⋙ (derivedFunctorValue e) ≅ (complexFunctorValue e) ⋙ qValue.{a} A

def derivedFactorsValue : qValue.{a} R ⋙ (derivedFunctorValue e) ≅ (complexFunctorValue e) ⋙ qValue.{a} A :=
  (moduleEquivalenceValue e).functor.mapDerivedCategoryFactors

def derivedFactorshType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A),
    qhValue.{a} R ⋙ (derivedFunctorValue e) ≅ (homotopyFunctorValue e) ⋙ qhValue.{a} A

def derivedFactorshValue : qhValue.{a} R ⋙ (derivedFunctorValue e) ≅ (homotopyFunctorValue e) ⋙ qhValue.{a} A :=
  (moduleEquivalenceValue e).functor.mapDerivedCategoryFactorsh

def localizationCompatibilityType : Prop :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A) (X : compValue.{a} R),
    (derivedFactorshValue e).hom.app ((quotientValue.{a} R).obj X) =
      (derivedFunctorValue e).map ((quotientCompQhIsoValue.{a} R).hom.app X) ≫
        (derivedFactorsValue e).hom.app X ≫
        (quotientCompQhIsoValue.{a} A).inv.app ((complexFunctorValue e).obj X) ≫
        (qhValue.{a} A).map ((homotopyFactorsValue e).inv.app X)

def shiftCompatibilityType : Prop :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A),
    (∀ (X : compValue.{a} R) (n i : ℤ), (((complexFunctorValue e).commShiftIso n).hom.app X).f i = 𝟙 _) ∧
      NatTrans.CommShift ((moduleEquivalenceValue e).functor.mapHomotopyCategoryFactors (.up ℤ)).hom ℤ ∧
      NatTrans.CommShift (derivedFactorsValue e).hom ℤ ∧
      NatTrans.CommShift (moduleEquivalenceValue e).functor.mapDerivedCategoryFactorsh.hom ℤ

def cohomologyIsoType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A) (i : ℤ),
    (complexFunctorValue e) ⋙ cohomologyValue.{a} A i ≅ cohomologyValue.{a} R i ⋙ ((moduleEquivalenceValue e).functor)

def cohomologyIsoValue (i : ℤ) :
    (complexFunctorValue e) ⋙ cohomologyValue.{a} A i ≅ cohomologyValue.{a} R i ⋙ ((moduleEquivalenceValue e).functor) :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor (ModuleCat.{a} R) (.up ℤ) i)
    (ShortComplex.homologyFunctorIso ((moduleEquivalenceValue e).functor))

def derivedCohomologyIsoType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A) (i : ℤ),
    (derivedFunctorValue e) ⋙ derivedCohomologyValue.{a} A i ≅ derivedCohomologyValue.{a} R i ⋙ ((moduleEquivalenceValue e).functor)

def derivedCohomologyIsoValue (i : ℤ) :
    (derivedFunctorValue e) ⋙ derivedCohomologyValue.{a} A i ≅ derivedCohomologyValue.{a} R i ⋙ ((moduleEquivalenceValue e).functor) :=
  Localization.liftNatIso (qValue.{a} R) (HomologicalComplex.quasiIso (ModuleCat.{a} R) (.up ℤ))
    _ _ _ _
    (Functor.isoWhiskerRight (derivedFactorsValue e) _ ≪≫
      Functor.isoWhiskerLeft (complexFunctorValue e) (cohomologyFactorsValue.{a} A i) ≪≫
      cohomologyIsoValue e i ≪≫ Functor.isoWhiskerRight (cohomologyFactorsValue.{a} R i).symm _)

def homotopyCohomologyIsoType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A) (i : ℤ),
    (homotopyFunctorValue e) ⋙ HomotopyCategory.homologyFunctor (ModuleCat.{a} A) (.up ℤ) i ≅
      HomotopyCategory.homologyFunctor (ModuleCat.{a} R) (.up ℤ) i ⋙ ((moduleEquivalenceValue e).functor)

def homotopyCohomologyIsoValue (i : ℤ) :
    (homotopyFunctorValue e) ⋙ HomotopyCategory.homologyFunctor (ModuleCat.{a} A) (.up ℤ) i ≅
      HomotopyCategory.homologyFunctor (ModuleCat.{a} R) (.up ℤ) i ⋙ ((moduleEquivalenceValue e).functor) :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight (homotopyFactorsValue e) _ ≪≫
      Functor.isoWhiskerLeft (complexFunctorValue e) (HomotopyCategory.homologyFunctorFactors (ModuleCat.{a} A) _ i) ≪≫
      cohomologyIsoValue e i ≪≫ Functor.isoWhiskerRight
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{a} R) _ i).symm _)

def modulePropertiesType : Prop :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A) (M : ModuleCat.{a} R),
    (Projective ((moduleEquivalenceValue e).functor.obj M) ↔ Projective M) ∧
    (Injective ((moduleEquivalenceValue e).functor.obj M) ↔ Injective M) ∧
    (Module.Finite A ((moduleEquivalenceValue e).functor.obj M) ↔ Module.Finite R M)

def complexComponentsType : Prop :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A) (X Y : compValue.{a} R)
    (g : X ⟶ Y) (i j : ℤ),
    ((complexFunctorValue e).obj X).X i = (moduleEquivalenceValue e).functor.obj (X.X i) ∧
    HEq (((complexFunctorValue e).obj X).d i j)
      ((moduleEquivalenceValue e).functor.map (X.d i j)) ∧
    HEq (((complexFunctorValue e).map g).f i) ((moduleEquivalenceValue e).functor.map (g.f i))

def complexPropertiesType : Prop :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A) (X Y : compValue.{a} R)
    (g : X ⟶ Y),
    (((complexFunctorValue e).obj X).Acyclic ↔ X.Acyclic) ∧
    (QuasiIso ((complexFunctorValue e).map g) ↔ QuasiIso g) ∧
    (∀ i : ℤ, Function.Injective (((complexFunctorValue e).map g).f i) ↔ Function.Injective (g.f i)) ∧
    (∀ i : ℤ, Function.Surjective (((complexFunctorValue e).map g).f i) ↔ Function.Surjective (g.f i))

/-- The rank-one free module on the original side, represented on the carrier of the small ring. -/
abbrev rankOneValue : ModuleCat.{a} R :=
  (moduleEquivalenceValue e).inverse.obj (ModuleCat.of A A)

def rankOneType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A], (R ≃+* A) → ModuleCat.{a} R

def rankOneComparisonType :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A),
    (complexFunctorValue e).obj ((stalkValue.{a} R).obj (rankOneValue e)) ≅ (stalkValue.{a} A).obj (ModuleCat.of A A)

def rankOneComparisonValue :
    (complexFunctorValue e).obj ((stalkValue.{a} R).obj (rankOneValue e)) ≅ (stalkValue.{a} A).obj (ModuleCat.of A A) :=
  ((moduleEquivalenceValue e).functor.mapCochainComplexSingleFunctor 0).app (rankOneValue e) ≪≫
    (stalkValue.{a} A).mapIso ((moduleEquivalenceValue e).counitIso.app (ModuleCat.of A A))

def rankOneGeneratorType : Prop :=
  ∀ {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A)
    (r : R) (x : rankOneValue e),
    (r • (show rankOneValue e from (1 : A)) : rankOneValue e) = x ↔ e r = (show A from x)

end Rings

def flatnessType : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] (e : R ≃+* A) (M : ModuleCat.{a} R),
    Module.Flat A ((moduleEquivalenceValue e).functor.obj M) ↔ Module.Flat R M


section Restriction

variable {R : Type u} {S : Type s} {A B : Type a}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S)

def conjugateType :=
  ∀ {R : Type u} {S : Type s} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B],
    (R ≃+* A) → (S ≃+* B) → (R →+* S) → (A →+* B)

abbrev conjugateValue : A →+* B :=
  d.toRingHom.comp (f.comp e.symm.toRingHom)


def restrictionIsoType :=
  ∀ {R : Type u} {S : Type s} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S),
    restrictScalarsValue.{a} f ⋙ ((moduleEquivalenceValue e).functor) ≅ ((moduleEquivalenceValue d).functor) ⋙ restrictScalarsValue.{a} (conjugateValue e d f)

def restrictionIsoValue : restrictScalarsValue.{a} f ⋙ ((moduleEquivalenceValue e).functor) ≅ ((moduleEquivalenceValue d).functor) ⋙ restrictScalarsValue.{a} (conjugateValue e d f) :=
  (ModuleCat.restrictScalarsComp e.symm.toRingHom f).symm ≪≫
    ModuleCat.restrictScalarsComp' (conjugateValue e d f) d.symm.toRingHom (f.comp e.symm.toRingHom) (by
      ext x
      exact (d.symm_apply_apply (f (e.symm x))).symm)

def restrictionIdentityOnCarriersType : Prop :=
  ∀ {R : Type u} {S : Type s} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S)
    (M : ModuleCat.{a} S) (x : M),
    (restrictionIsoValue e d f).hom.app M x = x ∧
    (restrictionIsoValue e d f).inv.app M x = x

def complexRestrictionIsoType :=
  ∀ {R : Type u} {S : Type s} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S),
    restrictScalarsComplexValue.{a} f ⋙ complexFunctorValue e ≅
      complexFunctorValue d ⋙ restrictScalarsComplexValue.{a} (conjugateValue e d f)

def complexRestrictionIsoValue :
    restrictScalarsComplexValue.{a} f ⋙ complexFunctorValue e ≅
      complexFunctorValue d ⋙ restrictScalarsComplexValue.{a} (conjugateValue e d f) :=
  NatIso.mapHomologicalComplex (restrictionIsoValue e d f) (.up ℤ)

def complexRestrictionComponentsType : Prop :=
  ∀ {R : Type u} {S : Type s} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S)
    (X : compValue.{a} S) (i : ℤ) (x : X.X i),
    ((complexRestrictionIsoValue e d f).hom.app X).f i x = x ∧
    ((complexRestrictionIsoValue e d f).inv.app X).f i x = x

end Restriction

section DerivedComparisons

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃} {J : C₃ ⥤ C₄}
  [F.Additive] [G.Additive] [H.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
  [PreservesFiniteLimits J] [PreservesFiniteColimits F] [PreservesFiniteColimits G]
  [PreservesFiniteColimits H] [PreservesFiniteColimits J]

/-- Descend a natural isomorphism of exact functors using its degreewise components. -/
def derivedIso {F₁ F₂ : C₁ ⥤ C₂} [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteLimits F₂]
    [PreservesFiniteColimits F₁] [PreservesFiniteColimits F₂] (α : F₁ ≅ F₂) :
    F₁.mapDerivedCategory ≅ F₂.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C₁ (.up ℤ))
    _ _ _ _ (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex α (.up ℤ)) DerivedCategory.Q)

def derivedSquare (α : F ⋙ G ≅ H ⋙ J) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory ⋙ J.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso F G ≪≫ derivedIso α ≪≫
    (Functor.mapDerivedCategoryCompIso H J).symm

end DerivedComparisons

section Coherence

variable {R : Type u} {S : Type s} {T : Type t} {A B C : Type a}
  [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B] [CommRing C]
  (e : R ≃+* A) (d : S ≃+* B) (c : T ≃+* C) (f : R →+* S) (g : S →+* T)


def derivedRestrictionIsoType :=
  ∀ {R : Type u} {S : Type s} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S),
    derivedRestrictScalarsValue.{a} f ⋙ derivedFunctorValue e ≅ derivedFunctorValue d ⋙ derivedRestrictScalarsValue.{a} (conjugateValue e d f)

def derivedRestrictionIsoValue :
    derivedRestrictScalarsValue.{a} f ⋙ derivedFunctorValue e ≅ derivedFunctorValue d ⋙ derivedRestrictScalarsValue.{a} (conjugateValue e d f) :=
  derivedSquare (restrictionIsoValue e d f)

def derivedRestrictionComponentsType : Prop :=
  ∀ {R : Type u} {S : Type s} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S) (X : compValue.{a} S),
    (derivedRestrictionIsoValue e d f).hom.app ((qValue.{a} S).obj X) ≫
        (derivedRestrictScalarsValue.{a} (conjugateValue e d f)).map
          ((derivedFactorsValue d).hom.app X) ≫
        (derivedRestrictScalarsFactorsValue.{a} (conjugateValue e d f)).hom.app
          ((complexFunctorValue d).obj X) =
      (derivedFunctorValue e).map ((derivedRestrictScalarsFactorsValue.{a} f).hom.app X) ≫
        (derivedFactorsValue e).hom.app ((restrictScalarsComplexValue.{a} f).obj X) ≫
        (qValue.{a} A).map ((complexRestrictionIsoValue e d f).hom.app X)

/-- Composition of restriction on the original rings or their representatives. -/
def restrictionComp (f : R →+* S) (g : S →+* T) :
    restrictScalarsValue.{a} g ⋙ restrictScalarsValue.{a} f ≅ restrictScalarsValue.{a} (g.comp f) :=
  (ModuleCat.restrictScalarsComp f g).symm

def conjugateComp :
    restrictScalarsValue.{a} (conjugateValue d c g) ⋙ restrictScalarsValue.{a} (conjugateValue e d f) ≅ restrictScalarsValue.{a} (conjugateValue e c (g.comp f)) :=
  (ModuleCat.restrictScalarsComp' (conjugateValue e d f) (conjugateValue d c g) (conjugateValue e c (g.comp f)) (by
    ext x
    change c (g (f (e.symm x))) = c (g (d.symm (d (f (e.symm x)))))
    rw [RingEquiv.symm_apply_apply])).symm

def conjugateId :
    restrictScalarsValue.{a} (conjugateValue e e (RingHom.id R)) ≅ 𝟭 _ :=
  ModuleCat.restrictScalarsId' _ (by ext x; exact e.apply_symm_apply x)

def derivedComp {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] {I : C₁ ⥤ C₂} {J : C₂ ⥤ C₃} {K : C₁ ⥤ C₃}
    [I.Additive] [J.Additive] [K.Additive] [PreservesFiniteLimits I] [PreservesFiniteLimits J]
    [PreservesFiniteLimits K] [PreservesFiniteColimits I] [PreservesFiniteColimits J]
    [PreservesFiniteColimits K] (α : I ⋙ J ≅ K) :
    I.mapDerivedCategory ⋙ J.mapDerivedCategory ≅ K.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso I J ≪≫ derivedIso α

def complexId {C₁ : Type*} [Category* C₁] [Abelian C₁] {I : C₁ ⥤ C₁} [I.Additive]
    (α : I ≅ 𝟭 _) : I.mapHomologicalComplex (.up ℤ) ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex α (.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso _ (.up ℤ)

def derivedId {C₁ : Type*} [Category* C₁] [Abelian C₁] {I : C₁ ⥤ C₁} [I.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I] (α : I ≅ 𝟭 _) :
    I.mapDerivedCategory ≅ 𝟭 _ :=
  derivedIso α ≪≫ Functor.mapDerivedCategoryIdIso C₁

/-- The comparison commutes with the two canonical ways to restrict through a composite. -/
def compositionCoherent
    {R S T A B C : Type*} [Category* R] [Category* S] [Category* T]
    [Category* A] [Category* B] [Category* C]
    {F : R ⥤ A} {G : S ⥤ B} {H : T ⥤ C}
    {f : S ⥤ R} {g : T ⥤ S} {gf : T ⥤ R}
    {f' : B ⥤ A} {g' : C ⥤ B} {gf' : C ⥤ A}
    (α : f ⋙ F ≅ G ⋙ f') (β : g ⋙ G ≅ H ⋙ g') (γ : gf ⋙ F ≅ H ⋙ gf')
    (δ : g ⋙ f ≅ gf) (δ' : g' ⋙ f' ≅ gf') : Prop :=
  ∀ X : T, F.map (δ.hom.app X) ≫ γ.hom.app X =
    α.hom.app (g.obj X) ≫ f'.map (β.hom.app X) ≫ δ'.hom.app (H.obj X)

def identityCoherent {R A : Type*} [Category* R] [Category* A] {F : R ⥤ A}
    {I : R ⥤ R} {J : A ⥤ A} (α : I ⋙ F ≅ F ⋙ J) (δ : I ≅ 𝟭 R) (δ' : J ≅ 𝟭 A) : Prop :=
  ∀ X : R, F.map (δ.hom.app X) = α.hom.app X ≫ δ'.hom.app (F.obj X)

def compositionCoherenceType : Prop :=
  ∀ {R : Type u} {S : Type s} {T : Type t} {A B C : Type a}
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B] [CommRing C]
    (e : R ≃+* A) (d : S ≃+* B) (c : T ≃+* C) (f : R →+* S) (g : S →+* T),
    compositionCoherent (restrictionIsoValue e d f) (restrictionIsoValue d c g)
      (restrictionIsoValue e c (g.comp f)) (restrictionComp.{a} f g) (conjugateComp e d c f g) ∧
    compositionCoherent (complexRestrictionIsoValue e d f) (complexRestrictionIsoValue d c g)
      (complexRestrictionIsoValue e c (g.comp f))
      (Functor.mapHomologicalComplexCompIso (restrictionComp.{a} f g) (.up ℤ))
      (Functor.mapHomologicalComplexCompIso (conjugateComp e d c f g) (.up ℤ)) ∧
    compositionCoherent (derivedRestrictionIsoValue e d f) (derivedRestrictionIsoValue d c g)
      (derivedRestrictionIsoValue e c (g.comp f))
      (derivedComp (restrictionComp.{a} f g)) (derivedComp (conjugateComp e d c f g))

def identityCoherenceType : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] (e : R ≃+* A),
    identityCoherent (restrictionIsoValue e e (RingHom.id R))
      (ModuleCat.restrictScalarsId R) (conjugateId e) ∧
    identityCoherent (complexRestrictionIsoValue e e (RingHom.id R))
      (complexId (ModuleCat.restrictScalarsId R)) (complexId (conjugateId e)) ∧
    identityCoherent (derivedRestrictionIsoValue e e (RingHom.id R))
      (derivedId (ModuleCat.restrictScalarsId R)) (derivedId (conjugateId e))

end Coherence


/-- The two natural transformations commute with the unit and counit of both adjunctions. -/
def adjunctionCompatible
    {C D E K : Type*} [Category* C] [Category* D] [Category* E] [Category* K]
    {G : C ⥤ E} {H : D ⥤ K} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ K} {R₂ : K ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂) : Prop :=
  (∀ X : C, G.map (adj₁.unit.app X) ≫ β.app (L₁.obj X) =
    adj₂.unit.app (G.obj X) ≫ R₂.map (α.app X)) ∧
  (∀ Y : D, L₂.map (β.app Y) ≫ adj₂.counit.app (H.obj Y) =
    α.app (R₁.obj Y) ≫ H.map (adj₁.counit.app Y))

section Adjunctions

variable {R : Type u} {S : Type s} {A B : Type (max a s)}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S)

def extensionMateValue :
    (moduleEquivalenceValue e).functor ⋙ ModuleCat.extendScalars (conjugateValue e d f) ⟶
      ModuleCat.extendScalars.{u, s, max a s} f ⋙ (moduleEquivalenceValue d).functor :=
  (mateEquiv (ModuleCat.extendRestrictScalarsAdj.{a} f)
    (ModuleCat.extendRestrictScalarsAdj.{max a s} (conjugateValue e d f))).symm
      (restrictionIsoValue e d f).hom

def coextensionMateValue :
    ModuleCat.coextendScalars.{u, s, max a s} f ⋙ (moduleEquivalenceValue d).functor ⟶
      (moduleEquivalenceValue e).functor ⋙ ModuleCat.coextendScalars (conjugateValue e d f) :=
  mateEquiv (ModuleCat.restrictCoextendScalarsAdj.{a} f)
    (ModuleCat.restrictCoextendScalarsAdj.{max a s} (conjugateValue e d f))
      (restrictionIsoValue e d f).inv

def extensionMateType : Prop :=
  ∀ {R : Type u} {S : Type s} {A B : Type (max a s)}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S),
    ∃ α : ModuleCat.extendScalars.{u, s, max a s} f ⋙ (moduleEquivalenceValue d).functor ≅
      (moduleEquivalenceValue e).functor ⋙ ModuleCat.extendScalars (conjugateValue e d f),
      α.inv = extensionMateValue.{a} e d f ∧
      (∀ (M : ModuleCat.{max a s} R) (b : S) (x : M),
        α.hom.app M (b ⊗ₜ[R,f] x) =
          ((d b) ⊗ₜ[A,conjugateValue e d f] (show (moduleEquivalenceValue e).functor.obj M from x) :
            (ModuleCat.extendScalars (conjugateValue e d f)).obj
              ((moduleEquivalenceValue e).functor.obj M))) ∧
      adjunctionCompatible (ModuleCat.extendRestrictScalarsAdj.{a} f)
        (ModuleCat.extendRestrictScalarsAdj.{max a s} (conjugateValue e d f))
        α.inv (restrictionIsoValue e d f).hom

def coextensionMateType : Prop :=
  ∀ {R : Type u} {S : Type s} {A B : Type (max a s)}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S),
    ∃ α : ModuleCat.coextendScalars.{u, s, max a s} f ⋙ (moduleEquivalenceValue d).functor ≅
      (moduleEquivalenceValue e).functor ⋙ ModuleCat.coextendScalars (conjugateValue e d f),
      α.hom = coextensionMateValue.{a} e d f ∧
      (∀ (M : ModuleCat.{max a s} R) (φ : (ModuleCat.coextendScalars f).obj M) (b : B),
        ModuleCat.CoextendScalars.equiv (conjugateValue e d f)
            ((moduleEquivalenceValue e).functor.obj M) (α.hom.app M φ)
            (show (ModuleCat.restrictScalars (conjugateValue e d f)).obj (ModuleCat.of B B) from b) =
          ModuleCat.CoextendScalars.equiv f M φ
            (show (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) from d.symm b)) ∧
      adjunctionCompatible (ModuleCat.restrictCoextendScalarsAdj.{a} f)
        (ModuleCat.restrictCoextendScalarsAdj.{max a s} (conjugateValue e d f))
        (restrictionIsoValue e d f).inv α.hom

end Adjunctions

section SmallExtendingRing

variable {R : Type u} {S : Type s} {A B : Type a}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S)

/-- Restriction along the represented map agrees with restriction along the original map. -/
def representedRestriction :
    (moduleEquivalenceValue d).functor ⋙ restrictScalarsValue.{a} (d.toRingHom.comp f) ≅
      restrictScalarsValue.{a} f :=
  (ModuleCat.restrictScalarsComp' (d.toRingHom.comp f) d.symm.toRingHom f (by
    ext r
    exact (d.symm_apply_apply (f r)).symm)).symm

/-- The extension tensor uses the carrier of the extending ring's representative. -/
abbrev representedExtension : ModuleCat.{a} R ⥤ ModuleCat.{a} S :=
  ModuleCat.extendScalars.{u, a, a} (d.toRingHom.comp f) ⋙ (moduleEquivalenceValue d).inverse

/-- The coextension functions use the carrier of the extending ring's representative. -/
abbrev representedCoextension : ModuleCat.{a} R ⥤ ModuleCat.{a} S :=
  ModuleCat.coextendScalars.{u, a, a} (d.toRingHom.comp f) ⋙ (moduleEquivalenceValue d).inverse

def representedExtensionAdjunction : representedExtension d f ⊣ restrictScalarsValue.{a} f :=
  ((ModuleCat.extendRestrictScalarsAdj.{a} (d.toRingHom.comp f)).comp
    (moduleEquivalenceValue d).toAdjunction').ofNatIsoRight (representedRestriction d f)

def representedCoextensionAdjunction : restrictScalarsValue.{a} f ⊣ representedCoextension d f :=
  ((moduleEquivalenceValue d).toAdjunction.comp
    (ModuleCat.restrictCoextendScalarsAdj.{a} (d.toRingHom.comp f))).ofNatIsoLeft
      (representedRestriction d f)

def representedExtensionMateType : Prop :=
  ∀ {R : Type u} {S : Type s} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S),
    ∃ α : representedExtension d f ⋙ (moduleEquivalenceValue d).functor ≅
        (moduleEquivalenceValue e).functor ⋙ ModuleCat.extendScalars (conjugateValue e d f),
      α.inv = (mateEquiv (representedExtensionAdjunction d f)
        (ModuleCat.extendRestrictScalarsAdj.{a} (conjugateValue e d f))).symm
          (restrictionIsoValue e d f).hom ∧
      (∀ (M : ModuleCat.{a} R) (b : S) (x : M),
        α.hom.app M (d b ⊗ₜ[R,d.toRingHom.comp f] x) =
          (d b ⊗ₜ[A,conjugateValue e d f] (show (moduleEquivalenceValue e).functor.obj M from x) :
            (ModuleCat.extendScalars (conjugateValue e d f)).obj
              ((moduleEquivalenceValue e).functor.obj M))) ∧
      adjunctionCompatible (representedExtensionAdjunction d f)
        (ModuleCat.extendRestrictScalarsAdj.{a} (conjugateValue e d f))
        α.inv (restrictionIsoValue e d f).hom

def representedCoextensionMateType : Prop :=
  ∀ {R : Type u} {S : Type s} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S),
    ∃ α : representedCoextension d f ⋙ (moduleEquivalenceValue d).functor ≅
        (moduleEquivalenceValue e).functor ⋙ ModuleCat.coextendScalars (conjugateValue e d f),
      α.hom = mateEquiv (representedCoextensionAdjunction d f)
        (ModuleCat.restrictCoextendScalarsAdj.{a} (conjugateValue e d f))
          (restrictionIsoValue e d f).inv ∧
      (∀ (M : ModuleCat.{a} R) (φ : (representedCoextension d f).obj M) (b : B),
        ModuleCat.CoextendScalars.equiv (conjugateValue e d f)
            ((moduleEquivalenceValue e).functor.obj M) (α.hom.app M φ)
            (show (ModuleCat.restrictScalars (conjugateValue e d f)).obj (ModuleCat.of B B) from b) =
          ModuleCat.CoextendScalars.equiv (d.toRingHom.comp f) M φ
            (show (ModuleCat.restrictScalars (d.toRingHom.comp f)).obj (ModuleCat.of B B)
              from d (d.symm b))) ∧
      adjunctionCompatible (representedCoextensionAdjunction d f)
        (ModuleCat.restrictCoextendScalarsAdj.{a} (conjugateValue e d f))
        (restrictionIsoValue e d f).inv α.hom

end SmallExtendingRing

def uliftActionType : Prop :=
  ∀ (R : Type u) [Ring R] (M : ModuleCat.{max u a} R) (r : ULift.{a} R)
    (x : (moduleEquivalenceValue (uliftRingEquivValue R)).functor.obj M),
    r • x = r.down • (show M from x)

def uliftConjugateType : Prop :=
  ∀ {R : Type u} {S : Type s} [CommRing R] [CommRing S] (f : R →+* S)
    (r : ULift.{max s a} R),
    conjugateValue (uliftRingEquivValue R) (uliftRingEquivValue S) f r =
      (ULift.up (f r.down) : ULift.{max u a} S)

end
end Specs.DerivedFormalization.CochainRingTransport
