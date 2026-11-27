import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Cochains
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Independent specifications for restriction of scalars along a map of commutative rings. -/

namespace Specs.DerivedFormalization.DerivedRestriction

open CategoryTheory CategoryTheory.Pretriangulated
open Specs.DerivedFormalization.Cochains

universe v u w

attribute [local instance] HasDerivedCategory.standard

-- The type-valued specifications keep the two ring universes and the module universe independent.
set_option linter.checkUnivs false

noncomputable section

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)

def restrictScalarsType :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S], (R →+* S) →
    ModuleCat.{v} S ⥤ ModuleCat.{v} R

abbrev restrictScalarsValue : ModuleCat.{v} S ⥤ ModuleCat.{v} R :=
  ModuleCat.restrictScalars f

def restrictScalarsSmulType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{v} S) (r : R) (x : (restrictScalarsValue f).obj M),
    r • x = f r • (show M from x)

def restrictScalarsMapApplyType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    {M N : ModuleCat.{v} S} (g : M ⟶ N) (x : M),
    (restrictScalarsValue f).map g x = g x

def restrictScalarsComplexType :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S], (R →+* S) →
    compValue.{v} S ⥤ compValue.{v} R

abbrev restrictScalarsComplexValue : compValue.{v} S ⥤ compValue.{v} R :=
  (ModuleCat.restrictScalars.{v} f).mapHomologicalComplex (.up ℤ)

def restrictScalarsComplexXType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (X : compValue.{v} S) (i : ℤ),
    ((restrictScalarsComplexValue f).obj X).X i = (restrictScalarsValue f).obj (X.X i)

def restrictScalarsComplexDType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (X : compValue.{v} S) (i j : ℤ),
    ((restrictScalarsComplexValue f).obj X).d i j = (restrictScalarsValue f).map (X.d i j)

def restrictScalarsComplexMapFType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    {X Y : compValue.{v} S} (g : X ⟶ Y) (i : ℤ),
    ((restrictScalarsComplexValue f).map g).f i = (restrictScalarsValue f).map (g.f i)

def restrictScalarsExactType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (C : ShortComplex (ModuleCat.{v} S)), C.Exact → (C.map (restrictScalarsValue f)).Exact

def restrictScalarsComplexShortExactType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (C : ShortComplex (compValue.{v} S)),
    C.ShortExact → (C.map (restrictScalarsComplexValue f)).ShortExact

def restrictScalarsCohomologyIsoType :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S) (i : ℤ),
    restrictScalarsComplexValue.{v} f ⋙ cohomologyValue.{v} R i ≅
      cohomologyValue.{v} S i ⋙ restrictScalarsValue.{v} f

def restrictScalarsCohomologyIsoValue (i : ℤ) :
    restrictScalarsComplexValue.{v} f ⋙ cohomologyValue.{v} R i ≅
      cohomologyValue.{v} S i ⋙ restrictScalarsValue.{v} f :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} S) (.up ℤ) i)
    (ShortComplex.homologyFunctorIso (ModuleCat.restrictScalars.{v} f))

def restrictScalarsComplexQuasiIsoType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    {X Y : compValue.{v} S} (g : X ⟶ Y),
    QuasiIso g → QuasiIso ((restrictScalarsComplexValue f).map g)

def derivedRestrictScalarsType :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S], (R →+* S) →
    derivedValue.{v} S ⥤ derivedValue.{v} R

abbrev derivedRestrictScalarsValue : derivedValue.{v} S ⥤ derivedValue.{v} R :=
  (ModuleCat.restrictScalars.{v} f).mapDerivedCategory

def derivedRestrictScalarsFactorsType :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S),
    qValue.{v} S ⋙ derivedRestrictScalarsValue.{v} f ≅
      restrictScalarsComplexValue.{v} f ⋙ qValue.{v} R

def derivedRestrictScalarsFactorsValue :
    qValue.{v} S ⋙ derivedRestrictScalarsValue.{v} f ≅
      restrictScalarsComplexValue.{v} f ⋙ qValue.{v} R :=
  (ModuleCat.restrictScalars.{v} f).mapDerivedCategoryFactors

def derivedRestrictScalarsFactorsNaturalityType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    {X Y : compValue.{v} S} (g : X ⟶ Y),
    (derivedRestrictScalarsValue f).map ((qValue S).map g) ≫
        (derivedRestrictScalarsFactorsValue f).hom.app Y =
      (derivedRestrictScalarsFactorsValue f).hom.app X ≫
        (qValue R).map ((restrictScalarsComplexValue f).map g)

def derivedRestrictScalarsIsTriangulatedType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S),
    (derivedRestrictScalarsValue.{v} f).IsTriangulated

def derivedRestrictScalarsCohomologyIsoType :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S) (i : ℤ),
    derivedRestrictScalarsValue.{v} f ⋙ derivedCohomologyValue.{v} R i ≅
      derivedCohomologyValue.{v} S i ⋙ restrictScalarsValue.{v} f

def derivedRestrictScalarsCohomologyIsoValue (i : ℤ) :
    derivedRestrictScalarsValue.{v} f ⋙ derivedCohomologyValue.{v} R i ≅
      derivedCohomologyValue.{v} S i ⋙ restrictScalarsValue.{v} f :=
  Localization.liftNatIso (qValue.{v} S) (HomologicalComplex.quasiIso (ModuleCat.{v} S) (.up ℤ))
    _ _ _ _
    (Functor.isoWhiskerRight (derivedRestrictScalarsFactorsValue.{v} f) _ ≪≫
      Functor.isoWhiskerLeft (restrictScalarsComplexValue.{v} f) (cohomologyFactorsValue.{v} R i) ≪≫
      restrictScalarsCohomologyIsoValue.{v} f i ≪≫
      Functor.isoWhiskerRight (cohomologyFactorsValue.{v} S i).symm _)

end

end Specs.DerivedFormalization.DerivedRestriction
