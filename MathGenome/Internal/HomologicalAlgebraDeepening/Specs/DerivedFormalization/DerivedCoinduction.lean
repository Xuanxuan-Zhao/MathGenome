import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CoinductionComplex

/-! Derived coinduction along maps of commutative rings. -/

namespace Specs.DerivedFormalization.DerivedCoinduction

open CategoryTheory
open Cochains (compValue derivedValue qValue)
open CochainModels (isKInjectiveValue)
open CoinductionComplex (coinduceValue evaluationValue restrictionComp)
open DerivedRestriction (derivedRestrictScalarsValue derivedRestrictScalarsFactorsValue
  restrictScalarsComplexValue)

universe v u w t

attribute [local instance] HasDerivedCategory.standard

set_option linter.checkUnivs false

noncomputable section

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)

/-- The derived morphism represented by evaluation at one of the coinduced complex. -/
def evaluation (I : compValue.{max v w} A) :
    (derivedRestrictScalarsValue f).obj ((qValue B).obj ((coinduceValue.{v} f).obj I)) ⟶
      (qValue A).obj I :=
  (derivedRestrictScalarsFactorsValue f).hom.app ((coinduceValue.{v} f).obj I) ≫
    (qValue A).map (evaluationValue.{v} f I)

/-- The canonical comparison from the cochain model, given by transposing evaluation. -/
def comparison {G : derivedValue.{max v w} A ⥤ derivedValue.{max v w} B}
    (adj : derivedRestrictScalarsValue f ⊣ G) (I : compValue.{max v w} A) :
    (qValue B).obj ((coinduceValue.{v} f).obj I) ⟶ G.obj ((qValue A).obj I) :=
  adj.homEquiv _ _ (evaluation.{v} f I)

/-- A derived right adjoint to restriction, with its canonical computation on all
K-injective models. The computation property uses evaluation for this same adjunction. -/
structure Coinduction where
  functor : derivedValue.{max v w} A ⥤ derivedValue.{max v w} B
  adjunction : derivedRestrictScalarsValue f ⊣ functor
  comparison_isIso : ∀ (I : compValue.{max v w} A), isKInjectiveValue I →
    IsIso (comparison.{v} f adjunction I)

/-- A right adjoint exists for each ring map. The module universe contains
both ring universes, as in the unbounded K-injective replacement theorem. -/
def existenceType : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B),
    Nonempty (Coinduction.{max u v} f)

/-- Compute the right adjoint using any K-injective replacement of a derived object. -/
def Coinduction.modelIso (G : Coinduction.{v} f) {Y : derivedValue.{max v w} A}
    (I : compValue.{max v w} A) (i : Y ≅ (qValue A).obj I) (hI : isKInjectiveValue I) :
    G.functor.obj Y ≅ (qValue B).obj ((coinduceValue.{v} f).obj I) :=
  haveI := G.comparison_isIso I hI
  G.functor.mapIso i ≪≫ (asIso (comparison.{v} f G.adjunction I)).symm

/-- With this computation the counit is the localized evaluation map, transported
along the replacement. -/
theorem Coinduction.modelCounit (G : Coinduction.{v} f) {Y : derivedValue.{max v w} A}
    (I : compValue.{max v w} A) (i : Y ≅ (qValue A).obj I) (hI : isKInjectiveValue I) :
    (derivedRestrictScalarsValue f).map (G.modelIso f I i hI).inv ≫ G.adjunction.counit.app Y =
      evaluation.{v} f I ≫ i.inv := by
  have := G.comparison_isIso I hI
  have h := G.adjunction.homEquiv_counit
    (X := (qValue B).obj ((coinduceValue.{v} f).obj I)) (Y := (qValue A).obj I)
    (g := comparison.{v} f G.adjunction I)
  rw [show (G.adjunction.homEquiv _ _).symm (comparison.{v} f G.adjunction I) =
    evaluation.{v} f I from Equiv.symm_apply_apply _ _] at h
  change (derivedRestrictScalarsValue f).map
    (comparison.{v} f G.adjunction I ≫ G.functor.map i.inv) ≫ _ = _
  have hn := G.adjunction.counit.naturality i.inv
  change (derivedRestrictScalarsValue f).map (G.functor.map i.inv) ≫ _ =
    G.adjunction.counit.app ((qValue A).obj I) ≫ i.inv at hn
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, ← h]

variable {C : Type t} [CommRing C] (g : B →+* C)

/-- The derived restriction comparison obtained by localizing the cochain comparison. -/
def restrictionComposition :
    derivedRestrictScalarsValue.{max v w t} (g.comp f) ≅
      derivedRestrictScalarsValue g ⋙ derivedRestrictScalarsValue f :=
  Localization.liftNatIso (qValue.{max v w t} C)
    (HomologicalComplex.quasiIso (ModuleCat.{max v w t} C) (.up ℤ))
    (restrictScalarsComplexValue (g.comp f) ⋙ qValue A)
    (restrictScalarsComplexValue g ⋙ restrictScalarsComplexValue f ⋙ qValue A)
    _ _ (Functor.isoWhiskerRight (restrictionComp.{v} f g) _ ≪≫ Functor.associator _ _ _)

/-- The two derived right adjoints compose naturally. This comparison intertwines
their counits on every object with the successive counits. -/
def compositionType : Prop :=
  ∀ {A : Type u} {B : Type w} {C : Type t} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (F : Coinduction.{max v w t} f) (G : Coinduction.{max v w t} g)
    (H : Coinduction.{max v w t} (g.comp f)),
    ∃ e : F.functor ⋙ G.functor ≅ H.functor,
      ∀ Y : derivedValue.{max v w t} A,
        (derivedRestrictScalarsValue (g.comp f)).map (e.hom.app Y) ≫ H.adjunction.counit.app Y =
          (restrictionComposition.{v} f g).hom.app ((F.functor ⋙ G.functor).obj Y) ≫
          (derivedRestrictScalarsValue f).map (G.adjunction.counit.app (F.functor.obj Y)) ≫
          F.adjunction.counit.app Y

end

end Specs.DerivedFormalization.DerivedCoinduction
