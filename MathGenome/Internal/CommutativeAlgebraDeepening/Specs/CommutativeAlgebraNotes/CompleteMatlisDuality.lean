import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Artinian.Defs

/-! Matlis duality over a complete Noetherian local ring (M05). -/

noncomputable section

open CategoryTheory Opposite

namespace CommutativeAlgebraNotes.CompleteMatlisDualitySpecs

open MatlisDualFunctorSpecs

universe u v

/-- The full subcategory of finitely generated modules. -/
def finiteModules (R : Type u) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun X => Module.Finite R X

/-- The full subcategory of Artinian modules. -/
def artinianModules (R : Type u) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun X => IsArtinian R X

variable {R : Type u} [CommRing R] [IsLocalRing R]

def dualOfFiniteIsArtinian : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    [IsNoetherianRing R] (X : Type v) [AddCommGroup X] [Module R X]
    [Module.Finite R X], IsArtinian R (matlisDualModuleValue E X)

def dualOfArtinianIsFinite : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (X : Type u) [AddCommGroup X] [Module R X]
    [IsArtinian R X], Module.Finite R (matlisDualModuleValue E X)

def evaluationBijectiveOfFinite : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (X : Type v) [AddCommGroup X] [Module R X]
    [Module.Finite R X], Function.Bijective (matlisEvaluationValue E X)

def evaluationBijectiveOfArtinian : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (X : Type u) [AddCommGroup X] [Module R X]
    [IsArtinian R X], Function.Bijective (matlisEvaluationValue E X)

/-- Restriction of the Matlis dual from finite modules to Artinian modules. -/
def finiteDual (E : residueFieldEnvelopeValue R)
    (h : ∀ X : (finiteModules R).FullSubcategory, IsArtinian R (matlisDualModuleValue E X.obj)) :
    (finiteModules R).FullSubcategoryᵒᵖ ⥤ (artinianModules R).FullSubcategory :=
  (artinianModules R).lift ((finiteModules R).ι.op ⋙ matlisDualValue E) (fun X => h X.unop)

/-- Restriction of the Matlis dual from Artinian modules to finite modules. -/
def artinianDual (E : residueFieldEnvelopeValue R)
    (h : ∀ X : (artinianModules R).FullSubcategory, Module.Finite R (matlisDualModuleValue E X.obj)) :
    (artinianModules R).FullSubcategoryᵒᵖ ⥤ (finiteModules R).FullSubcategory :=
  (finiteModules R).lift ((artinianModules R).ι.op ⋙ matlisDualValue E) (fun X => h X.unop)

/-- The equivalence uses the restricted Matlis duals in both directions. Its inverse unit
on the opposite category and its inverse counit are the two bidual evaluations. The
heterogeneous equalities compare maps whose domains and codomains are identified by the
preceding functor equalities. -/
def completeMatlisDuality : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (E : residueFieldEnvelopeValue R),
    ∃ (hF : ∀ X : (finiteModules R).FullSubcategory, IsArtinian R (matlisDualModuleValue E X.obj))
      (hA : ∀ Y : (artinianModules R).FullSubcategory, Module.Finite R (matlisDualModuleValue E Y.obj))
      (e : (finiteModules R).FullSubcategoryᵒᵖ ≌ (artinianModules R).FullSubcategory),
      e.functor = finiteDual E hF ∧ e.inverse = (artinianDual E hA).rightOp ∧
      (∀ X : (finiteModules R).FullSubcategory,
        HEq (e.unitIso.inv.app (op X)).unop.hom.hom (matlisEvaluationValue E X.obj)) ∧
      (∀ Y : (artinianModules R).FullSubcategory,
        HEq (e.counitIso.inv.app Y).hom.hom (matlisEvaluationValue E Y.obj))

end CommutativeAlgebraNotes.CompleteMatlisDualitySpecs
