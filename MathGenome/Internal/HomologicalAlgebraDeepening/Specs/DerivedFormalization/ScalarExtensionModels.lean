import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Degreewise change of scalars preserves the two classes of cochain models. -/

namespace Specs.DerivedFormalization.ScalarExtensionModels

open CategoryTheory
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainModels (isKFlatValue isKProjectiveValue)

universe u w v
set_option linter.checkUnivs false

def extendScalarsComplexType :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S],
    (R →+* S) → compValue.{max w v} R ⥤ compValue.{max w v} S

noncomputable abbrev extendScalarsComplexValue {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) : compValue.{max w v} R ⥤ compValue.{max w v} S :=
  (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)

def restrict_acyclic_iffType : Prop :=
  ∀ {R : Type u} {S : Type w} [Ring R] [Ring S] (f : R →+* S) (A : compValue.{v} S),
    (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj A).Acyclic ↔ A.Acyclic

def isKFlat_extendScalarsType : Prop :=
  ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (P : compValue.{u} R),
    isKFlatValue P → isKFlatValue ((extendScalarsComplexValue f).obj P)

def isKProjective_extendScalarsType : Prop :=
  ∀ {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (P : compValue.{max w v} R),
    isKProjectiveValue P → isKProjectiveValue ((extendScalarsComplexValue f).obj P)

end Specs.DerivedFormalization.ScalarExtensionModels
