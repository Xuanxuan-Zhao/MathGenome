import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels

namespace Specs.DerivedFormalization.ModelQuasiIsoInvariance

open CategoryTheory
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainModels

universe u v

def tensorMap_quasiIso_of_isKFlatType : Prop :=
  ∀ {R : Type u} [CommRing R] (P : compValue.{u} R) (_hP : isKFlatValue P)
    {X Y : compValue.{u} R} (g : X ⟶ Y), QuasiIso g →
      QuasiIso (tensorMapValue (𝟙 P) g)

def internalHomMap_quasiIso_of_isKProjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (P : compValue.{v} R) (_hP : isKProjectiveValue P)
    {X Y : compValue.{v} R} (g : X ⟶ Y), QuasiIso g →
      QuasiIso (internalHomMapValue (𝟙 P) g)

def internalHomMap_quasiIso_of_isKInjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : compValue.{v} R) (_hI : isKInjectiveValue I)
    {X Y : compValue.{v} R} (g : X ⟶ Y), QuasiIso g →
      QuasiIso (internalHomMapValue g (𝟙 I))

end Specs.DerivedFormalization.ModelQuasiIsoInvariance
