import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.SemifreeModels

/-! Result U02, with both homotopical tests on the same semifree replacement. -/

open CategoryTheory

namespace Specs.DerivedFormalization.SemifreeReplacement

open Cochains (compValue)
open CochainModels (isKProjectiveValue isKFlatValue)
open CochainTensor (isKFlat)
open CochainCoefficientLift (lift toOriginal toOriginalCohomology)
open CochainRingTransport (shrinkRingEquivValue uliftRingEquivValue)

universe u v t

/-- Resolve an arbitrary original complex in an ambient that contains the
rank-one free stalk. The mixed maps are induced by the strict augmentation. -/
def AdequateReplacement : Prop :=
  ∀ (R : Type u) [CommRing R] (X : compValue.{v} R),
    let e := uliftRingEquivValue.{max u v t} R
    let jX := (lift.{max u t, v} R).obj X
    ∃ (F : compValue.{max u v t} R) (p : F ⟶ jX),
      QuasiIso p ∧
      (∀ i, Function.Surjective (p.f i)) ∧
      Nonempty (SemifreeFiltrationTransport.Filtration e F) ∧
      isKProjectiveValue F ∧ isKFlat F ∧
      (∀ i, Function.Surjective ((toOriginal.{max u t, v} p).f i)) ∧
      (∀ i, Function.Bijective (toOriginalCohomology.{max u t, v} p i))

/-- Resolve the original complex directly whenever the ring has a carrier
representative at the original coefficient level. Both tests use this level. -/
def NativeReplacement : Prop :=
  ∀ (R : Type u) [CommRing R] [Small.{v} R] (X : compValue.{v} R),
    ∃ (F : compValue.{v} R) (p : F ⟶ X),
      QuasiIso p ∧
      (∀ i, Function.Surjective (p.f i)) ∧
      Nonempty (SemifreeFiltrationTransport.Filtration (shrinkRingEquivValue.{v} R) F) ∧
      isKProjectiveValue F ∧ isKFlat F

/-- The replacement in the diagonal cochain category, with its native free
stalk and signed tensor. -/
def DiagonalReplacement : Prop :=
  ∀ (R : Type u) [CommRing R] (X : compValue.{u} R),
    ∃ (F : compValue.{u} R) (p : F ⟶ X),
      QuasiIso p ∧
      (∀ i, Function.Surjective (p.f i)) ∧
      Nonempty (SemifreeFiltration.Filtration F) ∧
      isKProjectiveValue F ∧ isKFlatValue F

end Specs.DerivedFormalization.SemifreeReplacement
