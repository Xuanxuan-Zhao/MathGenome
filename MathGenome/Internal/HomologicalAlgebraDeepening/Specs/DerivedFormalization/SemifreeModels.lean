import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.SemifreeFiltrationTransport

/-! The resolution and K-projectivity assertions of Result U02. -/

open CategoryTheory

namespace Specs.DerivedFormalization.SemifreeModels

open Cochains (compValue)
open CochainModels (isKProjectiveValue)
open CochainCoefficientLift (lift toOriginal toOriginalCohomology)
open CochainRingTransport (shrinkRingEquivValue uliftRingEquivValue)

universe u v t

/-- Every original cochain complex has a resolution at any adequate module
level. Its degree maps to the original complex are the linear components of
`toOriginal p`, which commute with the original differentials. The comparison
on cohomology uses the maps induced by that same augmentation. -/
def AdequateResolution : Prop :=
  ∀ (R : Type u) [CommRing R] (X : compValue.{v} R),
    let e := uliftRingEquivValue.{max u v t} R
    let jX := (lift.{max u t, v} R).obj X
    ∃ (F : compValue.{max u v t} R) (p : F ⟶ jX),
      QuasiIso p ∧
      (∀ i, Function.Surjective (p.f i)) ∧
      Nonempty (SemifreeFiltrationTransport.Filtration e F) ∧
      isKProjectiveValue F ∧
      (∀ i, Function.Surjective ((toOriginal.{max u t, v} p).f i)) ∧
      (∀ i, Function.Bijective (toOriginalCohomology.{max u t, v} p i))

/-- When the original ring has a carrier representative at the original
module level, the strict augmentation and the K-projectivity test can both
be taken in the original cochain category. -/
def NativeResolution : Prop :=
  ∀ (R : Type u) [CommRing R] [Small.{v} R] (X : compValue.{v} R),
    ∃ (F : compValue.{v} R) (p : F ⟶ X),
      QuasiIso p ∧
      (∀ i, Function.Surjective (p.f i)) ∧
      Nonempty (SemifreeFiltrationTransport.Filtration (shrinkRingEquivValue.{v} R) F) ∧
      isKProjectiveValue F

/-- The native assertion on the diagonal, with its usual free rank-one stalk. -/
def DiagonalResolution : Prop :=
  ∀ (R : Type u) [CommRing R] (X : compValue.{u} R),
    ∃ (F : compValue.{u} R) (p : F ⟶ X),
      QuasiIso p ∧
      (∀ i, Function.Surjective (p.f i)) ∧
      Nonempty (SemifreeFiltration.Filtration F) ∧
      isKProjectiveValue F

end Specs.DerivedFormalization.SemifreeModels
