import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels

namespace Specs.DerivedFormalization.KInjectiveReplacement

open CategoryTheory
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainModels (isKInjectiveValue)

universe u v

/-- Every unbounded cochain complex over a commutative ring has a termwise monic
quasi-isomorphism to a K-injective complex of injective modules.
The module universe is taken to contain the ring universe. -/
def replacementType : Prop :=
  ∀ {R : Type u} [CommRing R] (X : compValue.{max u v} R),
    ∃ (I : compValue.{max u v} R) (f : X ⟶ I),
      (∀ j : ℤ, Mono (f.f j)) ∧ QuasiIso f ∧ isKInjectiveValue I ∧
        ∀ j : ℤ, Injective (I.X j)

end Specs.DerivedFormalization.KInjectiveReplacement
