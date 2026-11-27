import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels

namespace Specs.DerivedFormalization.StrictInjectiveExtension

open CategoryTheory
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainModels (isKInjectiveValue)

universe u v

/-- Every cochain map into a termwise injective K-injective complex extends
across a termwise monic quasi-isomorphism. -/
def strictInjectiveExtensionType : Prop :=
  ∀ {R : Type u} [CommRing R] {X J I : compValue.{v} R} (i : X ⟶ J),
    (∀ n : ℤ, Mono (i.f n)) → QuasiIso i →
    isKInjectiveValue I → (∀ n : ℤ, Injective (I.X n)) →
    ∀ f : X ⟶ I, ∃ g : J ⟶ I, i ≫ g = f

end Specs.DerivedFormalization.StrictInjectiveExtension
