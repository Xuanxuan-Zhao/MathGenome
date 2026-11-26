import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! The first two assertions of Lemma 5.2 of Topics in Commutative Algebra. -/

universe u

namespace CommutativeAlgebraNotes.Specs

/-- Regularity ascends along a flat local map from a regular local ring
when the closed fibre is regular local. -/
def flatLocalRegularityAscent : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B],
    IsRegularLocalRing A →
    IsRegularLocalRing (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) →
    IsRegularLocalRing B

/-- Regularity descends along a flat local map of Noetherian local rings. -/
def flatLocalRegularityDescent : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B],
    IsRegularLocalRing B → IsRegularLocalRing A

end CommutativeAlgebraNotes.Specs
