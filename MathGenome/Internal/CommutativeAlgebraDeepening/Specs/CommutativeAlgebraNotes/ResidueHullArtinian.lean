import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.Noetherian.Defs

namespace Specs.CommutativeAlgebraNotes.ResidueHullArtinian

universe u

/-- The injective hull of the residue field of a Noetherian local ring is Artinian
as a module over that ring. -/
def residueHullArtinianType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs.residueFieldEnvelopeValue R),
    IsArtinian R E.carrier

end Specs.CommutativeAlgebraNotes.ResidueHullArtinian
