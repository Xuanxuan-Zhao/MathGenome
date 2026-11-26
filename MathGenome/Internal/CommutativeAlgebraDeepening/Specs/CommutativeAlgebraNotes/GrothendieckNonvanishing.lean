import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Noetherian.Defs

open CategoryTheory

namespace Specs.CommutativeAlgebraNotes.GrothendieckNonvanishing

universe u

/-- A nonzero finite module over a Noetherian local ring has nonzero local
cohomology at the maximal ideal in the Krull dimension of its support.
The witness expresses that dimension as a natural number, including zero. -/
def nonvanishingType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
    ∃ d : ℕ, Module.supportDim R M = (d : WithBot ℕ∞) ∧
      Nontrivial ((IdealTorsion.localCohomology (IsLocalRing.maximalIdeal R) (d : ℤ)).obj M)

end Specs.CommutativeAlgebraNotes.GrothendieckNonvanishing
