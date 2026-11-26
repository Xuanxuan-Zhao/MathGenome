import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import Mathlib.RingTheory.Artinian.Defs

/-! Artinianness of maximal-ideal local cohomology and finiteness of its dual (M08). -/

namespace Specs.CommutativeAlgebraNotes.ArtinianLocalCohomology

open IsLocalRing
open IdealTorsion (localCohomology)
open CompletionOfTorsionModules (Completion IsPowerTorsion completionModule completionScalarTower)
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs
  (residueFieldEnvelopeValue matlisDualModuleValue)

universe u v

def localCohomologyArtinianType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (X : ModuleCat.{v} R) [Module.Finite R X] (i : ℤ),
    IsArtinian R ((localCohomology (maximalIdeal R) i).obj X)

/-- The completion acts on the dual by its canonical action on the residue-field hull. -/
def localCohomologyDualFiniteType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (E : residueFieldEnvelopeValue R) (X : ModuleCat.{v} R) [Module.Finite R X] (i : ℤ),
    ∃ hE : IsPowerTorsion R E.carrier,
      letI := completionModule hE
      letI := completionScalarTower hE
      Module.Finite (Completion R)
        (matlisDualModuleValue E ((localCohomology (maximalIdeal R) i).obj X))

end Specs.CommutativeAlgebraNotes.ArtinianLocalCohomology
