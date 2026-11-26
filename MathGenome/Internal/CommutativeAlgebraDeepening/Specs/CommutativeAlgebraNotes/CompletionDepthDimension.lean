import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.Module

/-! Specifications for Proposition 2.4, completion of a finite module over a
Noetherian local ring. -/

open CategoryTheory

namespace Specs.CommutativeAlgebraNotes.CompletionDepthDimension

open CompletionOfTorsionModules (Completion IsPowerTorsion)
open IdealTorsion (localCohomology)
open LocalCohomologyCompletion (adicCompletionFunctor completedAction finiteModules)
open AdvCommAlg.Depth.Specs (depthValue)

universe u

local notation "𝔪[" R "]" => IsLocalRing.maximalIdeal R

def completionNontrivialType : Prop :=
  ∀ (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    Nontrivial (AdicCompletion 𝔪[R] M)

def completionSupportDimType : Prop :=
  ∀ (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    Module.supportDim (Completion R) (AdicCompletion 𝔪[R] M) = Module.supportDim R M

def completionDepthType : Prop :=
  ∀ (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    depthValue (Completion R) (AdicCompletion 𝔪[R] M) = depthValue R M

/-- The completed-linear local cohomology identification is natural on finite
modules, with target support in the extension of the original maximal ideal. -/
def localCohomologyAdicCompletionType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (q : ℤ),
    ∃ h : ∀ M, IsPowerTorsion R ((localCohomology 𝔪[R] q).obj M),
      Nonempty
        ((finiteModules R).ι ⋙ completedAction (localCohomology 𝔪[R] q) h ≅
          (finiteModules R).ι ⋙ adicCompletionFunctor R ⋙
            localCohomology (𝔪[R].map (algebraMap R (Completion R))) q)

end Specs.CommutativeAlgebraNotes.CompletionDepthDimension
