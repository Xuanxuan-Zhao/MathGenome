import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.RingTheory.Noetherian.Defs

/-! The exactness, radical invariance and extreme cases of sections supported in an ideal. -/

open CategoryTheory CategoryTheory.Limits

namespace Specs.CommutativeAlgebraNotes.IdealTorsionProperties

open Specs.CommutativeAlgebraNotes.IdealTorsion

universe v u

set_option linter.checkUnivs false

/-- Applying the torsion functor to a short exact sequence preserves exactness
at the middle module and injectivity at the first module. -/
def leftExactType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (S : ShortComplex (ModuleCat.{v} R)), S.ShortExact →
      (S.map (idealTorsionFunctor I)).Exact ∧ Mono ((idealTorsionFunctor I).map S.f)

def preservesFiniteLimitsType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    PreservesFiniteLimits (idealTorsionFunctor.{v} I)

def submoduleEqOfRadicalEqType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] {I J : Ideal R}, I.radical = J.radical →
    ∀ (M : Type v) [AddCommGroup M] [Module R M], idealTorsion I M = idealTorsion J M

/-- For equal radicals the natural identification commutes with the inclusions
of both torsion submodules into each module. -/
def inclusionIsoOfRadicalEqType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] {I J : Ideal R}, I.radical = J.radical →
    ∃ e : idealTorsionFunctor.{v} I ≅ idealTorsionFunctor.{v} J,
      e.hom ≫ idealTorsionInclusion J = idealTorsionInclusion I

/-- For the zero ideal the inclusion into the identity functor is an isomorphism. -/
def botInclusionIsIsoType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R],
    IsIso (idealTorsionInclusion.{v} (⊥ : Ideal R))

/-- For the unit ideal the torsion functor is a zero object of the functor category. -/
def topFunctorIsZeroType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R],
    IsZero (idealTorsionFunctor.{v} (⊤ : Ideal R))

end Specs.CommutativeAlgebraNotes.IdealTorsionProperties
