import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Support

open CategoryTheory

namespace Specs.CommutativeAlgebraNotes.LocalCohomologyBaseChange

universe u

open IdealTorsion

/-- Restriction of scalars identifies the local cohomology functors. Naturality
in the B-module includes the endomorphisms given by multiplication by b ∈ B. -/
def ChangeOfRings : Prop :=
  ∀ {R B : Type u} [CommRing R] [CommRing B] [IsNoetherianRing R]
    [IsNoetherianRing B] (f : R →+* B) (I : Ideal R) (q : ℤ),
    Nonempty ((ModuleCat.restrictScalars.{u} f ⋙ localCohomology.{u} I q) ≅
      (localCohomology.{u} (I.map f) q ⋙ ModuleCat.restrictScalars.{u} f))

/-- For a flat ring map, the base-change comparison is natural and B-linear. -/
def FlatBaseChange : Prop :=
  ∀ {R B : Type u} [CommRing R] [CommRing B] [IsNoetherianRing R]
    [IsNoetherianRing B] (f : R →+* B), f.Flat → ∀ (I : Ideal R) (q : ℤ),
    Nonempty ((localCohomology.{u} I q ⋙ ModuleCat.extendScalars.{u, u, u} f) ≅
      (ModuleCat.extendScalars.{u, u, u} f ⋙ localCohomology.{u} (I.map f) q))

/-- Local cohomology can be supported only on the original module's support
and on the closed locus of the supporting ideal. -/
def SupportInclusion : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (q : ℤ) (M : ModuleCat.{u} R),
    Module.support R ((localCohomology.{u} I q).obj M) ⊆
      PrimeSpectrum.zeroLocus (I : Set R) ∩ Module.support R M

end Specs.CommutativeAlgebraNotes.LocalCohomologyBaseChange
