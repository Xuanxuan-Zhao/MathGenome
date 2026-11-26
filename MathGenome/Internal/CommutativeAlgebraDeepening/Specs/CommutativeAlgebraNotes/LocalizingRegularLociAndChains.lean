import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import Mathlib.RingTheory.Localization.Submodule

universe u v

namespace CommutativeAlgebraNotes.Excellence.Specs

def regularLocus_eq_preimage_of_isLocalizationType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S],
      regularLocusValue S = PrimeSpectrum.comap (algebraMap R S) ⁻¹' regularLocusValue R

def catenary_of_isLocalizationType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S], CatenaryValue R → CatenaryValue S

def j2_of_finiteTypeType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S], J2Value R →
      letI := Algebra.FiniteType.isNoetherianRing R S
      J2Value S

def universallyCatenary_of_finiteTypeType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S], UniversallyCatenaryValue R →
      letI := Algebra.FiniteType.isNoetherianRing R S
      UniversallyCatenaryValue S

def j2_of_isLocalizationType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    (M : Submonoid R) [IsLocalization M S], J2Value R →
      letI := IsLocalization.isNoetherianRing M S (inferInstance : IsNoetherianRing R)
      J2Value S

def universallyCatenary_of_isLocalizationType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    (M : Submonoid R) [IsLocalization M S], UniversallyCatenaryValue R →
      letI := IsLocalization.isNoetherianRing M S (inferInstance : IsNoetherianRing R)
      UniversallyCatenaryValue S

def j2_of_essFiniteTypeType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.EssFiniteType R S], J2Value R →
      letI := Algebra.EssFiniteType.isNoetherianRing R S
      J2Value S

def universallyCatenary_of_essFiniteTypeType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.EssFiniteType R S], UniversallyCatenaryValue R →
      letI := Algebra.EssFiniteType.isNoetherianRing R S
      UniversallyCatenaryValue S

end CommutativeAlgebraNotes.Excellence.Specs
