import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedPrimesInterface
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
Independent statements for the support assertions of Theorem 5.4
(paper.tex:984–990), including the minimal-prime finiteness consequence.
Associated primes are exact annihilators, and support consists of primes
with nonzero localization, as in the shared source interface. Minimality
uses inclusion of prime ideals. The zero ring and zero module are allowed.
-/
namespace P103.Specs.Ch05.SupportGeometry

open P103.Specs.Ch05.AssociatedPrimesInterface
universe u v

def support_eq_zeroLocusType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    supportValue R M = PrimeSpectrum.zeroLocus (Module.annihilator R M : Set R)

def associatedPrimes_subset_supportType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    {p : PrimeSpectrum R | p.asIdeal ∈ associatedPrimesValue R M} ⊆ supportValue R M

def minimal_support_associatedType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : PrimeSpectrum R),
    Minimal (· ∈ supportValue R M) p → p.asIdeal ∈ associatedPrimesValue R M

/-- An equivalent ideal-valued form, convenient for specializing to M = R. -/
def minimalPrimes_annihilator_subset_associatedPrimesType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    (Module.annihilator R M).minimalPrimes ⊆ associatedPrimesValue R M

/-- The boundary assertion holds without either finiteness hypothesis. -/
def zero_moduleType : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M],
    Module.annihilator R M = ⊤ ∧
      supportValue R M = ∅ ∧ associatedPrimesValue R M = ∅

def minimalPrimes_finiteType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    (minimalPrimes R).Finite

end P103.Specs.Ch05.SupportGeometry
