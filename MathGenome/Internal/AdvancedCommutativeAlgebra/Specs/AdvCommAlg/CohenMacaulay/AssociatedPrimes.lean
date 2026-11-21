import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-! Independent specifications for CM-03, paper.tex:3282–3299.
Minimality is stated in the actual support, ordered by inclusion of prime ideals.
The quotient dimensions of all minimal support primes give equidimensionality;
the equality of associated primes with minimal primes over the annihilator
also states the absence of embedded associated primes. -/

universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def dim_quotient_eq_dimension_of_associatedPrimeType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M] [Nontrivial M],
  LocalCohenMacaulayValue R M → ∀ p : Ideal R, p ∈ associatedPrimes R M →
    ringKrullDim (R ⧸ p) = dimensionValue R M

def minimal_support_of_associatedPrimeType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M] [Nontrivial M],
  LocalCohenMacaulayValue R M → ∀ (p : PrimeSpectrum R),
    p.asIdeal ∈ associatedPrimes R M → Minimal (fun q => q ∈ Module.support R M) p

def associatedPrime_of_minimal_supportType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M] [Nontrivial M],
  ∀ (p : PrimeSpectrum R), Minimal (fun q => q ∈ Module.support R M) p →
    p.asIdeal ∈ associatedPrimes R M

def associatedPrimes_eq_minimalPrimes_annihilatorType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M] [Nontrivial M],
  LocalCohenMacaulayValue R M →
    associatedPrimes R M = (Module.annihilator R M).minimalPrimes

def dim_quotient_eq_dimension_of_minimal_supportType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M] [Nontrivial M],
  LocalCohenMacaulayValue R M → ∀ (p : PrimeSpectrum R),
    Minimal (fun q => q ∈ Module.support R M) p →
      ringKrullDim (R ⧸ p.asIdeal) = dimensionValue R M

end AdvCommAlg.CohenMacaulay.Specs
