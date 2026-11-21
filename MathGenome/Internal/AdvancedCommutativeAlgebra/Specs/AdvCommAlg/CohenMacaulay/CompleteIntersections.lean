import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! Independent specifications for the forward assertions of CM-09,
paper.tex:3445–3456. The displayed integer c is represented by the length of
its generating list, and the hypothesis is the equality ht(I) = length(x).
This implies properness, since ht(⊤) = ∞. The localization assertion is stated
at all primes containing I, hence includes all the required maximal ideals.
No positive-length or positive-height assumption excludes the empty list.
-/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def completeIntersection_regular_atPrimeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → ∀ (I : Ideal R) (x : List R),
    Ideal.ofList x = I → I.height = (x.length : ℕ∞) →
    ∀ p : PrimeSpectrum R, I ≤ p.asIdeal →
      RingTheory.Sequence.IsRegular (Localization.AtPrime p.asIdeal)
        (x.map (algebraMap R (Localization.AtPrime p.asIdeal)))

def completeIntersection_cohenMacaulay_moduleType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → ∀ (I : Ideal R) (x : List R),
    Ideal.ofList x = I → I.height = (x.length : ℕ∞) →
      IsCohenMacaulayValue R (R ⧸ I)

def completeIntersection_cohenMacaulayType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → ∀ (I : Ideal R) (x : List R),
    Ideal.ofList x = I → I.height = (x.length : ℕ∞) →
      CohenMacaulayRingValue (R ⧸ I)

def completeIntersection_associated_heightType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → ∀ (I : Ideal R) (x : List R),
    Ideal.ofList x = I → I.height = (x.length : ℕ∞) →
    ∀ p : Ideal R, p ∈ associatedPrimes R (R ⧸ I) →
      p ∈ I.minimalPrimes ∧ p.height = (x.length : ℕ∞)

def completeIntersection_unmixedType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → ∀ (I : Ideal R) (x : List R),
    Ideal.ofList x = I → I.height = (x.length : ℕ∞) →
    ∀ q : Ideal (R ⧸ I), q ∈ associatedPrimes (R ⧸ I) (R ⧸ I) →
      q.comap (Ideal.Quotient.mk I) ∈ I.minimalPrimes ∧
        (q.comap (Ideal.Quotient.mk I)).height = (x.length : ℕ∞)

def regularLocal_quotient_cohenMacaulayType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsRegularLocalRing R]
    (x : List R), (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) →
    RingTheory.Sequence.IsRegular R x → CohenMacaulayRingValue (R ⧸ Ideal.ofList x)

end AdvCommAlg.CohenMacaulay.Specs
