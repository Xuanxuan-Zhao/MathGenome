import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! SN-08, general membership assertion. No reducedness or domain assumption.
The map is localization at the nonzerodivisors followed by prime localization;
its existence uses preservation of nonzerodivisors under localization. -/
universe u
namespace AdvCommAlg.Normality.Specs

noncomputable def totalQuotientToAtPrimeValue (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) : FractionRing A →+*
      FractionRing (Localization.AtPrime p.asIdeal) :=
  IsLocalization.map (FractionRing (Localization.AtPrime p.asIdeal))
    (algebraMap A (Localization.AtPrime p.asIdeal))
    (IsLocalization.nonZeroDivisors_le_comap p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal))

def totalQuotientToAtPrimeType := ∀ (A : Type u) [CommRing A]
    (p : PrimeSpectrum A), FractionRing A →+* FractionRing (Localization.AtPrime p.asIdeal)

def nonZeroDivisor_atPrimeType : Prop := ∀ (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) (b : A), b ∈ nonZeroDivisors A →
      algebraMap A (Localization.AtPrime p.asIdeal) b ∈
        nonZeroDivisors (Localization.AtPrime p.asIdeal)

def totalQuotientToAtPrime_algebraMapType : Prop := ∀ (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) (a : A),
    totalQuotientToAtPrimeValue A p (algebraMap A (FractionRing A) a) =
      algebraMap (Localization.AtPrime p.asIdeal)
        (FractionRing (Localization.AtPrime p.asIdeal))
        (algebraMap A (Localization.AtPrime p.asIdeal) a)

def codimensionOne_membershipType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A],
    CohenMacaulay.Specs.RingSerreConditionValue A 2 →
    ∀ z : FractionRing A,
      (∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 →
        totalQuotientToAtPrimeValue A p z ∈ Set.range
          (algebraMap (Localization.AtPrime p.asIdeal)
            (FractionRing (Localization.AtPrime p.asIdeal)))) →
      z ∈ Set.range (algebraMap A (FractionRing A))

end AdvCommAlg.Normality.Specs
