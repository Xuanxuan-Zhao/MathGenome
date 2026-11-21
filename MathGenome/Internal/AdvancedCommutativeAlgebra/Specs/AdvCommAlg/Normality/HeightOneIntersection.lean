import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! SN-08: all intersections are taken as subrings of the chosen fraction field.
Normality is the chapter's local normality predicate. -/
universe u v
namespace AdvCommAlg.Normality.Specs

/-- The canonical embedding A_p → Frac(A) → K. -/
noncomputable def atPrimeToFractionFieldValue
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : PrimeSpectrum A) : Localization.AtPrime p.asIdeal →+* K :=
  (IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) K).toRingHom.comp
    (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A))

def atPrimeToFractionFieldType :=
  ∀ (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : PrimeSpectrum A), Localization.AtPrime p.asIdeal →+* K

def heightOne_intersectionType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K],
    IsNormalValue A → 0 < ringKrullDim A →
    (algebraMap A K).range =
      ⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        (atPrimeToFractionFieldValue A K p).range

end AdvCommAlg.Normality.Specs
