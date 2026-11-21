import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SerreDepthConditions
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! Independent specifications for SN-01 (paper.tex:4037–4059).

The chapter assumes Noetherian rings throughout. The module and ring `(S_j)`
conditions are exactly the predicates specified in
`AdvCommAlg.CohenMacaulay.Specs.SerreConditionValue` and
`AdvCommAlg.CohenMacaulay.Specs.RingSerreConditionValue`; no new depth predicate
is introduced here. Normality includes the domain requirement at each prime.
-/
universe u
namespace AdvCommAlg.Normality.Specs

def RegularInCodimensionType :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A], ℕ → Prop

noncomputable def RegularInCodimensionValue : RegularInCodimensionType.{u} :=
  fun A _ _ j => ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ (j : ℕ∞) →
    IsRegularLocalRing (Localization.AtPrime p.asIdeal)

def IsNormalType := ∀ (A : Type u) [CommRing A] [IsNoetherianRing A], Prop

def IsNormalValue : IsNormalType.{u} :=
  fun A _ _ => ∀ p : PrimeSpectrum A,
    IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal)

def TotalQuotientRingType :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A], Type u

/-- The multiplicative set consists of all nonzerodivisors, even when `A`
is not a domain. -/
def TotalQuotientRingValue : TotalQuotientRingType.{u} :=
  fun A _ _ => Localization (nonZeroDivisors A)

def regularInCodimension_iffType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (j : ℕ),
    RegularInCodimensionValue A j ↔
      ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ (j : ℕ∞) →
        IsRegularLocalRing (Localization.AtPrime p.asIdeal)

def isNormal_iffType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A],
    IsNormalValue A ↔ ∀ p : PrimeSpectrum A,
      IsDomain (Localization.AtPrime p.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal)

def isNormal_of_subsingletonType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [Subsingleton A],
    IsNormalValue A

end AdvCommAlg.Normality.Specs
