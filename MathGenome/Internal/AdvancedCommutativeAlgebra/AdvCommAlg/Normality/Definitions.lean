import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SerreDepthConditions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions

/-! SN-01: Serre's regularity conditions, normality, and total quotients.

All rings in this chapter are Noetherian. For `(S_j)` on finite modules and
rings use the existing `AdvCommAlg.CohenMacaulay.SerreCondition` and
`AdvCommAlg.CohenMacaulay.RingSerreCondition` without alteration.
-/
universe u
namespace AdvCommAlg.Normality

/-- Serre's `(R_j)`: regular local rings at all primes of height at most `j`. -/
noncomputable def RegularInCodimension : Specs.RegularInCodimensionType.{u} :=
  Specs.RegularInCodimensionValue

/-- A normal ring has an integrally closed domain at every prime localization.
This condition is vacuous for the zero ring. -/
def IsNormal : Specs.IsNormalType.{u} := Specs.IsNormalValue

/-- The source's `Q(A)`, the localization at all nonzerodivisors.
This is Mathlib's `FractionRing`, also for rings which are not domains. -/
abbrev TotalQuotientRing (A : Type u) [CommRing A] [IsNoetherianRing A] :=
  FractionRing A

variable (A : Type u) [CommRing A] [IsNoetherianRing A]

theorem regularInCodimension_iff (j : ℕ) :
    RegularInCodimension A j ↔
      ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ (j : ℕ∞) →
        IsRegularLocalRing (Localization.AtPrime p.asIdeal) := Iff.rfl

theorem isNormal_iff :
    IsNormal A ↔ ∀ p : PrimeSpectrum A,
      IsDomain (Localization.AtPrime p.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := Iff.rfl

theorem isNormal_of_subsingleton [Subsingleton A] : IsNormal A := by
  haveI : IsEmpty (PrimeSpectrum A) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mpr inferInstance
  intro p
  exact isEmptyElim p

end AdvCommAlg.Normality
