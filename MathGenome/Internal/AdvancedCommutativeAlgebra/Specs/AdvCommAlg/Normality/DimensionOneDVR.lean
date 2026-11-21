import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
Independent statements for SN-06, paper.tex:4175–4218.
The dimension is Krull dimension. Regularity uses the standard Noetherian
local-ring definition, and units in the factorizations belong to A itself.
The generator π is universally quantified; only its exponent is asserted unique.
-/
namespace Specs.AdvCommAlg.Normality

def DimensionOneDVREquivalences : Prop :=
  ∀ (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    ringKrullDim A = 1 →
    (IsIntegrallyClosed A ↔ IsRegularLocalRing A) ∧
    (IsRegularLocalRing A ↔ IsDiscreteValuationRing A)

def DimensionOneFractionalFactorization : Prop :=
  ∀ (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsIntegrallyClosed A], ringKrullDim A = 1 →
    ∀ (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
      (π : A), IsLocalRing.maximalIdeal A = Ideal.span {π} →
      ∀ z : K, z ≠ 0 →
        ∃! n : ℤ, ∃ u : Aˣ,
          z = algebraMap A K (u : A) * (algebraMap A K π) ^ n

def DimensionOneIntegralFactorization : Prop :=
  ∀ (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsIntegrallyClosed A], ringKrullDim A = 1 →
    ∀ (π : A), IsLocalRing.maximalIdeal A = Ideal.span {π} →
      ∀ a : A, a ≠ 0 → ∃! n : ℕ, ∃ u : Aˣ, a = (u : A) * π ^ n

/-- The integer exponent of a nonzero ring element is nonnegative, even when
its factorization is initially presented in the fraction field. -/
def DimensionOneFractionalExponentNonnegative : Prop :=
  ∀ (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsIntegrallyClosed A], ringKrullDim A = 1 →
    ∀ (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
      (π : A), IsLocalRing.maximalIdeal A = Ideal.span {π} →
      ∀ a : A, a ≠ 0 → ∀ (n : ℤ) (u : Aˣ),
        algebraMap A K a = algebraMap A K (u : A) * (algebraMap A K π) ^ n → 0 ≤ n

end Specs.AdvCommAlg.Normality
