import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Artinian.Defs

/-! Independent specifications for the product assertion in SN-04.
The index is the full set of minimal primes, including the empty set for a zero ring.
-/
universe u
namespace AdvCommAlg.Normality

abbrev MinimalPrime (A : Type u) [CommRing A] :=
  {p : Ideal A // p ∈ minimalPrimes A}

instance {A : Type u} [CommRing A] (p : MinimalPrime A) : p.val.IsPrime :=
  p.property.isPrime

abbrev MinimalFraction (A : Type u) [CommRing A] (p : MinimalPrime A) :=
  FractionRing (A ⧸ p.val)

namespace Specs

def nonZeroDivisors_iff_avoids_minimalPrimesType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A] (a : A),
    a ∈ nonZeroDivisors A ↔ ∀ p ∈ minimalPrimes A, a ∉ p

def finite_minimalPrime_familyType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A], Finite (MinimalPrime A)

def totalQuotient_zeroDimensionalType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A],
    Ring.KrullDimLE 0 (FractionRing A)

def totalQuotient_artinianType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A],
    IsArtinianRing (FractionRing A)

/-- Compatibility on `A` specifies the canonical isomorphism uniquely. -/
def existsUnique_totalQuotientEquivType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A],
    ∃! e : FractionRing A ≃+* (∀ p : MinimalPrime A, MinimalFraction A p),
      ∀ (a : A) (p : MinimalPrime A),
        e (algebraMap A (FractionRing A) a) p =
          algebraMap (A ⧸ p.val) (MinimalFraction A p) (Ideal.Quotient.mk p.val a)

def exists_localization_minimalPrime_equivType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A] (p : MinimalPrime A),
    ∃ e : Localization.AtPrime p.val ≃+* MinimalFraction A p,
      ∀ a : A, e (algebraMap A (Localization.AtPrime p.val) a) =
        algebraMap (A ⧸ p.val) (MinimalFraction A p) (Ideal.Quotient.mk p.val a)

def minimalPrimes_empty_of_subsingletonType : Prop :=
  ∀ (A : Type u) [CommRing A] [Subsingleton A], IsEmpty (MinimalPrime A)

def minimalFraction_product_subsingletonType : Prop :=
  ∀ (A : Type u) [CommRing A] [Subsingleton A],
    Subsingleton (∀ p : MinimalPrime A, MinimalFraction A p)

end Specs
end AdvCommAlg.Normality
