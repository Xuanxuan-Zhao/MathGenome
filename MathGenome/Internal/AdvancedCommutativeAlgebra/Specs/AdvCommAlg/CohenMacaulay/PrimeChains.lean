import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.Ideal.Height
import Mathlib.Order.Preorder.Chain

/-! Independent statements for the prime-chain assertions of CM-07.
A `CovBy` relation series lists primes in increasing order with no prime
strictly between adjacent terms. Its length counts inclusions, so a singleton
has length zero. Catenarity includes existence and uniqueness of the length
of saturated chains in each closed prime interval, and finiteness of arbitrary
chains in that interval (not only finite enumerations). The final statement covers
arbitrary maximal chain sets, by exhibiting their finite saturated enumeration.
-/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

abbrev PrimeChain (R : Type u) [CommRing R] :=
  RelSeries {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q}

def CatenaryType := ∀ (R : Type u) [CommRing R], Prop

def CatenaryValue : CatenaryType.{u} := fun R _ =>
  (∀ p q : PrimeSpectrum R, p ≤ q → ∀ S : Set (Set.Icc p q),
    IsChain (· ≤ ·) S → S.Finite) ∧
  ∀ p q : PrimeSpectrum R, p ≤ q →
    ∃ c : PrimeChain R, c.head = p ∧ c.last = q ∧
      ∀ d : PrimeChain R, d.head = p → d.last = q → d.length = c.length

def height_add_one_of_covByType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → ∀ p q : PrimeSpectrum R, p ⋖ q →
      p.asIdeal.height + 1 = q.asIdeal.height

def saturated_chain_lengthType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → ∀ c : PrimeChain R,
      (c.length : ℕ∞) + c.head.asIdeal.height = c.last.asIdeal.height

def catenaryType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    CohenMacaulayRingValue R → CatenaryValue R

def maximal_chain_localType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    CohenMacaulayRingValue R → ∀ S : Set (PrimeSpectrum R),
      IsMaxChain (· ≤ ·) S →
        ∃ c : PrimeChain R, Set.range c = S ∧
          IsMin c.head ∧ c.last.asIdeal = IsLocalRing.maximalIdeal R ∧
          (c.length : WithBot ℕ∞) = ringKrullDim R

end AdvCommAlg.CohenMacaulay.Specs
