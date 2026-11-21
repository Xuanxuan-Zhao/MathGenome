import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.LegendreGauss
import Mathlib.SetTheory.Cardinal.Finite

/-! The unit branches of paper.tex, Theorem nt:B09 (807–816, 839–857).
Roots are residue classes in the ordinary ring `ZMod m`; the integer parameter
is unrestricted in sign. Natural primes encode positive integer primes. -/
namespace P203Specs.Ch02

-- Keep this goal’s local root model separate from the general reduction interface.
namespace UnitQuadratic

/-- The actual set of square roots in the residue ring, with no choice of
integer representative and no additional unit certificate. -/
def QuadraticRoots (m : ℕ) (a : ℤ) := {y : ZMod m // y ^ 2 = (a : ZMod m)}

/-- Number of distinct root classes modulo `m`. -/
noncomputable def quadraticRootCount (m : ℕ) (a : ℤ) : ℕ :=
  Nat.card (QuadraticRoots m a)

end UnitQuadratic

open UnitQuadratic

def OddPrimeUnitRootCount : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (j : ℕ), 1 ≤ j →
    ∀ (a : ℤ), ¬(p : ℤ) ∣ a →
      quadraticRootCount (p ^ j) a = if legendreSymbol a p = 1 then 2 else 0

def TwoUnitRootCount : Prop :=
  ∀ (a : ℤ), ¬(2 : ℤ) ∣ a → quadraticRootCount 2 a = 1

def FourUnitRootCount : Prop :=
  ∀ (a : ℤ), ¬(2 : ℤ) ∣ a →
    quadraticRootCount 4 a = if a ≡ 1 [ZMOD 4] then 2 else 0

def TwoPowerUnitRootCount : Prop :=
  ∀ (j : ℕ), 3 ≤ j → ∀ (a : ℤ), ¬(2 : ℤ) ∣ a →
    quadraticRootCount (2 ^ j) a = if a ≡ 1 [ZMOD 8] then 4 else 0

end P203Specs.Ch02
