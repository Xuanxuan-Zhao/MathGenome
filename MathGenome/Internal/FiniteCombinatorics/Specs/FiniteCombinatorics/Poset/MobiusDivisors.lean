import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.MobiusInverse
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! Independent statements for the divisor specialization in `paper.tex`, p204:W09.
The order is divisibility, and membership in `N.divisors` ensures positivity.
Functions in arithmetic inversion are unrestricted at zero, which is never tested. -/
noncomputable section
open Classical

namespace FiniteCombinatorics.Poset

/-- Positive divisors of `N`; for `N = 0` this type is empty. -/
def DivisorPoset (N : ℕ) := {d : ℕ // d ∈ N.divisors}

instance (N : ℕ) : Fintype (DivisorPoset N) :=
  inferInstanceAs (Fintype {d : ℕ // d ∈ N.divisors})

instance (N : ℕ) : PartialOrder (DivisorPoset N) where
  le a b := a.val ∣ b.val
  le_refl _ := dvd_rfl
  le_trans _ _ _ := dvd_trans
  le_antisymm a b h₁ h₂ := Subtype.ext (Nat.dvd_antisymm h₁ h₂)

end FiniteCombinatorics.Poset

open scoped FiniteCombinatorics.Poset
namespace Specs.FiniteCombinatorics.Poset.MobiusDivisors
open _root_.FiniteCombinatorics.Poset

/-- Integer incidence Möbius values on every comparable divisor pair. -/
def IntegerFormula : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (a b : DivisorPoset N), a ≤ b →
    MobiusInverse.mobiusValue ℤ (DivisorPoset N) a b =
      ArithmeticFunction.moebius (b.val / a.val)

/-- The same formula after the canonical coefficient map into any commutative ring. -/
def CoefficientFormula : Prop :=
  ∀ (R : Type*) [CommRing R] (N : ℕ), 0 < N →
    ∀ (a b : DivisorPoset N), a ≤ b →
      MobiusInverse.mobiusValue R (DivisorPoset N) a b =
        (ArithmeticFunction.moebius (b.val / a.val) : R)

/-- Both directions of the usual divisor inversion, with precisely the positive domain. -/
def DivisorInversion : Prop :=
  ∀ (R : Type*) [CommRing R] (f g : ℕ → R),
    (∀ n > 0, g n = ∑ d ∈ n.divisors, f d) ↔
    (∀ n > 0, f n = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius (n / d) : R) * g d)

end Specs.FiniteCombinatorics.Poset.MobiusDivisors
