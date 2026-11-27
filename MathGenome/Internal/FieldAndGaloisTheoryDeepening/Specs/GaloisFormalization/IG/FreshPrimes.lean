import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Prime.Defs

namespace Specs.GaloisFormalization.IG

/-- Lemma 4.15. Given `n ≥ 2` and a finite set of primes, some prime outside
the set has predecessor divisible by `n`. -/
def FreshPrime : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q) →
    ∃ p : ℕ, Nat.Prime p ∧ p ∉ S ∧ n ∣ p - 1

end Specs.GaloisFormalization.IG
