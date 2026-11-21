import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Prime.Defs

namespace P203Specs.Ch03

/-- Theorem 3.12 (`nt:C10`): Bertrand's postulate for all real `x > 1`.
Primes are represented by natural numbers; primality includes positivity. -/
def bertrand : Prop :=
  ∀ x : ℝ, 1 < x → ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) < 2 * x

end P203Specs.Ch03
