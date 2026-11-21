import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.NatAntidiagonal

/-!
Independent specification of the divided-power paragraph of K05.15.normalization
(paper.tex:3045–3050). The algebra may be noncommutative and of any dimension.
Division by a scalar is represented by multiplication by its inverse via scalar
action; these are ordinary powers with factorial normalization.
-/
noncomputable section

namespace D05.Specs.M15.Normalization.DividedPowers

/-- The convention `u^[n] = u^n / n!`, including the nullary power. -/
def dividedPowerType := ∀ (K A : Type*) [Field K] [Ring A] [Algebra K A], A → ℕ → A

def dividedPowerValue : dividedPowerType :=
  fun K _ _ _ _ u n => (n.factorial : K)⁻¹ • u ^ n

/-- Degree zero is the unit and degree one is the original element. -/
def boundaryDegrees : Prop :=
  ∀ (K A : Type*) [Field K] [CharZero K] [Ring A] [Algebra K A] (u : A),
    dividedPowerValue K A u 0 = 1 ∧ dividedPowerValue K A u 1 = u

/-- Products of divided powers of a single element. No commutativity of A is assumed. -/
def dividedPower_mul : Prop :=
  ∀ (K A : Type*) [Field K] [CharZero K] [Ring A] [Algebra K A]
    (u : A) (r s : ℕ),
    dividedPowerValue K A u r * dividedPowerValue K A u s =
      ((r + s).choose r : K) • dividedPowerValue K A u (r + s)

/-- The sum ranges over exactly the nonnegative pairs r+s=k.
The commuting hypothesis is necessary for an arbitrary unital algebra. -/
def dividedPower_add : Prop :=
  ∀ (K A : Type*) [Field K] [CharZero K] [Ring A] [Algebra K A]
    (u v : A), Commute u v → ∀ k : ℕ,
    dividedPowerValue K A (u + v) k =
      ∑ rs ∈ Finset.antidiagonal k,
        dividedPowerValue K A u rs.1 * dividedPowerValue K A v rs.2

end D05.Specs.M15.Normalization.DividedPowers
