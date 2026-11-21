import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Int.GCD
import Mathlib.Data.Set.Finite.Basic

namespace P203Specs.Ch05.DirichletBoundedDenominators

/-- `paper.tex`, §nt:E05, bounded denominators, with the source's integer parameter. -/
def BoundedDenominators : Prop :=
  ∀ (x : ℝ) (N : ℤ), 1 ≤ N →
    ∃ p q : ℤ, 1 ≤ q ∧ q ≤ N ∧ |(q : ℝ) * x - (p : ℝ)| ≤ 1 / ((N : ℝ) + 1)

/-- The strict version in §nt:E05 for irrational real numbers. -/
def StrictBoundedDenominators : Prop :=
  ∀ (x : ℝ), Irrational x → ∀ (N : ℤ), 1 ≤ N →
    ∃ p q : ℤ, 1 ≤ q ∧ q ≤ N ∧ |(q : ℝ) * x - (p : ℝ)| < 1 / ((N : ℝ) + 1)

/-- Infinitude in §nt:E05: elements of the set are rational values, with
explicit positive, coprime integer numerator/denominator witnesses. -/
def InfiniteReducedApproximations : Prop :=
  ∀ (x : ℝ), Irrational x →
    {r : ℚ | ∃ p q : ℤ, 0 < q ∧ Int.gcd p q = 1 ∧
      r = (p : ℚ) / (q : ℚ) ∧
      |x - (p : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2}.Infinite

end P203Specs.Ch05.DirichletBoundedDenominators
