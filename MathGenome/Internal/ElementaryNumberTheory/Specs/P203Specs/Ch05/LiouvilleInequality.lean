import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Real.Irrational

namespace P203Specs

/-- Liouville's inequality, with `d` the degree over ℚ of the real algebraic
irrational `x` (paper.tex, §5.9, theorem at lines 2543–2550). -/
def LiouvilleInequality : Prop :=
  ∀ (x : ℝ) (d : ℕ), IsAlgebraic ℚ x → Irrational x →
    (minpoly ℚ x).natDegree = d → 2 ≤ d →
    ∃ c : ℝ, 0 < c ∧ ∀ (p q : ℤ), 0 < q → Int.gcd p q = 1 →
      c / (q : ℝ) ^ d ≤ |x - (p : ℝ) / (q : ℝ)|

end P203Specs
