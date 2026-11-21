import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.QuadraticContinuedFractions
import Mathlib.Algebra.Ring.Int.Defs

/-! The signed-denominator surd recurrence in paper.tex,
`lem:nt-reduced-step` and `eq:nt-cf-surd-step` (lines 2424–2432).
The updates are integer-valued; exactness of integer division is a conclusion.
No reducedness or positivity assumption on Q is imposed. -/
namespace P203Specs

/-- The next integer numerator parameter, using the floor of the current surd. -/
noncomputable def surdNextP (P Q D : ℤ) : ℤ :=
  ⌊((P : ℝ) + Real.sqrt (D : ℝ)) / (Q : ℝ)⌋ * Q - P

/-- The next integer denominator parameter. On admissible states this division
is exact, as asserted by `SurdRecurrence`. -/
noncomputable def surdNextQ (P Q D : ℤ) : ℤ :=
  (D - surdNextP P Q D ^ 2) / Q

def SurdUpdateType := ℤ → ℤ → ℤ → ℤ

/-- The full recurrence, including nonvanishing, exactness and preservation of
the divisibility condition. Nonsquare means not a square of any integer. -/
def SurdRecurrence : Prop :=
  ∀ (P Q D : ℤ), 0 < D → ¬ IsSquare D → Q ≠ 0 → Q ∣ D - P ^ 2 →
    surdNextQ P Q D ≠ 0 ∧
    Q * surdNextQ P Q D = D - surdNextP P Q D ^ 2 ∧
    surdNextQ P Q D ∣ D - surdNextP P Q D ^ 2 ∧
    continuedFractionStep (((P : ℝ) + Real.sqrt (D : ℝ)) / (Q : ℝ)) =
      ((surdNextP P Q D : ℝ) + Real.sqrt (D : ℝ)) / (surdNextQ P Q D : ℝ)

end P203Specs
