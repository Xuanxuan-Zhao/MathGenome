import Mathlib.Data.Int.Basic

/-! Independent statements of Theorem 4.2 (`nt:D02`) in `paper.tex`. -/

namespace P203Specs.Ch04.FermatFour

/-- No sum of two nonzero integer fourth powers is an integer square. -/
def fourthPowersNotSquare : Prop :=
  ∀ (x y z : ℤ), x ≠ 0 → y ≠ 0 → x ^ 4 + y ^ 4 ≠ z ^ 2

/-- The exponent-four consequence, with precisely the source's `xy ≠ 0` condition. -/
def fourthPowersNotFourthPower : Prop :=
  ∀ (x y z : ℤ), x * y ≠ 0 → x ^ 4 + y ^ 4 ≠ z ^ 4

end P203Specs.Ch04.FermatFour
