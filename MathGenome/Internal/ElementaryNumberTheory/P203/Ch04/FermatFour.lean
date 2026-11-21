import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.FermatFour
import Mathlib.NumberTheory.FLT.Four

/-! Theorem 4.2 (`nt:D02`): Fermat's descent at exponent four. -/

namespace P203.Ch04.FermatFour

theorem fourthPowersNotSquare : P203Specs.Ch04.FermatFour.fourthPowersNotSquare := by
  intro x y z hx hy
  exact not_fermat_42 hx hy

theorem fourthPowersNotFourthPower :
    P203Specs.Ch04.FermatFour.fourthPowersNotFourthPower := by
  intro x y z hxy h
  have hx : x ≠ 0 := fun hx => hxy (by rw [hx, zero_mul])
  have hy : y ≠ 0 := fun hy => hxy (by rw [hy, mul_zero])
  apply fourthPowersNotSquare x y (z ^ 2) hx hy
  simpa only [← pow_mul] using h

end P203.Ch04.FermatFour
