import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.FourSquares
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace P203.Ch04.FourSquares

open P203Specs.Ch04.FourSquares (FourVector)

def squaredNorm : FourVector → ℤ := P203Specs.Ch04.FourSquares.squaredNorm

def construction : FourVector → FourVector → FourVector :=
  P203Specs.Ch04.FourSquares.construction

/-- The source's four-square product identity, by polynomial expansion. -/
theorem norm_multiplicative : P203Specs.Ch04.FourSquares.NormMultiplicative := by
  intro A B
  dsimp [P203Specs.Ch04.FourSquares.squaredNorm,
    P203Specs.Ch04.FourSquares.construction]
  ring

/-- Substituting congruent input coordinates preserves every output coordinate. -/
theorem construction_congr (m : ℤ) (A A' B B' : FourVector)
    (hA : ∀ i, A i ≡ A' i [ZMOD m]) (hB : ∀ i, B i ≡ B' i [ZMOD m])
    (i : Fin 4) : construction A B i ≡ construction A' B' i [ZMOD m] := by
  fin_cases i
  · exact (((hA 0).mul (hB 0)).add ((hA 1).mul (hB 1))).add
      ((hA 2).mul (hB 2)) |>.add ((hA 3).mul (hB 3))
  · exact (((hB 0).mul (hA 1)).sub ((hA 0).mul (hB 1))).sub
      (((hA 2).mul (hB 3)).sub ((hA 3).mul (hB 2)))
  · exact (((hB 0).mul (hA 2)).sub ((hA 0).mul (hB 2))).sub
      (((hA 3).mul (hB 1)).sub ((hA 1).mul (hB 3)))
  · exact (((hB 0).mul (hA 3)).sub ((hA 0).mul (hB 3))).sub
      (((hA 1).mul (hB 2)).sub ((hA 2).mul (hB 1)))

/-- At equal inputs the vector part vanishes and the scalar part is the squared norm. -/
theorem construction_self (B : FourVector) :
    construction B B = ![squaredNorm B, 0, 0, 0] := by
  funext i
  fin_cases i <;>
    dsimp [construction, squaredNorm, P203Specs.Ch04.FourSquares.construction,
      P203Specs.Ch04.FourSquares.squaredNorm] <;> ring

theorem construction_congruences :
    P203Specs.Ch04.FourSquares.ConstructionCongruences := by
  intro m _hm A B h
  have hC := construction_congr m A B B B h (fun _ => Int.ModEq.rfl)
  rw [construction_self] at hC
  constructor
  · intro i
    have hi := hC i.succ
    fin_cases i <;> simpa [construction] using hi
  · simpa [construction, squaredNorm] using hC 0

/-- Lagrange's theorem, retaining zero and nonnegative witnesses. -/
theorem lagrange_four_squares : P203Specs.Ch04.FourSquares.LagrangeFourSquares := by
  intro n
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨a, b, c, d, h.symm⟩

end P203.Ch04.FourSquares
