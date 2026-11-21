import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.ThreeSquaresReduction

/-! The full conclusion of Legendre's three-square theorem,
`paper.tex:1874–1994`, Theorem 4.10 (`nt:D06`). -/
namespace P203Specs.Ch04

/-- Every positive natural number is a sum of three signed integer squares
exactly when it is outside the excluded family. -/
def ThreeSquaresTheorem : Prop :=
  ∀ n : ℕ, 0 < n → (ThreeSquares n ↔ ¬Forbidden n)

/-- The separately stated boundary case of Theorem 4.10. -/
def ThreeSquaresAtZero : Prop := ThreeSquares 0

end P203Specs.Ch04
