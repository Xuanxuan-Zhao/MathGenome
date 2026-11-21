import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

/-!
Independent statements for the derangement assertion of paper.tex, W04.
`derangements (Fin n)` is the subtype of permutations `f` satisfying
`∀ i, f i ≠ i`; thus the left sides count actual fixed-point-free permutations
of an n-element set. `range (n + 1)` includes both endpoints 0 and n.
-/

open scoped BigOperators

namespace Specs.FiniteCombinatorics.Counting

def DerangementsInteger : Prop :=
  ∀ n : ℕ, (Fintype.card (derangements (Fin n)) : ℤ) =
    ∑ j ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ j * (Nat.choose n j : ℤ) * ((n - j).factorial : ℤ)

def DerangementsRational : Prop :=
  ∀ n : ℕ, (Fintype.card (derangements (Fin n)) : ℚ) =
    (n.factorial : ℚ) *
      ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j / (j.factorial : ℚ)

def DerangementsZero : Prop :=
  Fintype.card (derangements (Fin 0)) = 1

end Specs.FiniteCombinatorics.Counting
