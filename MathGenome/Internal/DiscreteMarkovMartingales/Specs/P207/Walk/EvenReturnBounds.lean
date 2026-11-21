import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.LatticeLocalBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent statement of `paper.tex`, Theorem `p207:thm:lattice-return-rate`.
The return mass is the power of the shared nearest-neighbor lattice kernel.
Real constants express finiteness; `[NeZero d]` expresses `d ≥ 1`. -/

namespace P207.Walk.EvenReturnBoundsSpec

noncomputable section

/-- Both estimates, with constants depending only on the dimension, at every
positive integer time parameter, including `n = 1`. -/
def even_return_bounds : Prop :=
  ∀ (d : ℕ) [NeZero d], ∃ c C : ℝ,
    0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      c * (n : ℝ) ^ (-(d : ℝ) / 2) ≤ (returnProbability d (2 * n)).toReal ∧
      (returnProbability d (2 * n)).toReal ≤ C * (n : ℝ) ^ (-(d : ℝ) / 2)

end
end P207.Walk.EvenReturnBoundsSpec
