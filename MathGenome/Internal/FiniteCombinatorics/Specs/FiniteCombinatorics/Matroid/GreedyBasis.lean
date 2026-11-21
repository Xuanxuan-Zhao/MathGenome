import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GreedyPrefix

/-! Independent statement of the basis conclusion of paper.tex W79.
Weights are arbitrary real numbers; the tie order is arbitrary. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u

def greedyBasisOptimal : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E),
    M.IsBase (greedyOutput (fromMatroid M) w tie) ∧
      ∀ B, M.IsBase B →
        subsetWeight (fromMatroid M) w B ≤
          subsetWeight (fromMatroid M) w (greedyOutput (fromMatroid M) w tie)

end FiniteCombinatorics.Matroid.Expected
