import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic

/-! The independence bound by deletion, paper.tex, Corollary 4.5 (W18).
The vertex type may be empty. The edge count counts unordered edges once.
No regularity, nonempty-edge, or strict probability hypothesis is imposed. -/

open scoped Classical

namespace P205.Probability.IndependenceDeletionSpec

def independenceBound : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (p : ℝ),
    0 ≤ p → p ≤ 1 →
    p * (Fintype.card V : ℝ) - p ^ 2 * (G.edgeFinset.card : ℝ) ≤
      (G.indepNum : ℝ)

end P205.Probability.IndependenceDeletionSpec
