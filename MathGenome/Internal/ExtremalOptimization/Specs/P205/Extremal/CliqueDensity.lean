import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic

/-! The fixed-sample clique-counting conclusion of paper.tex, W03.
Cliques are counted once as vertex subsets, without inducedness requirements. -/
namespace P205.Extremal.CliqueDensitySpecs

open SimpleGraph

/-- Uniform supersaturation above the `(r-1)`-partite threshold. -/
def supersaturationStatement : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N ≤ Fintype.card V →
        (1 - 1 / ((r : ℝ) - 1) + ε) * ((Fintype.card V).choose 2 : ℝ) ≤
          (G.edgeFinset.card : ℝ) →
        c * (Fintype.card V : ℝ) ^ r ≤ (G.cliqueFinset r).card

end P205.Extremal.CliqueDensitySpecs
