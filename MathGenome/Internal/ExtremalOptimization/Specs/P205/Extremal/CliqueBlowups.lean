import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic

/-! Independent specification of paper.tex, Theorem 1.4 (W03).
Containment means an injective adjacency-preserving map; extra ambient edges
are permitted. The threshold is an edge density, with no degree assumptions. -/
namespace P205.Extremal.CliqueBlowupsSpecs

open SimpleGraph

/-- Every fixed positive excess above the Turán threshold forces any fixed
complete equipartite graph as a (not necessarily induced) subgraph. -/
def blowupsStatement : Prop :=
  ∀ (r t : ℕ), 2 ≤ r → 1 ≤ t → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N ≤ Fintype.card V →
        (1 - 1 / ((r : ℝ) - 1) + ε) * ((Fintype.card V).choose 2 : ℝ) ≤
          (G.edgeFinset.card : ℝ) →
        Nonempty (Copy (completeEquipartiteGraph r t) G)

end P205.Extremal.CliqueBlowupsSpecs
