import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic

/-! Independent specification of the graph assertion of paper.tex,
Proposition p205:W20 (5.1), lines 955–958. The graph is any finite simple
undirected graph; the vertex type may be empty. Both graph quantities
are Mathlib's canonical ones. -/

open scoped BigOperators Classical

namespace Specs.P205.Probability.CaroWei

universe u

def Bound : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    (∑ v, (1 : ℝ) / ((G.degree v : ℝ) + 1)) ≤ (G.indepNum : ℝ)

end Specs.P205.Probability.CaroWei
