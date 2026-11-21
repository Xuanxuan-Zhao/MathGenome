import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.Characterizations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.DegreesLeaves
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

universe u

namespace FiniteCombinatorics.Graph.Trees

/-- W37: the endpoints of a longest path in a nontrivial tree are leaves. -/
theorem two_leaves :
    Specs.FiniteCombinatorics.Graph.Trees.DegreesLeaves.two_leavesType := by
  intro V _ G hG hsize
  classical
  let : Fintype V := Fintype.ofFinite V
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp
    (by rw [Nat.card_eq_fintype_card] at hsize; omega)
  obtain ⟨a, b, hne, ha, hb⟩ := hG.exists_ne_and_degree_eq_one
  exact ⟨a, b, hne, (degree_mathlib G a).trans ha, (degree_mathlib G b).trans hb⟩

/-- W37: each unordered edge contributes two to the sum of degrees. -/
theorem degree_sum :
    Specs.FiniteCombinatorics.Graph.Trees.DegreesLeaves.degree_sumType := by
  intro V _ G
  classical
  simp_rw [degree_mathlib G]
  simpa only [G.edgeFinset_card, Nat.card_eq_fintype_card] using
    G.sum_degrees_eq_twice_card_edges

/-- W37: combine handshaking with the tree edge count, also for one vertex. -/
theorem tree_degree_sum :
    Specs.FiniteCombinatorics.Graph.Trees.DegreesLeaves.tree_degree_sumType := by
  intro V _ G hG
  have : Nonempty V := hG.connected.nonempty
  rw [degree_sum G, ((tree_iff_edge_count G).mp hG).2]

/-- W37: the number of vertices of odd degree is even. -/
theorem even_odd_degree_count :
    Specs.FiniteCombinatorics.Graph.Trees.DegreesLeaves.even_odd_degree_countType := by
  intro V _ G
  classical
  let : Fintype V := Fintype.ofFinite V
  simp_rw [degree_mathlib G]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    G.even_card_odd_degree_vertices

end FiniteCombinatorics.Graph.Trees
