import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.Characterizations

universe u

namespace FiniteCombinatorics.Graph.Trees

/-- W36: the edge count characterization, with natural subtraction and no
exclusion of the one-vertex tree. -/
theorem tree_iff_edge_count :
    Specs.FiniteCombinatorics.Graph.Trees.Characterizations.tree_iff_edge_countType := by
  intro V _ _ G
  change G.IsTree ↔ G.Connected ∧ Nat.card G.edgeSet = Nat.card V - 1
  rw [SimpleGraph.isTree_iff_connected_and_card]
  have hpos : 0 < Nat.card V := Nat.card_pos
  constructor <;> rintro ⟨hc, he⟩ <;> exact ⟨hc, by omega⟩

/-- W36: each ordered pair has exactly one vertex-simple path. -/
theorem tree_iff_unique_path :
    Specs.FiniteCombinatorics.Graph.Trees.Characterizations.tree_iff_unique_pathType := by
  intro V _ _ G
  change G.IsTree ↔ ∀ a b : V, ∃! p : G.Path a b, True
  rw [SimpleGraph.isTree_iff_existsUnique_path]
  constructor
  · rintro ⟨_, h⟩ a b
    obtain ⟨p, hp, hu⟩ := h a b
    exact ⟨⟨p, hp⟩, trivial, fun q _ => Subtype.ext (hu q.val q.property)⟩
  · intro h
    refine ⟨inferInstance, fun a b => ?_⟩
    obtain ⟨p, _, hu⟩ := h a b
    exact ⟨p.val, p.property, fun q hq => congrArg Subtype.val (hu ⟨q, hq⟩ trivial)⟩

/-- A spanning tree retains the entire vertex type and only removes edges. -/
theorem spanning_tree :
    Specs.FiniteCombinatorics.Graph.Trees.Characterizations.spanning_treeType := by
  intro V _ G hG
  exact hG.exists_isTree_le

/-- Equality of reachability makes each original component a component of
an acyclic spanning subgraph, hence its induced graph is a tree. -/
lemma tree_on_component_of_reachable_eq {V : Type u} {F G : SimpleGraph V}
    (hF : F.IsAcyclic) (hreach : F.Reachable = G.Reachable)
    (c : G.ConnectedComponent) : (F.induce c.supp).IsTree := by
  obtain ⟨v, hv⟩ := c.nonempty_supp
  let d := F.connectedComponentMk v
  have hs : d.supp = c.supp := by
    ext w
    change F.connectedComponentMk w = F.connectedComponentMk v ↔ w ∈ c.supp
    rw [SimpleGraph.ConnectedComponent.eq, hreach,
      ← SimpleGraph.ConnectedComponent.eq, (c.mem_supp_iff v).mp hv]
    exact (c.mem_supp_iff w).symm
  have ht := hF.isTree_connectedComponent d
  change (F.induce d.supp).IsTree at ht
  rwa [hs] at ht

/-- W36: a component-preserving spanning forest, valid also on no vertices. -/
theorem spanning_forest :
    Specs.FiniteCombinatorics.Graph.Trees.Characterizations.spanning_forestType := by
  intro V _ G
  obtain ⟨F, hle, hF, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  exact ⟨F, hle, hF, hreach, tree_on_component_of_reachable_eq hF hreach⟩

end FiniteCombinatorics.Graph.Trees
