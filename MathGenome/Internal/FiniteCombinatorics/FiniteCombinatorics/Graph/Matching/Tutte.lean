import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.Tutte
import Mathlib.Combinatorics.SimpleGraph.Tutte

universe u
noncomputable section

namespace FiniteCombinatorics.Graph.Matching

/-- The induced graph on precisely the vertices not in `S`. -/
abbrev deletedGraph : Specs.FiniteCombinatorics.Graph.Matching.Tutte.deletedGraphType :=
  Specs.FiniteCombinatorics.Graph.Matching.Tutte.deletedGraphValue

/-- The number of connected components with an odd number of vertices. -/
abbrev oddComponentCount :
    Specs.FiniteCombinatorics.Graph.Matching.Tutte.oddComponentCountType :=
  Specs.FiniteCombinatorics.Graph.Matching.Tutte.oddComponentCountValue

variable {V : Type u} [Finite V]

private theorem deletedGraph_eq (G : SimpleGraph V) (S : Set V) :
    ((⊤ : G.Subgraph).deleteVerts S).coe = deletedGraph G S := by
  ext a b
  simp only [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteVerts_adj,
    SimpleGraph.Subgraph.verts_top, Set.mem_univ, true_and,
    SimpleGraph.Subgraph.top_adj]
  exact and_iff_right a.property.2 |>.trans (and_iff_right b.property.2)

private theorem perfectMatching_exists_iff (G : SimpleGraph V) :
    (∃ M : Set (Sym2 V), IsPerfectMatching G M) ↔
    ∃ H : G.Subgraph, H.IsPerfectMatching := by
  constructor
  · rintro ⟨M, hm⟩
    refine ⟨edgeSubgraph G M hm.1.1, ?_⟩
    apply (perfect_subgraph_iff G _).mpr
    rwa [edgeSubgraph_edgeSet]
  · rintro ⟨H, hH⟩
    exact ⟨H.edgeSet, (perfect_subgraph_iff G H).mp hH⟩

/-- Tutte's perfect-matching criterion, including the empty vertex set (W53). -/
theorem tutte : Specs.FiniteCombinatorics.Graph.Matching.Tutte.tutteType := by
  intro V _ G
  change (∃ M : Set (Sym2 V), IsPerfectMatching G M) ↔ _
  rw [perfectMatching_exists_iff G, SimpleGraph.tutte]
  apply forall_congr'
  intro S
  rw [SimpleGraph.IsTutteViolator, not_lt, deletedGraph_eq]
  rfl

end FiniteCombinatorics.Graph.Matching
