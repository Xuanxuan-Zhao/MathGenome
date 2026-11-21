import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Blocks.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Blocks.Membership
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Order.Preorder.Finite

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Blocks
open SimpleGraph
open FiniteCombinatorics.Graph.Trees

variable {V : Type u} [Finite V] {G : SimpleGraph V}

/-- Connectivity after deleting an ambient vertex, whether or not it was in the subgraph. -/
lemma TwoConnected.connected_deleteVerts {H : G.Subgraph}
    (hH : TwoConnected H.coe) (v : V) : (H.deleteVerts {v}).Connected := by
  classical
  by_cases hv : v ∈ H.verts
  · rw [Subgraph.connected_iff']
    apply (H.coeDeleteVertsIso {v}).connected_iff.mpr
    have hs : {w : H.verts | ↑w ∉ ({v} : Set V)} = {w | w ≠ ⟨v, hv⟩} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact not_congr (Subtype.ext_iff (a1 := w) (a2 := ⟨v, hv⟩)).symm
    rw [hs]
    exact hH.2.2 ⟨v, hv⟩
  · have heq : H.deleteVerts {v} = H := by
      apply le_antisymm H.deleteVerts_le
      constructor
      · intro a ha
        exact ⟨ha, fun h => hv (h ▸ ha)⟩
      · intro a b hab
        exact Subgraph.deleteVerts_adj.mpr ⟨H.edge_vert hab,
          fun h => hv (h ▸ H.edge_vert hab), H.edge_vert hab.symm,
          fun h => hv (h ▸ H.edge_vert hab.symm), hab⟩
    rw [heq, Subgraph.connected_iff']
    exact hH.2.1

/-- Deletion distributes over union, keeping both vertices and edges. -/
lemma deleteVerts_sup (H K : G.Subgraph) (s : Set V) :
    (H ⊔ K).deleteVerts s = H.deleteVerts s ⊔ K.deleteVerts s := by
  ext a b <;> simp only [Subgraph.deleteVerts_verts, Subgraph.verts_sup,
    Set.mem_sdiff, Set.mem_union, Subgraph.deleteVerts_adj, Subgraph.sup_adj]
  · tauto
  · constructor
    · rintro ⟨ha, has, hb, hbs, hab | hab⟩
      · exact Or.inl ⟨H.edge_vert hab, has, H.edge_vert hab.symm, hbs, hab⟩
      · exact Or.inr ⟨K.edge_vert hab, has, K.edge_vert hab.symm, hbs, hab⟩
    · rintro (⟨ha, has, hb, hbs, hab⟩ | ⟨ha, has, hb, hbs, hab⟩)
      · exact ⟨Or.inl ha, has, Or.inl hb, hbs, Or.inl hab⟩
      · exact ⟨Or.inr ha, has, Or.inr hb, hbs, Or.inr hab⟩

/-- The union lemma used in the source's proof of block intersection uniqueness. -/
lemma TwoConnected.sup {H K : G.Subgraph}
    (hH : TwoConnected H.coe) (hK : TwoConnected K.coe)
    {a b : V} (haH : a ∈ H.verts) (haK : a ∈ K.verts)
    (hbH : b ∈ H.verts) (hbK : b ∈ K.verts) (hab : a ≠ b) :
    TwoConnected (H ⊔ K).coe := by
  classical
  refine ⟨hH.1.trans ?_, ?_, ?_⟩
  · exact Nat.card_le_card_of_injective (Subgraph.inclusion (le_sup_left : H ≤ H ⊔ K))
      (Subgraph.inclusion.injective _)
  · exact (Subgraph.connected_sup ⟨hH.2.1.preconnected⟩ ⟨hK.2.1.preconnected⟩
      ⟨a, haH, haK⟩).coe
  · intro v
    have hconn : ((H ⊔ K).deleteVerts {v.val}).Connected := by
      rw [deleteVerts_sup]
      apply Subgraph.connected_sup
        (hH.connected_deleteVerts v.val).preconnected
        (hK.connected_deleteVerts v.val).preconnected
      by_cases hav : a = v.val
      · exact ⟨b, ⟨hbH, by simpa only [Set.mem_singleton_iff] using
          (show b ≠ v.val from fun h => hab (hav.trans h.symm))⟩,
          hbK, by simpa only [Set.mem_singleton_iff] using
          (show b ≠ v.val from fun h => hab (hav.trans h.symm))⟩
      · exact ⟨a, ⟨haH, hav⟩, haK, hav⟩
    have hc := ((H ⊔ K).coeDeleteVertsIso {v.val}).connected_iff.mp hconn.coe
    have hs : {w : (H ⊔ K).verts | ↑w ∉ ({v.val} : Set V)} = {w | w ≠ v} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact not_congr Subtype.ext_iff.symm
    rw [hs] at hc
    exact hc

/-- Maximal 2-connected subgraphs sharing two vertices are equal. -/
lemma maximalTwoConnected_eq_of_two_mem {H K : G.Subgraph}
    (hH : MaximalTwoConnectedSubgraph G H) (hK : MaximalTwoConnectedSubgraph G K)
    {a b : V} (haH : a ∈ H.verts) (haK : a ∈ K.verts)
    (hbH : b ∈ H.verts) (hbK : b ∈ K.verts) (hab : a ≠ b) : H = K := by
  have hsup := hH.1.sup hK.1 haH haK hbH hbK hab
  exact (hH.2 (H ⊔ K) le_sup_left hsup).symm.trans (hK.2 (H ⊔ K) le_sup_right hsup)

/-- Deleting one endpoint prevents a walk from using that endpoint's edge. -/
def deleteVertexToDeleteEdge {W : Type u} [Finite W] {H : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f) (a b : W) :
    deleteVertex H a →g G.deleteEdges {s(f a, f b)} where
  toFun x := f x.val
  map_rel' := by
    intro x y hxy
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨f.map_adj hxy, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact x.property (hf hx)
    · exact y.property (hf hy)

/-- Any two vertices of a 2-connected subgraph have an ambient walk avoiding
the edge between them, even when that edge is absent from the subgraph. -/
lemma TwoConnected.reachable_deleteEdge {W : Type u} [Finite W] {H : SimpleGraph W}
    (hH : TwoConnected H) (f : H →g G) (hf : Function.Injective f) (a b : W) :
    (G.deleteEdges {s(f a, f b)}).Reachable (f a) (f b) := by
  by_cases hab : a = b
  · subst b
    exact Reachable.refl _
  have hc : (3 : ℕ∞) ≤ ENat.card W := by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast hH.1
  obtain ⟨c, hca, hcb⟩ := ENat.exists_ne_ne_of_three_le hc a b
  have h₁ := (hH.2.2 b ⟨a, hab⟩ ⟨c, hcb⟩).map
    (deleteVertexToDeleteEdge f hf b a)
  have h₂ := (hH.2.2 a ⟨c, hca⟩ ⟨b, Ne.symm hab⟩).map
    (deleteVertexToDeleteEdge f hf a b)
  have hs : s(f b, f a) = s(f a, f b) := Sym2.eq_swap
  change (G.deleteEdges {s(f b, f a)}).Reachable (f a) (f c) at h₁
  rw [hs] at h₁
  exact h₁.trans h₂

/-- A bridge cannot have both endpoints in a 2-connected subgraph. -/
lemma TwoConnected.not_bridge_of_mem {H : G.Subgraph}
    (hH : TwoConnected H.coe) {a b : V} (ha : a ∈ H.verts) (hb : b ∈ H.verts)
    (hab : G.Adj a b) : ¬ Bridge G s(a, b) := by
  intro he
  have he' := (bridge_iff_isBridge G s(a, b) hab).mp he
  exact he' (hH.reachable_deleteEdge H.hom Subtype.val_injective ⟨a, ha⟩ ⟨b, hb⟩)

/-- The two distinct vertices of a bridge block determine its edge and the whole subgraph. -/
lemma BridgeBlock.eq_edge_of_two_mem {H : G.Subgraph} (hH : BridgeBlock G H)
    {a b : V} (ha : a ∈ H.verts) (hb : b ∈ H.verts) (hab : a ≠ b) :
    ∃ h : G.Adj a b, Bridge G s(a, b) ∧ H = G.subgraphOfAdj h := by
  obtain ⟨x, y, hxy, he, rfl⟩ := hH
  simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact ⟨hxy, he, rfl⟩
  · refine ⟨hxy.symm, ?_, (G.subgraphOfAdj_symm hxy).symm⟩
    rw [Sym2.eq_swap]
    exact he
  · exact (hab rfl).elim

/-- Isolated blocks cannot contain two distinct vertices. -/
lemma IsolatedBlock.verts_subsingleton {H : G.Subgraph} (hH : IsolatedBlock G H) :
    H.verts.Subsingleton := by
  obtain ⟨v, hv, rfl⟩ := hH
  exact Set.subsingleton_singleton

/-- All three kinds of blocks satisfy the same intersection uniqueness property. -/
lemma IsBlock.eq_of_two_mem {H K : G.Subgraph} (hH : IsBlock G H) (hK : IsBlock G K)
    {a b : V} (haH : a ∈ H.verts) (haK : a ∈ K.verts)
    (hbH : b ∈ H.verts) (hbK : b ∈ K.verts) (hab : a ≠ b) : H = K := by
  rcases hH with hH | hH | hH
  · rcases hK with hK | hK | hK
    · exact maximalTwoConnected_eq_of_two_mem hH hK haH haK hbH hbK hab
    · obtain ⟨h, he, _⟩ := hK.eq_edge_of_two_mem haK hbK hab
      exact (hH.1.not_bridge_of_mem haH hbH h he).elim
    · exact (hab (hK.verts_subsingleton haK hbK)).elim
  · rcases hK with hK | hK | hK
    · obtain ⟨h, he, _⟩ := hH.eq_edge_of_two_mem haH hbH hab
      exact (hK.1.not_bridge_of_mem haK hbK h he).elim
    · obtain ⟨h₁, _, he₁⟩ := hH.eq_edge_of_two_mem haH hbH hab
      obtain ⟨h₂, _, he₂⟩ := hK.eq_edge_of_two_mem haK hbK hab
      exact he₁.trans he₂.symm
    · exact (hab (hK.verts_subsingleton haK hbK)).elim
  · exact (hab (hH.verts_subsingleton haH hbH)).elim

/-- W38: distinct blocks share at most one vertex, including bridges and isolated blocks. -/
theorem distinct_blocks_intersection :
    Specs.FiniteCombinatorics.Graph.Blocks.Membership.distinct_blocks_intersectionType := by
  intro V _ G B C hBC a ha b hb
  by_contra hab
  exact hBC (Subtype.ext (IsBlock.eq_of_two_mem B.property C.property
    ha.1 ha.2 hb.1 hb.2 hab))

/-- A contiguous part of a walk gives a subgraph of the whole walk. -/
lemma walkSubgraph_mono {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (hpq : p.IsSubwalk q) : p.toSubgraph ≤ q.toSubgraph := by
  constructor
  · intro x hx
    exact q.mem_verts_toSubgraph.mpr (hpq.support_subset (p.mem_verts_toSubgraph.mp hx))
  · intro x y hxy
    exact Walk.adj_toSubgraph_iff_mem_edges.mpr
      (hpq.edges_subset (Walk.adj_toSubgraph_iff_mem_edges.mp hxy))

/-- A simple cycle, regarded as its actual vertex-and-edge subgraph, is 2-connected. -/
lemma cycle_twoConnected {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    TwoConnected p.toSubgraph.coe := by
  classical
  refine ⟨?_, p.toSubgraph_connected.coe, ?_⟩
  · have hv : p.toSubgraph.verts = (p.tail.support.toFinset : Set V) := by
      ext x
      simp only [Walk.mem_verts_toSubgraph, Finset.mem_coe, List.mem_toFinset]
      rw [← p.cons_support_tail hp.not_nil, List.mem_cons]
      exact ⟨by rintro (rfl | hx); exact p.tail.end_mem_support; exact hx, Or.inr⟩
    change 3 ≤ p.toSubgraph.verts.ncard
    rw [hv, Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.isPath_tail.support_nodup,
      Walk.length_support, Walk.length_tail]
    have := hp.three_le_length
    omega
  · intro v
    let q := p.rotate v.val (p.mem_verts_toSubgraph.mp v.property)
    have hq : q.IsCycle := hp.rotate _
    have hqp : q.toSubgraph = p.toSubgraph := p.toSubgraph_rotate _
    have hqt : ¬q.tail.Nil := by
      rw [Walk.not_nil_iff_lt_length, Walk.length_tail]
      have := hq.three_le_length
      omega
    let r := q.tail.dropLast
    have hparts : q.support = v.val :: (r.support ++ [v.val]) := by
      rw [← q.cons_support_tail hq.not_nil, ← Walk.support_dropLast_concat hqt]
    have havoid : v.val ∉ r.support := by
      have hn := hq.isPath_tail.support_nodup
      rw [← Walk.support_dropLast_concat hqt] at hn
      intro hv
      exact List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 hv (by simp)
    have hrq : r.toSubgraph ≤ q.toSubgraph :=
      walkSubgraph_mono q.isSubwalk_rfl.tail.dropLast
    have hle : r.toSubgraph ≤ q.toSubgraph.deleteVerts {v.val} := by
      constructor
      · intro x hx
        exact ⟨hrq.1 hx, fun he => havoid (he ▸ r.mem_verts_toSubgraph.mp hx)⟩
      · intro x y hxy
        exact Subgraph.deleteVerts_adj.mpr ⟨hrq.1 (r.toSubgraph.edge_vert hxy),
          fun he => havoid (he ▸ r.mem_verts_toSubgraph.mp (r.toSubgraph.edge_vert hxy)),
          hrq.1 (r.toSubgraph.edge_vert hxy.symm),
          fun he => havoid (he ▸ r.mem_verts_toSubgraph.mp (r.toSubgraph.edge_vert hxy.symm)),
          hrq.2 hxy⟩
    have hverts : r.toSubgraph.verts = (q.toSubgraph.deleteVerts {v.val}).verts := by
      apply Set.Subset.antisymm hle.1
      intro x hx
      have hxq := q.mem_verts_toSubgraph.mp hx.1
      rw [hparts] at hxq
      have hxn : x ≠ v.val := hx.2
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hxq
      exact r.mem_verts_toSubgraph.mpr (by tauto)
    have hc := r.toSubgraph_connected.mono hle hverts
    rw [hqp] at hc
    have hc' := (p.toSubgraph.coeDeleteVertsIso {v.val}).connected_iff.mp hc.coe
    have hs : {w : p.toSubgraph.verts | ↑w ∉ ({v.val} : Set V)} = {w | w ≠ v} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact not_congr Subtype.ext_iff.symm
    rw [hs] at hc'
    exact hc'

/-- Finite maximal extension among 2-connected subgraphs. -/
lemma exists_maximalTwoConnected_ge {H : G.Subgraph} (hH : TwoConnected H.coe) :
    ∃ K : G.Subgraph, H ≤ K ∧ MaximalTwoConnectedSubgraph G K := by
  obtain ⟨K, hHK, hK⟩ := Finite.exists_le_maximal (p := fun L : G.Subgraph =>
    TwoConnected L.coe) hH
  exact ⟨K, hHK, hK.1, fun L hKL hL => le_antisymm (hK.2 hL hKL) hKL⟩

/-- W38: every edge lies in exactly one block. -/
theorem edge_unique_block :
    Specs.FiniteCombinatorics.Graph.Blocks.Membership.edge_unique_blockType := by
  intro V _ G a b hab
  classical
  have hex : ∃ B : Block G, B.val.Adj a b := by
    by_cases hb : Bridge G s(a, b)
    · exact ⟨⟨G.subgraphOfAdj hab, Or.inr (Or.inl ⟨a, b, hab, hb, rfl⟩)⟩, rfl⟩
    · have hb' : ¬G.IsBridge s(a, b) := fun h =>
        hb ((bridge_iff_isBridge G s(a, b) hab).mpr h)
      have hexcycle : ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s(a, b) ∈ p.edges := by
        by_contra! hn
        exact hb' ((SimpleGraph.isBridge_iff_forall_cycle_notMem hab).mpr hn)
      obtain ⟨v, p, hp, he⟩ := hexcycle
      obtain ⟨K, hK, hmax⟩ := exists_maximalTwoConnected_ge (cycle_twoConnected hp)
      exact ⟨⟨K, Or.inl hmax⟩, hK.2 (Walk.adj_toSubgraph_iff_mem_edges.mpr he)⟩
  obtain ⟨B, hB⟩ := hex
  refine ⟨B, hB, ?_⟩
  intro C hC
  apply Subtype.ext
  exact IsBlock.eq_of_two_mem C.property B.property
    (C.val.edge_vert hC) (B.val.edge_vert hB)
    (C.val.edge_vert hC.symm) (B.val.edge_vert hB.symm) hab.ne

/-- Every kind of block is connected. -/
lemma IsBlock.connected {H : G.Subgraph} (hH : IsBlock G H) : H.Connected := by
  rcases hH with hH | ⟨a, b, hab, _, rfl⟩ | ⟨v, _, rfl⟩
  · exact ⟨hH.1.2.1⟩
  · exact Subgraph.subgraphOfAdj_connected hab
  · exact Subgraph.singletonSubgraph_connected

/-- At a vertex of a block, there is an incident edge unless this is the isolated singleton. -/
lemma IsBlock.eq_singleton_or_exists_adj {H : G.Subgraph} (hH : IsBlock G H)
    {v : V} (hv : v ∈ H.verts) :
    (H = G.singletonSubgraph v ∧ G.IsIsolated v) ∨ ∃ a, H.Adj v a := by
  rcases hH with hH | ⟨a, b, hab, _, rfl⟩ | ⟨w, hw, rfl⟩
  · have : Nontrivial H.verts := Finite.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_le (by decide : 1 < 3) hH.1.1)
    obtain ⟨a, ha⟩ := hH.1.2.1.preconnected.exists_adj_of_nontrivial ⟨v, hv⟩
    exact Or.inr ⟨a.val, ha⟩
  · simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact Or.inr ⟨b, rfl⟩
    · exact Or.inr ⟨a, by exact Sym2.eq_swap⟩
  · have hvw : v = w := hv
    subst w
    exact Or.inl ⟨rfl, hw⟩

/-- Deleting a vertex of a block leaves a preconnected graph; it can be empty
for the isolated singleton and have one vertex for a bridge block. -/
lemma IsBlock.preconnected_deleteVerts {H : G.Subgraph} (hH : IsBlock G H)
    {v : V} (hv : v ∈ H.verts) : (H.deleteVerts {v}).Preconnected := by
  classical
  rcases hH with hH | ⟨a, b, hab, _, rfl⟩ | ⟨w, _, rfl⟩
  · exact (hH.1.connected_deleteVerts v).preconnected
  · have hs : ((G.subgraphOfAdj hab).deleteVerts {v}).verts.Subsingleton := by
      intro x hx y hy
      simp only [Subgraph.deleteVerts_verts, subgraphOfAdj_verts, Set.mem_sdiff,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact (hx.1.resolve_left hx.2).trans (hy.1.resolve_left hy.2).symm
      · exact (hx.1.resolve_right hx.2).trans (hy.1.resolve_right hy.2).symm
    have : Subsingleton ((G.subgraphOfAdj hab).deleteVerts {v}).verts := hs.coe_sort
    exact ⟨SimpleGraph.Preconnected.of_subsingleton⟩
  · have hs : ((G.singletonSubgraph w).deleteVerts {v}).verts.Subsingleton := by
      intro x hx y hy
      exact (show x = w from hx.1).trans (show y = w from hy.1).symm
    have : Subsingleton ((G.singletonSubgraph w).deleteVerts {v}).verts := hs.coe_sort
    exact ⟨SimpleGraph.Preconnected.of_subsingleton⟩

/-- Vertices in a block remain mutually reachable in the original component
after deleting any other vertex of that block. -/
lemma IsBlock.reachable_componentDeleteVertex {H : G.Subgraph} (hH : IsBlock G H)
    {v a b : V} (hv : v ∈ H.verts) (ha : a ∈ H.verts) (hb : b ∈ H.verts)
    (hav : a ≠ v) (hbv : b ≠ v) :
    (componentDeleteVertex G v).Reachable
      ⟨a, (hH.connected ⟨v, hv⟩ ⟨a, ha⟩).map H.hom, hav⟩
      ⟨b, (hH.connected ⟨v, hv⟩ ⟨b, hb⟩).map H.hom, hbv⟩ := by
  let f : (H.deleteVerts {v}).coe →g componentDeleteVertex G v := {
    toFun := fun x => ⟨x.val, (hH.connected ⟨v, hv⟩ ⟨x.val, x.property.1⟩).map H.hom,
      x.property.2⟩
    map_rel' := fun h => (H.deleteVerts {v}).adj_sub h }
  exact (hH.preconnected_deleteVerts hv ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩).map f

/-- The component count detects preconnectedness, including on the empty vertex type. -/
lemma preconnected_iff_componentCount_le_one (H : SimpleGraph V) :
    H.Preconnected ↔ componentCount H ≤ 1 := by
  rw [show componentCount H = Nat.card H.ConnectedComponent from rfl,
    Finite.card_le_one_iff_subsingleton]
  exact ⟨SimpleGraph.Preconnected.subsingleton_connectedComponent,
    fun h a b => ConnectedComponent.exact (h.elim _ _)⟩

/-- Every vertex of the deleted component can reach an original neighbor of
the deleted vertex without using that vertex. -/
lemma exists_neighbor_reachable_after_delete (v : V)
    (x : {w : V // G.Reachable v w ∧ w ≠ v}) :
    ∃ a : {w : V // G.Reachable v w ∧ w ≠ v},
      G.Adj v a.val ∧ (componentDeleteVertex G v).Reachable a x := by
  classical
  obtain ⟨p⟩ := x.property.1
  let q := p.toPath
  have hn : ¬q.val.Nil := q.val.not_nil_of_ne (Ne.symm x.property.2)
  have havoid : v ∉ q.val.tail.support := by
    have hs := q.property.support_nodup
    rw [← q.val.cons_support_tail hn] at hs
    exact (List.nodup_cons.mp hs).1
  have hmem (y : V) (hy : y ∈ q.val.tail.support) : G.Reachable v y ∧ y ≠ v := by
    have hyq : y ∈ q.val.support := q.val.isSubwalk_rfl.tail.support_subset hy
    exact ⟨(q.val.takeUntil y hyq).reachable, fun he => havoid (he ▸ hy)⟩
  exact ⟨⟨q.val.snd, hmem _ q.val.tail.start_mem_support⟩,
    q.val.adj_snd hn, (q.val.tail.induce _ hmem).reachable⟩

/-- Two incident edges joined by a path avoiding their common endpoint are in one block. -/
lemma exists_block_of_reachable_after_delete (v : V)
    (a b : {w : V // G.Reachable v w ∧ w ≠ v})
    (hva : G.Adj v a.val) (hvb : G.Adj v b.val)
    (hpath : (componentDeleteVertex G v).Reachable a b) :
    ∃ B : Block G, B.val.Adj v a.val ∧ B.val.Adj v b.val := by
  classical
  by_cases hab : a.val = b.val
  · obtain ⟨B, hB, _⟩ := edge_unique_block G v a.val hva
    exact ⟨B, hB, hab ▸ hB⟩
  obtain ⟨p⟩ := hpath
  change (G.induce {w | G.Reachable v w ∧ w ≠ v}).Walk a b at p
  let f : (G.induce {w | G.Reachable v w ∧ w ≠ v}) →g G :=
    (SimpleGraph.Embedding.induce _).toHom
  let q : G.Walk a.val b.val := p.toPath.val.map f
  have hq : q.IsPath := p.toPath.property.map Subtype.val_injective
  have havoid : v ∉ q.support := by
    intro hv
    change v ∈ (p.toPath.val.map f).support at hv
    rw [Walk.support_map] at hv
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hv
    exact w.property.2 he
  let c := (q.concat hvb.symm).cons hva
  have hc : c.IsCycle := by
    apply (Walk.cons_isCycle_iff _ _).mpr
    refine ⟨hq.concat havoid hvb.symm, ?_⟩
    intro he
    rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact havoid (q.fst_mem_support_of_mem_edges he)
    · rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact b.property.2 h₁.symm
      · exact hab h₂
  obtain ⟨K, hK, hmax⟩ := exists_maximalTwoConnected_ge (cycle_twoConnected hc)
  refine ⟨⟨K, Or.inl hmax⟩, ?_, ?_⟩
  · apply hK.2
    exact Walk.adj_toSubgraph_iff_mem_edges.mpr (by simp [c])
  · apply hK.2
    apply Walk.adj_toSubgraph_iff_mem_edges.mpr
    simp only [c, Walk.edges_cons, Walk.edges_concat, List.concat_eq_append,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr Sym2.eq_swap)

/-- An isolated ambient vertex can occur only in its singleton block. -/
lemma IsBlock.eq_singleton_of_isolated {H : G.Subgraph} (hH : IsBlock G H)
    {v : V} (hv : v ∈ H.verts) (hi : G.IsIsolated v) : H = G.singletonSubgraph v := by
  rcases hH.eq_singleton_or_exists_adj hv with ⟨h, _⟩ | ⟨a, ha⟩
  · exact h
  · exact (hi a (H.adj_sub ha)).elim

/-- W38: the shared vertices are exactly the cut vertices of their original component. -/
theorem cutVertex_iff_mem_two_blocks :
    Specs.FiniteCombinatorics.Graph.Blocks.Membership.cutVertex_iff_mem_two_blocksType := by
  intro V _ G v
  classical
  constructor
  · intro hcut
    have hn : ¬(componentDeleteVertex G v).Preconnected := by
      intro hpre
      have hcount := (preconnected_iff_componentCount_le_one _).mp hpre
      change 2 ≤ componentCount (componentDeleteVertex G v) at hcut
      omega
    obtain ⟨x, y, hxy⟩ : ∃ x y, ¬(componentDeleteVertex G v).Reachable x y := by
      simpa only [SimpleGraph.Preconnected, not_forall] using hn
    obtain ⟨a, hva, hax⟩ := exists_neighbor_reachable_after_delete v x
    obtain ⟨b, hvb, hby⟩ := exists_neighbor_reachable_after_delete v y
    obtain ⟨B, hB, _⟩ := edge_unique_block G v a.val hva
    obtain ⟨C, hC, _⟩ := edge_unique_block G v b.val hvb
    refine ⟨B, C, ?_, B.val.edge_vert hB, C.val.edge_vert hC⟩
    intro hBC
    subst C
    have hab := IsBlock.reachable_componentDeleteVertex B.property (B.val.edge_vert hB)
      (B.val.edge_vert hB.symm) (B.val.edge_vert hC.symm) a.property.2 b.property.2
    exact hxy (hax.symm.trans (hab.trans hby))
  · rintro ⟨B, C, hBC, hvB, hvC⟩
    by_contra hcut
    have hpre : (componentDeleteVertex G v).Preconnected := by
      apply (preconnected_iff_componentCount_le_one _).mpr
      change ¬2 ≤ componentCount (componentDeleteVertex G v) at hcut
      omega
    have hniso : ¬G.IsIsolated v := by
      intro hi
      exact hBC (Subtype.ext ((IsBlock.eq_singleton_of_isolated B.property hvB hi).trans
        (IsBlock.eq_singleton_of_isolated C.property hvC hi).symm))
    obtain ⟨a, hBa⟩ := (IsBlock.eq_singleton_or_exists_adj B.property hvB).resolve_left
      (fun h => hniso h.2)
    obtain ⟨b, hCb⟩ := (IsBlock.eq_singleton_or_exists_adj C.property hvC).resolve_left
      (fun h => hniso h.2)
    have hva : G.Adj v a := B.val.adj_sub hBa
    have hvb : G.Adj v b := C.val.adj_sub hCb
    let a' : {w : V // G.Reachable v w ∧ w ≠ v} := ⟨a, hva.reachable, hva.ne.symm⟩
    let b' : {w : V // G.Reachable v w ∧ w ≠ v} := ⟨b, hvb.reachable, hvb.ne.symm⟩
    obtain ⟨K, hKa, hKb⟩ := exists_block_of_reachable_after_delete v a' b' hva hvb
      (hpre a' b')
    have hBK : B = K := (edge_unique_block G v a hva).unique hBa hKa
    have hCK : C = K := (edge_unique_block G v b hvb).unique hCb hKb
    exact hBC (hBK.trans hCK.symm)

end FiniteCombinatorics.Graph.Blocks
