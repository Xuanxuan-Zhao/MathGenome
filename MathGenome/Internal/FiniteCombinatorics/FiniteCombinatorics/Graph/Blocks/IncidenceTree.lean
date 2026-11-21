import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Blocks.Membership
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Blocks.IncidenceTree

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FiniteCombinatorics.Graph.Blocks
open SimpleGraph

variable {V : Type u} [Finite V] {G : SimpleGraph V}

/-- Every vertex belongs to a block, including isolated vertices. -/
lemma exists_block_mem (v : V) : ∃ B : Block G, v ∈ B.val.verts := by
  classical
  by_cases hi : G.IsIsolated v
  · exact ⟨⟨G.singletonSubgraph v, isolated_isBlock G v hi⟩, rfl⟩
  · obtain ⟨w, hw⟩ : ∃ w, G.Adj v w := by
      simpa only [SimpleGraph.IsIsolated, not_forall, not_not] using hi
    obtain ⟨B, hB, _⟩ := edge_unique_block G v w hw
    exact ⟨B, B.val.edge_vert hB⟩

/-- A block containing a vertex of a component lies entirely in that component. -/
lemma block_subset_component (c : G.ConnectedComponent) (B : Block G)
    {v : V} (hv : v ∈ B.val.verts) (hc : v ∈ c.supp) : B.val.verts ⊆ c.supp := by
  intro w hw
  exact (c.mem_supp_iff w).mpr ((ConnectedComponent.sound
    ((B.property.connected ⟨w, hw⟩ ⟨v, hv⟩).map B.val.hom)).trans
      ((c.mem_supp_iff v).mp hc))

/-- Deleting an arbitrary ambient vertex leaves a block preconnected. -/
lemma IsBlock.preconnected_deleteVerts_any {H : G.Subgraph} (hH : IsBlock G H) (v : V) :
    (H.deleteVerts {v}).Preconnected := by
  by_cases hv : v ∈ H.verts
  · exact hH.preconnected_deleteVerts hv
  · have hs : H.verts ∩ ({v} : Set V) = ∅ := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hw he
      exact hv (he ▸ hw)
    rw [← Subgraph.deleteVerts_inter_verts_left_eq, hs, Subgraph.deleteVerts_empty]
    exact hH.connected.preconnected

/-- Remaining vertices of a block can be joined while avoiding any given vertex. -/
lemma IsBlock.reachable_deleteVertex {H : G.Subgraph} (hH : IsBlock G H)
    (v : V) {a b : V} (ha : a ∈ H.verts) (hb : b ∈ H.verts)
    (hav : a ≠ v) (hbv : b ≠ v) :
    (deleteVertex G v).Reachable ⟨a, hav⟩ ⟨b, hbv⟩ := by
  let f : (H.deleteVerts {v}).coe →g deleteVertex G v := {
    toFun := fun x => ⟨x.val, x.property.2⟩
    map_rel' := fun h => (H.deleteVerts {v}).adj_sub h }
  exact (hH.preconnected_deleteVerts_any v ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩).map f

/-- A cut vertex cannot exhaust the vertices of a block. -/
lemma block_exists_ne_cut (v : V) (hv : CutVertex G v) (B : Block G) :
    ∃ w ∈ B.val.verts, w ≠ v := by
  classical
  obtain ⟨w, hw⟩ := B.property.connected.nonempty
  by_cases hwv : w = v
  · have hvB : v ∈ B.val.verts := hwv ▸ hw
    rcases B.property.eq_singleton_or_exists_adj hvB with ⟨_, hi⟩ | ⟨a, ha⟩
    · exact (isolated_not_cutVertex G v hi hv).elim
    · exact ⟨a, B.val.edge_vert ha.symm, (B.val.adj_sub ha).ne.symm⟩
  · exact ⟨w, hw, hwv⟩

/-- A walk in the whole vertex-deleted graph remains in the starting component. -/
lemma reachable_componentDeleteVertex_of_deleteVertex {v a b : V}
    (ha : G.Reachable v a) (hb : G.Reachable v b) (hav : a ≠ v) (hbv : b ≠ v)
    (h : (deleteVertex G v).Reachable ⟨a, hav⟩ ⟨b, hbv⟩) :
    (componentDeleteVertex G v).Reachable ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩ := by
  classical
  obtain ⟨p⟩ := h
  let q := p.map (SimpleGraph.Embedding.induce _).toHom
  have hmem (w : V) (hw : w ∈ q.support) : G.Reachable v w ∧ w ≠ v := by
    refine ⟨ha.trans (q.takeUntil w hw).reachable, ?_⟩
    rw [Walk.support_map] at hw
    obtain ⟨x, _, hx⟩ := List.mem_map.mp hw
    exact hx ▸ x.property
  exact (q.induce _ hmem).reachable

private def nodeVertices : BlockCutNode G → Set V
  | .inl B => B.val.verts
  | .inr w => {w.val}

private lemma node_exists_ne_cut (v : V) (hv : CutVertex G v)
    (x : BlockCutNode G) (hx : x ≠ .inr ⟨v, hv⟩) :
    ∃ a ∈ nodeVertices x, a ≠ v := by
  cases x with
  | inl B => exact block_exists_ne_cut v hv B
  | inr w =>
    refine ⟨w.val, rfl, ?_⟩
    intro he
    exact hx (congrArg Sum.inr (Subtype.ext he))

private lemma node_reachable_deleteVertex (v : V) (x : BlockCutNode G)
    {a b : V} (ha : a ∈ nodeVertices x) (hb : b ∈ nodeVertices x)
    (hav : a ≠ v) (hbv : b ≠ v) :
    (deleteVertex G v).Reachable ⟨a, hav⟩ ⟨b, hbv⟩ := by
  cases x with
  | inl B => exact B.property.reachable_deleteVertex v ha hb hav hbv
  | inr w =>
    have hab : (⟨a, hav⟩ : {w : V // w ≠ v}) = ⟨b, hbv⟩ :=
      Subtype.ext (ha.trans hb.symm)
    rw [hab]

private lemma adjacent_reachable_deleteVertex (v : V) (hv : CutVertex G v)
    {x y : BlockCutNode G} (h : (blockCutGraph G).Adj x y)
    (hx : x ≠ .inr ⟨v, hv⟩) (hy : y ≠ .inr ⟨v, hv⟩)
    {a b : V} (ha : a ∈ nodeVertices x) (hb : b ∈ nodeVertices y)
    (hav : a ≠ v) (hbv : b ≠ v) :
    (deleteVertex G v).Reachable ⟨a, hav⟩ ⟨b, hbv⟩ := by
  cases x with
  | inl B =>
    cases y with
    | inl C => exact h.elim
    | inr w =>
      have he : b = w.val := hb
      exact B.property.reachable_deleteVertex v ha (he.symm ▸ h) hav hbv
  | inr w =>
    cases y with
    | inr z => exact h.elim
    | inl B =>
      have he : a = w.val := ha
      exact B.property.reachable_deleteVertex v (he.symm ▸ h) hb hav hbv

/-- Lift a block–cut walk avoiding a cut node to a walk avoiding that vertex. -/
private lemma walk_avoiding_cut_reachable (v : V) (hv : CutVertex G v)
    {x y : BlockCutNode G} (p : (blockCutGraph G).Walk x y)
    (hp : Sum.inr ⟨v, hv⟩ ∉ p.support)
    {a b : V} (ha : a ∈ nodeVertices x) (hb : b ∈ nodeVertices y)
    (hav : a ≠ v) (hbv : b ≠ v) :
    (deleteVertex G v).Reachable ⟨a, hav⟩ ⟨b, hbv⟩ := by
  induction p generalizing a b with
  | nil => exact node_reachable_deleteVertex v _ ha hb hav hbv
  | @cons x z y hxz p ih =>
    change Sum.inr ⟨v, hv⟩ ∉ x :: p.support at hp
    have hx : x ≠ .inr ⟨v, hv⟩ := by
      intro he
      exact hp (List.mem_cons.mpr (Or.inl he.symm))
    have hp' : Sum.inr ⟨v, hv⟩ ∉ p.support :=
      fun h => hp (List.mem_cons.mpr (Or.inr h))
    have hz : z ≠ .inr ⟨v, hv⟩ := by
      intro he
      exact hp' (he ▸ p.start_mem_support)
    obtain ⟨c, hc, hcv⟩ := node_exists_ne_cut v hv z hz
    exact (adjacent_reachable_deleteVertex v hv hxz hx hz ha hc hav hcv).trans
      (ih hp' hc hb hcv hbv)

/-- Each incidence edge separates the block from its incident cut node. -/
lemma blockCutGraph_incidence_isBridge (v : V) (hv : CutVertex G v)
    (B : Block G) (hvB : v ∈ B.val.verts) :
    (blockCutGraph G).IsBridge s(Sum.inr ⟨v, hv⟩, Sum.inl B) := by
  classical
  intro hreach
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  cases p with
  | @cons _ x _ h p =>
    have h' := SimpleGraph.deleteEdges_adj.mp h
    cases x with
    | inr w => exact h'.1.elim
    | inl C =>
      have hvC : v ∈ C.val.verts := h'.1
      have hCB : C ≠ B := by
        intro he
        subst C
        exact h'.2 rfl
      have hp' : Sum.inr ⟨v, hv⟩ ∉ p.support :=
        (Walk.cons_isPath_iff _ _).mp hp |>.2
      let q := p.map (Hom.ofLE (SimpleGraph.deleteEdges_le _))
      have hq : Sum.inr ⟨v, hv⟩ ∉ q.support := by
        change Sum.inr ⟨v, hv⟩ ∉ (p.map (Hom.ofLE (SimpleGraph.deleteEdges_le _))).support
        rw [Walk.support_map]
        change Sum.inr ⟨v, hv⟩ ∉ p.support.map id
        simpa only [List.map_id] using hp'
      obtain ⟨a, hCa⟩ := (IsBlock.eq_singleton_or_exists_adj C.property hvC).resolve_left
        (fun hi => isolated_not_cutVertex G v hi.2 hv)
      obtain ⟨b, hBb⟩ := (B.property.eq_singleton_or_exists_adj hvB).resolve_left
        (fun hi => isolated_not_cutVertex G v hi.2 hv)
      have hva : G.Adj v a := C.val.adj_sub hCa
      have hvb : G.Adj v b := B.val.adj_sub hBb
      have hr := walk_avoiding_cut_reachable v hv q hq
        (C.val.edge_vert hCa.symm) (B.val.edge_vert hBb.symm) hva.ne.symm hvb.ne.symm
      have hr' := reachable_componentDeleteVertex_of_deleteVertex hva.reachable hvb.reachable
        hva.ne.symm hvb.ne.symm hr
      obtain ⟨K, hKa, hKb⟩ := exists_block_of_reachable_after_delete v
        ⟨a, hva.reachable, hva.ne.symm⟩ ⟨b, hvb.reachable, hvb.ne.symm⟩ hva hvb hr'
      have hCK : C = K := (edge_unique_block G v a hva).unique hCa hKa
      have hBK : B = K := (edge_unique_block G v b hvb).unique hBb hKb
      exact hCB (hCK.trans hBK.symm)

/-- The full block–cut graph is a forest, also for disconnected ambient graphs. -/
lemma blockCutGraph_isAcyclic (G : SimpleGraph V) : (blockCutGraph G).IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
  intro x y hxy
  cases x with
  | inl B =>
    cases y with
    | inl C => exact hxy.elim
    | inr v =>
      exact Sym2.eq_swap ▸ blockCutGraph_incidence_isBridge v.val v.property B hxy
  | inr v =>
    cases y with
    | inr w => exact hxy.elim
    | inl B => exact blockCutGraph_incidence_isBridge v.val v.property B hxy

/-- Blocks sharing a vertex are joined, through a cut node when they are distinct. -/
lemma component_blocks_reachable_of_common_vertex (c : G.ConnectedComponent)
    (B C : Block G) (hB : B.val.verts ⊆ c.supp) (hC : C.val.verts ⊆ c.supp)
    {v : V} (hvB : v ∈ B.val.verts) (hvC : v ∈ C.val.verts) :
    (componentBlockCutGraph G c).Reachable ⟨.inl B, hB⟩ ⟨.inl C, hC⟩ := by
  by_cases hBC : B = C
  · subst C
    exact Reachable.rfl
  · have hcut : CutVertex G v :=
      (cutVertex_iff_mem_two_blocks G v).mpr ⟨B, C, hBC, hvB, hvC⟩
    let w : componentNodes G c := ⟨.inr ⟨v, hcut⟩, hB hvB⟩
    have h₁ : (componentBlockCutGraph G c).Adj ⟨.inl B, hB⟩ w := hvB
    have h₂ : (componentBlockCutGraph G c).Adj w ⟨.inl C, hC⟩ := hvC
    exact h₁.reachable.trans h₂.reachable

/-- Follow original edges through their unique blocks, retaining the component. -/
lemma component_blocks_reachable_of_walk (c : G.ConnectedComponent) {a b : V}
    (p : G.Walk a b) (B C : Block G)
    (hB : B.val.verts ⊆ c.supp) (hC : C.val.verts ⊆ c.supp)
    (ha : a ∈ B.val.verts) (hb : b ∈ C.val.verts) :
    (componentBlockCutGraph G c).Reachable ⟨.inl B, hB⟩ ⟨.inl C, hC⟩ := by
  induction p generalizing B with
  | nil => exact component_blocks_reachable_of_common_vertex c B C hB hC ha hb
  | @cons a z b haz p ih =>
    obtain ⟨D, hD, _⟩ := edge_unique_block G a z haz
    have hDc : D.val.verts ⊆ c.supp :=
      block_subset_component c D (D.val.edge_vert hD) (hB ha)
    exact (component_blocks_reachable_of_common_vertex c B D hB hDc ha
      (D.val.edge_vert hD)).trans (ih D hDc (D.val.edge_vert hD.symm) hb)

/-- Every component incidence node can reach a block node of that component. -/
lemma component_node_reachable_block (c : G.ConnectedComponent) (x : componentNodes G c) :
    ∃ (B : Block G) (hB : B.val.verts ⊆ c.supp),
      (componentBlockCutGraph G c).Reachable x ⟨.inl B, hB⟩ := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl B => exact ⟨B, hx, Reachable.rfl⟩
  | inr v =>
    obtain ⟨B, hvB⟩ := exists_block_mem (G := G) v.val
    have hB := block_subset_component c B hvB hx
    exact ⟨B, hB, (show (componentBlockCutGraph G c).Adj
      ⟨.inr v, hx⟩ ⟨.inl B, hB⟩ from hvB).reachable⟩

/-- Connectivity holds for the actual componentwise incidence graph. -/
lemma componentBlockCutGraph_connected (G : SimpleGraph V) (c : G.ConnectedComponent) :
    (componentBlockCutGraph G c).Connected := by
  classical
  have hnonempty : Nonempty (componentNodes G c) := by
    obtain ⟨v, hv⟩ := c.nonempty_supp
    obtain ⟨B, hvB⟩ := exists_block_mem (G := G) v
    exact ⟨⟨.inl B, block_subset_component c B hvB hv⟩⟩
  refine { preconnected := ?_, nonempty := hnonempty }
  intro x y
  obtain ⟨B, hB, hx⟩ := component_node_reachable_block c x
  obtain ⟨C, hC, hy⟩ := component_node_reachable_block c y
  obtain ⟨a, ha⟩ := B.property.connected.nonempty
  obtain ⟨b, hb⟩ := C.property.connected.nonempty
  obtain ⟨p⟩ := c.reachable_of_mem_supp (hB ha) (hC hb)
  exact hx.trans ((component_blocks_reachable_of_walk c p B C hB hC ha hb).trans hy.symm)

/-- W38: every connected component has a nonempty, connected, acyclic block–cut graph. -/
theorem componentBlockCutGraph_isTree :
    Specs.FiniteCombinatorics.Graph.Blocks.IncidenceTree.componentBlockCutGraph_isTreeType := by
  intro V _ G c
  exact ⟨componentBlockCutGraph_connected G c,
    (blockCutGraph_isAcyclic G).comap (SimpleGraph.Embedding.induce _).toHom
      Subtype.val_injective⟩

/-- W38's boundary case: the entire isolated component consists of one block node. -/
theorem isolated_component_nodes :
    Specs.FiniteCombinatorics.Graph.Blocks.IncidenceTree.isolated_component_nodesType := by
  intro V _ G v hi
  classical
  have hs : (G.connectedComponentMk v).supp = {v} := by
    ext w
    constructor
    · intro hw
      have hr : G.Reachable v w := ConnectedComponent.exact
        (((G.connectedComponentMk v).mem_supp_iff w).mp hw).symm
      by_contra hne
      change w ≠ v at hne
      exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
        hne.symm hi.neighborSet_eq_empty hr
    · intro hw
      have he : w = v := hw
      subst w
      exact ((G.connectedComponentMk v).mem_supp_iff v).mpr rfl
  let B : Block G := ⟨G.singletonSubgraph v, isolated_isBlock G v hi⟩
  refine ⟨B, rfl, ?_⟩
  ext x
  cases x with
  | inl C =>
    change (C.val.verts ⊆ (G.connectedComponentMk v).supp) ↔ Sum.inl C ∈ {Sum.inl B}
    rw [hs]
    constructor
    · intro hC
      obtain ⟨w, hw⟩ := (IsBlock.connected C.property).nonempty
      have hwv : w = v := hC hw
      have hvC : v ∈ C.val.verts := hwv ▸ hw
      have hCB : C = B := Subtype.ext (IsBlock.eq_singleton_of_isolated C.property hvC hi)
      simp only [hCB, Set.mem_singleton_iff]
    · intro hx
      have hCB : C = B := Sum.inl.inj (Set.mem_singleton_iff.mp hx)
      subst C
      exact Set.Subset.rfl
  | inr w =>
    change w.val ∈ (G.connectedComponentMk v).supp ↔ Sum.inr w ∈ {Sum.inl B}
    rw [hs]
    constructor
    · intro hw
      have he : w.val = v := hw
      exact (isolated_not_cutVertex G v hi (he ▸ w.property)).elim
    · intro hx
      have he : (Sum.inr w : BlockCutNode G) = Sum.inl B := hx
      cases he

end FiniteCombinatorics.Graph.Blocks
