import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.TreeExchange
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.GraphicBridge

namespace P205.Matroids.TreeExchange
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.P205.Matroids.Graphic
open Specs.P205.Matroids.TreeExchange
noncomputable section
universe u v
variable {α : Type u} {β : Type v}

theorem unique_path : UniquePath.{u,v} := by
  intro α β G T hT x y
  exact hT.2.2.existsUnique_path x y

theorem pathLabels_nonempty : PathLabelsNonempty.{u,v} := by
  intro α β G T x y p hxy
  cases p with
  | nil => exact (hxy rfl).elim
  | @cons x z y h p =>
    obtain ⟨e, he, hel⟩ := h.2
    exact ⟨e, he, x, z, hel, by simp⟩

/-- Deleting a tree label deletes exactly its unordered shadow edge. -/
lemma shadow_delete (G : Graph α β) {T : Set β} (hT : SpanningTreeValue G T)
    {f : β} (hf : f ∈ T) {a b : G.vertexSet} (hl : G.IsLink f a.val b.val) :
    spanningShadow G (T \ {f}) = (spanningShadow G T).deleteEdges {s(a,b)} := by
  let := hT.2.1
  ext x y
  change (x ≠ y ∧ ∃ e, e ∈ T \ {f} ∧ G.IsLink e x.val y.val) ↔ _
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hne, e, he, hel⟩
    refine ⟨⟨hne, e, he.1, hel⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hab
    have hh : G.IsLink f x.val y.val := by
      rcases Sym2.eq_iff.mp hab with h | h
      · simpa only [h.1, h.2] using hl
      · simpa only [h.1, h.2] using hl.symm
    have : e = f := Graph.Simple.eq_of_isLink (G := G.restrict T) ⟨he.1, hel⟩ ⟨hf, hh⟩
    exact he.2 (this ▸ Set.mem_singleton f)
  · rintro ⟨⟨hne, e, he, hel⟩, hab⟩
    refine ⟨hne, e, ⟨he, ?_⟩, hel⟩
    intro hef
    have : e = f := hef
    subst e
    have hh := hel.eq_and_eq_or_eq_and_eq hl
    apply hab
    simp only [Set.mem_singleton_iff]
    rcases hh with ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hxa, Subtype.ext hyb⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hxb, Subtype.ext hya⟩)

lemma pathLabels_iff (G : Graph α β) {T : Set β} {x y : G.vertexSet}
    (p : (spanningShadow G T).Walk x y) {f : β} (hf : f ∈ T)
    {a b : G.vertexSet} (hl : G.IsLink f a.val b.val) :
    f ∈ pathLabels G T p ↔ s(a,b) ∈ p.edges := by
  constructor
  · rintro ⟨_, c, d, hcd, hp⟩
    have hh := hcd.eq_and_eq_or_eq_and_eq hl
    rcases hh with ⟨hca, hdb⟩ | ⟨hcb, hda⟩
    · simpa only [Subtype.ext hca, Subtype.ext hdb] using hp
    · simpa only [Subtype.ext hcb, Subtype.ext hda, Sym2.eq_swap] using hp
  · exact fun h => ⟨hf, a, b, hl, h⟩

lemma reachable_delete_iff (G : Graph α β) {T : Set β}
    (hT : SpanningTreeValue G T) {x y : G.vertexSet}
    (p : (spanningShadow G T).Walk x y) (hp : p.IsPath) {f : β} (hf : f ∈ T) :
    (spanningShadow G (T \ {f})).Reachable x y ↔ f ∉ pathLabels G T p := by
  classical
  obtain ⟨a, b, hl⟩ := G.exists_isLink_of_mem_edgeSet (hT.1 hf)
  let a' : G.vertexSet := ⟨a, hl.left_mem⟩
  let b' : G.vertexSet := ⟨b, hl.right_mem⟩
  rw [pathLabels_iff G p hf (a := a') (b := b') hl, shadow_delete G hT hf (a := a') (b := b') hl]
  constructor
  · intro hr
    obtain ⟨q, hq⟩ := hr.exists_isPath
    let leH := (spanningShadow G T).deleteEdges_le {s(a',b')}
    have heq : q.mapLe leH = p :=
      Subtype.mk.inj (hT.2.2.isAcyclic.subsingleton_path x y |>.elim
        ⟨q.mapLe leH, (SimpleGraph.Walk.isPath_mapLe leH).mpr hq⟩ ⟨p, hp⟩)
    intro hm
    have hm' : s(a',b') ∈ q.edges := by
      rw [← SimpleGraph.Walk.edges_mapLe_eq_edges leH q, heq]
      exact hm
    have hd := q.edges_subset_edgeSet hm'
    simp at hd
  · intro hn
    exact SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, hn⟩

/-- Inserting an edge into a one-edge-deleted base is independent exactly when
its endpoints are disconnected. This proof uses the incidence representation. -/
lemma exchange_iff_not_reachable (G : Graph α β) (hG : IsFiniteValue G)
    (hC : G.toSimpleGraph.Connected) {T : Set β} (hT : SpanningTreeValue G T)
    {f : β} (hf : f ∈ T) {e : β} {x y : G.vertexSet}
    (hl : G.IsLink e x.val y.val) (he : e ∉ T \ {f}) :
    SpanningTreeValue G (insert e (T \ {f})) ↔
      ¬ (spanningShadow G (T \ {f})).Reachable x y := by
  letI := hG.1.fintype
  let o : Orientation G := {
    tail := fun e => (G.exists_isLink_of_mem_edgeSet e.property).choose
    head := fun e => (G.exists_isLink_of_mem_edgeSet e.property).choose_spec.choose
    link := fun e => (G.exists_isLink_of_mem_edgeSet e.property).choose_spec.choose_spec }
  let M := incidenceMatroid G hG ℚ o
  have hb : M.IsBase T := (Graphic.connected_base_iff_tree G hG hC T).mpr hT
  have hi : M.Indep (T \ {f}) := hb.indep.subset Set.sdiff_subset
  have hi' : LinearIndepOn ℚ (column G ℚ o) (T \ {f}) := hi.2
  have hsub : T \ {f} ⊆ G.edgeSet := Set.sdiff_subset.trans hT.1
  rw [← Graphic.connected_base_iff_tree G hG hC]
  change M.IsBase (insert e (T \ {f})) ↔ _
  have hind : M.Indep (insert e (T \ {f})) ↔
      ¬ (spanningShadow G (T \ {f})).Reachable x y := by
    change (insert e (T \ {f}) ⊆ G.edgeSet ∧
      LinearIndepOn ℚ (column G ℚ o) (insert e (T \ {f}))) ↔ _
    rw [and_iff_right (Set.insert_subset hl.edge_mem hsub), linearIndepOn_insert he,
      and_iff_right hi', column_mem_span_iff G ℚ o hsub hl]
  constructor
  · exact fun h => hind.mp h.indep
  · intro h
    have hf' : f ∉ T \ {f} := by simp
    have hb' : M.IsBase (insert f (T \ {f})) := by
      simpa only [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hf] using hb
    exact Matroid.insert_isBase_of_insert_indep hf' he hb' (hind.mpr h)

theorem cut_exchange : CutExchange.{u,v} := by
  intro α β G hG hC T hT f hf e x y hl he
  exact exchange_iff_not_reachable G hG hC hT hf hl he

theorem path_exchange : PathExchange.{u,v} := by
  intro α β G hG hC T hT e x y hl he hxy p hp f hf
  rw [exchange_iff_not_reachable G hG hC hT hf hl
    (fun h => he h.1), reachable_delete_iff G hT p hp hf, not_not]

theorem crossing_reconnects : CrossingReconnects.{u,v} := by
  intro α β G hG hC T hT f hf e x y hl hcross
  have he : e ∉ T \ {f} := fun he => hcross (edge_reachable G he hl)
  exact (exchange_iff_not_reachable G hG hC hT hf hl he).mpr hcross

/-- Removing a tree edge gives two components, and every vertex belongs to
one of the two endpoint components. Isolated vertices are included in the count. -/
theorem delete_tree_edge : DeleteTreeEdge.{u,v} := by
  intro α β G hG T hT f hf a b hl
  have hC : G.toSimpleGraph.Connected := {
    preconnected := fun x y => (hT.2.2.connected x y).mono (by
      rw [← Graphic.spanningShadow_self G]
      exact shadow_mono G hT.1)
    nonempty := hT.2.2.connected.nonempty }
  have hF := ((Graphic.connected_spanningForest_iff_tree G hC T).mpr hT).2.1
  have hF' := hF.mono G (Set.sdiff_subset (t := {f}))
  have hcT : spanningComponentCount G T = 1 := by
    let := hT.2.2.connected.preconnected.subsingleton_connectedComponent
    let : Nonempty (spanningShadow G T).ConnectedComponent :=
      ⟨(spanningShadow G T).connectedComponentMk a⟩
    exact Nat.card_unique
  have hcardT := forest_cardinality G hG T hF
  have hcardI := forest_cardinality G hG (T \ {f}) hF'
  have hcard := Set.ncard_sdiff_singleton_add_one hf (hG.2.subset hT.1)
  have hc2 : spanningComponentCount G (T \ {f}) = 2 := by omega
  have hn : ¬ (spanningShadow G (T \ {f})).Reachable a b := by
    rw [shadow_delete G hT hf hl]
    have hab : (spanningShadow G T).Adj a b := by
      let := hT.2.1
      exact ⟨fun h => (show (G.restrict T).IsLink f a.val b.val from ⟨hf, hl⟩).ne
        (congrArg Subtype.val h), f, hf, hl⟩
    exact (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.2.2.isAcyclic hab)
  refine ⟨hc2, hn, ?_⟩
  let H := spanningShadow G (T \ {f})
  obtain ⟨c, hc, hu⟩ := (Nat.card_eq_two_iff' (H.connectedComponentMk a)).mp hc2
  have hb : H.connectedComponentMk b ≠ H.connectedComponentMk a := by
    intro h
    exact hn (SimpleGraph.ConnectedComponent.exact h.symm)
  intro z
  by_cases hz : H.connectedComponentMk z = H.connectedComponentMk a
  · exact Or.inl (SimpleGraph.ConnectedComponent.exact hz.symm)
  · exact Or.inr (SimpleGraph.ConnectedComponent.exact
      ((hu _ hb).trans (hu _ hz).symm))

end
end P205.Matroids.TreeExchange
