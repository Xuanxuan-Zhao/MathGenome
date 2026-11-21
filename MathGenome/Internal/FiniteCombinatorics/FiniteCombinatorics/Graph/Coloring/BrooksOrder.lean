import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Blocks.IncidenceTree
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.BrooksOrder
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Basic.Finite.Sum

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Coloring
set_option backward.isDefEq.respectTransparency false
open SimpleGraph
open FiniteCombinatorics.Graph.Blocks

variable {V : Type u} [Finite V] {G : SimpleGraph V}

omit [Finite V] in
/-- A connected noncomplete graph contains an induced three-vertex path. -/
lemma exists_nonadjacent_neighbors (hc : G.Connected) (hn : G ≠ ⊤) :
    ∃ v a b : V, a ≠ b ∧ G.Adj v a ∧ G.Adj v b ∧ ¬ G.Adj a b := by
  classical
  obtain ⟨a, b, hab, hnab⟩ : ∃ a b : V, a ≠ b ∧ ¬ G.Adj a b := by
    exact SimpleGraph.ne_top_iff_exists_not_adj.mp hn
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a b
  have hd : 1 < G.dist a b := by
    have hzero : G.dist a b ≠ 0 := fun h => hab (hc.dist_eq_zero_iff.mp h)
    have hone : G.dist a b ≠ 1 := fun h => hnab (dist_eq_one_iff_adj.mp h)
    omega
  obtain ⟨a', v, b', hav, hvb, hnab', hne⟩ := p.exists_adj_adj_not_adj_ne hp hd
  exact ⟨v, a', b', hne, hav.symm, hvb, hnab'⟩

omit [Finite V] in
/-- The first case in the source proof: no pair of distinct vertices separates G. -/
lemma two_initial_vertices_of_pair_deletions_connected
    (hc : G.Connected) (hn : G ≠ ⊤)
    (hdel : ∀ a b : V, a ≠ b → (G.induce {x | x ≠ a ∧ x ≠ b}).Connected) :
    ∃ v a b : V, a ≠ b ∧ G.Adj v a ∧ G.Adj v b ∧ ¬ G.Adj a b ∧
      (G.induce {x | x ≠ a ∧ x ≠ b}).Connected := by
  obtain ⟨v, a, b, hab, hva, hvb, hnab⟩ := exists_nonadjacent_neighbors hc hn
  exact ⟨v, a, b, hab, hva, hvb, hnab, hdel a b hab⟩

/-- A leaf block has exactly one ambient cut vertex. -/
def LeafBlock (G : SimpleGraph V) (B : Block G) (t : V) : Prop :=
  CutVertex G t ∧ t ∈ B.val.verts ∧ ∀ x ∈ B.val.verts, CutVertex G x → x = t

lemma blockCutGraph_connected (hc : G.Connected) : (blockCutGraph G).Connected := by
  obtain ⟨r⟩ := hc.nonempty
  let c := G.connectedComponentMk r
  have hmem (x : V) : x ∈ c.supp :=
    (c.mem_supp_iff x).mpr (ConnectedComponent.sound (hc x r))
  have hn (x : BlockCutNode G) : componentNodes G c x := by
    cases x with
    | inl B => exact fun x _ => hmem x
    | inr v => exact hmem v.val
  refine { nonempty := ⟨.inl (Classical.choose (exists_block_mem (G := G) r))⟩,
           preconnected := ?_ }
  intro x y
  exact (componentBlockCutGraph_connected G c ⟨x, hn x⟩ ⟨y, hn y⟩).map
    (SimpleGraph.Embedding.induce _).toHom

/-- Cut nodes cannot be leaves: each is incident with at least two distinct blocks. -/
lemma cut_node_not_unique_neighbor (t : V) (ht : CutVertex G t)
    (y : BlockCutNode G) :
    ¬ (∀ z, (blockCutGraph G).Adj (.inr ⟨t, ht⟩) z → z = y) := by
  obtain ⟨B, C, hBC, htB, htC⟩ := (cutVertex_iff_mem_two_blocks G t).mp ht
  intro hu
  exact hBC (Sum.inl.inj ((hu (.inl B) htB).trans (hu (.inl C) htC).symm))

/-- A connected graph with a cut vertex has two different leaf blocks. -/
lemma exists_two_leafBlocks (hc : G.Connected) (hcut : ∃ t, CutVertex G t) :
    ∃ (B C : Block G) (t s : V), B ≠ C ∧ LeafBlock G B t ∧ LeafBlock G C s := by
  classical
  let T : SimpleGraph (BlockCutNode G) := blockCutGraph G
  have ht : T.IsTree := ⟨blockCutGraph_connected hc, blockCutGraph_isAcyclic G⟩
  obtain ⟨w, hw⟩ := hcut
  obtain ⟨D, hwD⟩ := exists_block_mem (G := G) w
  have : Nontrivial (BlockCutNode G) :=
    ⟨⟨.inl D, .inr ⟨w, hw⟩, by simp⟩⟩
  have : Finite (Block G) := by
    change Finite {H : G.Subgraph // IsBlock G H}
    infer_instance
  have : Finite (BlockCutNode G) := by
    change Finite (Block G ⊕ {v : V // CutVertex G v})
    infer_instance
  let _ := Fintype.ofFinite (BlockCutNode G)
  let _ : DecidableRel T.Adj := Classical.decRel _
  obtain ⟨x, y, hxy, hx, hy⟩ := ht.exists_ne_and_degree_eq_one
  have hleaf (x : BlockCutNode G) (hx : T.degree x = 1) :
      ∃ (B : Block G) (t : V), x = .inl B ∧ LeafBlock G B t := by
    obtain ⟨z, hxz, hz⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
    cases x with
    | inr v => exact (cut_node_not_unique_neighbor v.val v.property z hz).elim
    | inl B =>
      cases z with
      | inl C => exact hxz.elim
      | inr t =>
        refine ⟨B, t.val, rfl, t.property, hxz, ?_⟩
        intro a ha hacut
        have he := hz (.inr ⟨a, hacut⟩) ha
        exact congrArg Subtype.val (Sum.inr.inj he)
  obtain ⟨B, t, rfl, hB⟩ := hleaf x hx
  obtain ⟨C, s, rfl, hC⟩ := hleaf y hy
  exact ⟨B, C, t, s, fun h => hxy (congrArg Sum.inl h), hB, hC⟩

/-- An interior vertex of a leaf block belongs to no other block. -/
lemma LeafBlock.unique_block {B : Block G} {t a : V} (hB : LeafBlock G B t)
    (ha : a ∈ B.val.verts) (hat : a ≠ t) (C : Block G) (haC : a ∈ C.val.verts) :
    C = B := by
  by_contra hCB
  have hacut := (cutVertex_iff_mem_two_blocks G a).mpr ⟨C, B, hCB, haC, ha⟩
  exact hat (hB.2.2 a ha hacut)

/-- No ambient edge can leave a leaf block through an interior vertex. -/
lemma LeafBlock.neighbor_mem {B : Block G} {t a x : V} (hB : LeafBlock G B t)
    (ha : a ∈ B.val.verts) (hat : a ≠ t) (hax : G.Adj a x) : x ∈ B.val.verts := by
  obtain ⟨C, hC, _⟩ := edge_unique_block G a x hax
  have he := hB.unique_block ha hat C (C.val.edge_vert hC)
  exact he ▸ C.val.edge_vert hC.symm

omit [Finite V] in
lemma reachable_mem_of_adj_closed {s : Set V}
    (hs : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s) {a b : V}
    (hab : G.Reachable a b) (ha : a ∈ s) : b ∈ s := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact ha
  | @cons x y z hxy p ih => exact ih (hs x ha y hxy)

/-- Two-connectivity forces a neighbor of v in every leaf-block interior of G-v. -/
lemma exists_neighbor_in_leafBlock (hG : TwoConnected G) (v : V)
    (B : Block (deleteVertex G v)) (t : {x : V // x ≠ v})
    (hB : LeafBlock (deleteVertex G v) B t) :
    ∃ a : {x : V // x ≠ v}, a ∈ B.val.verts ∧ a ≠ t ∧ G.Adj v a.val := by
  classical
  obtain ⟨a, ha, hat⟩ := block_exists_ne_cut t hB.1 B
  by_contra! hn
  let S : Set {x : V // x ≠ t.val} :=
    {x | ∃ hx : x.val ≠ v, (⟨x.val, hx⟩ : {x : V // x ≠ v}) ∈ B.val.verts}
  have hatval : a.val ≠ t.val := fun h => hat (Subtype.ext h)
  have hclosed : ∀ x ∈ S, ∀ y, (deleteVertex G t.val).Adj x y → y ∈ S := by
    rintro x ⟨hxv, hxB⟩ y hxy
    have hxt : (⟨x.val, hxv⟩ : {x : V // x ≠ v}) ≠ t :=
      fun h => x.property (congrArg Subtype.val h)
    have hyv : y.val ≠ v := by
      intro he
      have hvx : G.Adj v x.val := by
        simpa only [he] using (show G.Adj y.val x.val from hxy.symm)
      exact hn ⟨x.val, hxv⟩ hxB hxt hvx
    exact ⟨hyv, hB.neighbor_mem hxB hxt (show
      (deleteVertex G v).Adj ⟨x.val, hxv⟩ ⟨y.val, hyv⟩ from hxy)⟩
  have hv : v ≠ t.val := t.property.symm
  have hr := hG.2.2 t.val ⟨a.val, hatval⟩ ⟨v, hv⟩
  have hvs := reachable_mem_of_adj_closed hclosed hr (show
    (⟨a.val, hatval⟩ : {x : V // x ≠ t.val}) ∈ S from ⟨a.property, ha⟩)
  obtain ⟨hvv, _⟩ := hvs
  exact hvv rfl

omit [Finite V] in
/-- Reachability can be transported by a vertex map that sends edges to walks. -/
lemma reachable_map_of_adj_reachable {W : Type u} {K : SimpleGraph W} (f : V → W)
    (hf : ∀ x y, G.Adj x y → K.Reachable (f x) (f y)) {a b : V}
    (hab : G.Reachable a b) : K.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact Reachable.rfl
  | @cons x y z hxy p ih => exact (hf x y hxy).trans ih

omit [Finite V] in
/-- Reroute each removed vertex to an anchor in the remainder. -/
lemma connected_delete_pair_of_anchors (hc : G.Connected) (a b : V) (hab : a ≠ b)
    (t s : {x : V // x ≠ a ∧ x ≠ b})
    (ha : ∀ y, G.Adj a y → ∃ hy : y ≠ a ∧ y ≠ b,
      (G.induce {x | x ≠ a ∧ x ≠ b}).Reachable t ⟨y, hy⟩)
    (hb : ∀ y, G.Adj b y → ∃ hy : y ≠ a ∧ y ≠ b,
      (G.induce {x | x ≠ a ∧ x ≠ b}).Reachable s ⟨y, hy⟩) :
    (G.induce {x | x ≠ a ∧ x ≠ b}).Connected := by
  classical
  let K := G.induce {x | x ≠ a ∧ x ≠ b}
  let f : V → {x : V // x ≠ a ∧ x ≠ b} :=
    fun x => if hxa : x = a then t else if hxb : x = b then s else ⟨x, hxa, hxb⟩
  have fa : f a = t := by simp [f]
  have fb : f b = s := by simp [f, hab.symm]
  have fkeep (x : V) (hx : x ≠ a ∧ x ≠ b) : f x = ⟨x, hx⟩ := by
    simp [f, hx.1, hx.2]
  have hf (x y : V) (hxy : G.Adj x y) : K.Reachable (f x) (f y) := by
    by_cases hxa : x = a
    · subst x
      obtain ⟨hy, hr⟩ := ha y hxy
      rw [fa, fkeep y hy]
      exact hr
    by_cases hxb : x = b
    · subst x
      obtain ⟨hy, hr⟩ := hb y hxy
      rw [fb, fkeep y hy]
      exact hr
    by_cases hya : y = a
    · subst y
      obtain ⟨hx, hr⟩ := ha x hxy.symm
      rw [fa, fkeep x hx]
      exact hr.symm
    by_cases hyb : y = b
    · subst y
      obtain ⟨hx, hr⟩ := hb x hxy.symm
      rw [fb, fkeep x hx]
      exact hr.symm
    rw [fkeep x ⟨hxa, hxb⟩, fkeep y ⟨hya, hyb⟩]
    exact (show K.Adj ⟨x, hxa, hxb⟩ ⟨y, hya, hyb⟩ from hxy).reachable
  refine { nonempty := ⟨t⟩, preconnected := ?_ }
  intro x y
  have hr := reachable_map_of_adj_reachable f hf (hc x.val y.val)
  rw [fkeep x.val x.property, fkeep y.val y.property] at hr
  exact hr

/-- Inside a block, deleting an interior vertex still joins every remaining pair;
a vertex outside the block is automatically avoided as well. -/
lemma block_reachable_avoiding_pair (B : Block G) (a b : V)
    (hb : b ∉ B.val.verts) {x y : V}
    (hx : x ∈ B.val.verts) (hy : y ∈ B.val.verts) (hxa : x ≠ a) (hya : y ≠ a) :
    (G.induce {z | z ≠ a ∧ z ≠ b}).Reachable
      ⟨x, hxa, fun h => hb (h ▸ hx)⟩ ⟨y, hya, fun h => hb (h ▸ hy)⟩ := by
  let f : (B.val.deleteVerts {a}).coe →g G.induce {z | z ≠ a ∧ z ≠ b} := {
    toFun := fun z => ⟨z.val, z.property.2, fun h => hb (h ▸ z.property.1)⟩
    map_rel' := fun h => (B.val.deleteVerts {a}).adj_sub h }
  exact (B.property.preconnected_deleteVerts_any a ⟨x, hx, hxa⟩ ⟨y, hy, hya⟩).map f

/-- Interior vertices of different leaf blocks are nonadjacent and can be
deleted simultaneously without disconnecting the graph. -/
lemma leafBlock_pair_deletion (hc : G.Connected)
    (B C : Block G) (t s a b : V) (hBC : B ≠ C)
    (hB : LeafBlock G B t) (hC : LeafBlock G C s)
    (ha : a ∈ B.val.verts) (hat : a ≠ t)
    (hb : b ∈ C.val.verts) (hbs : b ≠ s) :
    a ≠ b ∧ ¬ G.Adj a b ∧ (G.induce {x | x ≠ a ∧ x ≠ b}).Connected := by
  have hbB : b ∉ B.val.verts := fun h => hBC (hC.unique_block hb hbs B h)
  have haC : a ∉ C.val.verts := fun h => hBC (hB.unique_block ha hat C h).symm
  have hab : a ≠ b := fun h => hbB (h ▸ ha)
  have hnab : ¬G.Adj a b := fun h => hbB (hB.neighbor_mem ha hat h)
  have hta : t ≠ a := hat.symm
  have htb : t ≠ b := fun h => hbB (h ▸ hB.2.1)
  have hsa : s ≠ a := fun h => haC (h ▸ hC.2.1)
  have hsb : s ≠ b := hbs.symm
  refine ⟨hab, hnab, connected_delete_pair_of_anchors hc a b hab
    ⟨t, hta, htb⟩ ⟨s, hsa, hsb⟩ ?_ ?_⟩
  · intro y hay
    have hy := hB.neighbor_mem ha hat hay
    refine ⟨⟨hay.ne.symm, fun h => hbB (h ▸ hy)⟩, ?_⟩
    exact block_reachable_avoiding_pair B a b hbB hB.2.1 hy hta hay.ne.symm
  · intro y hby
    have hy := hC.neighbor_mem hb hbs hby
    refine ⟨⟨fun h => haC (h ▸ hy), hby.ne.symm⟩, ?_⟩
    let f : G.induce {z | z ≠ b ∧ z ≠ a} →g G.induce {z | z ≠ a ∧ z ≠ b} := {
      toFun := fun z => ⟨z.val, z.property.2, z.property.1⟩
      map_rel' := fun h => h }
    exact (block_reachable_avoiding_pair C b a haC hC.2.1 hy hsb hby.ne.symm).map f

/-- For a connected graph, failure of preconnectedness after deletion detects
a cut vertex under the component-local convention of the shared interface. -/
lemma cutVertex_of_not_preconnected_delete (hc : G.Connected) (t : V)
    (hn : ¬ (deleteVertex G t).Preconnected) : CutVertex G t := by
  by_contra hcut
  have hpre : (componentDeleteVertex G t).Preconnected := by
    apply (preconnected_iff_componentCount_le_one _).mpr
    change ¬ 2 ≤ FiniteCombinatorics.Graph.componentCount (componentDeleteVertex G t) at hcut
    omega
  let f : componentDeleteVertex G t →g deleteVertex G t := {
    toFun := fun x => ⟨x.val, x.property.2⟩
    map_rel' := fun h => h }
  exact hn (hpre.map f (fun x => ⟨⟨x.val, hc t x.val, x.property⟩, rfl⟩))

/-- Nested vertex deletions and simultaneous deletion describe the same graph. -/
def deletePairIso (a b : V) (hba : b ≠ a) :
    deleteVertex (deleteVertex G a) ⟨b, hba⟩ ≃g G.induce {x | x ≠ a ∧ x ≠ b} where
  toFun x := ⟨x.val.val, x.val.property, fun h => x.property (Subtype.ext h)⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, fun h => x.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Minimum degree at least three leaves a neighbor after two vertices are removed. -/
lemma exists_third_neighbor (v a b : V)
    (hd : 3 ≤ FiniteCombinatorics.Graph.degree G v) :
    ∃ c : V, G.Adj v c ∧ c ≠ a ∧ c ≠ b := by
  classical
  by_contra! hn
  have hsub : G.neighborSet v ⊆ ({a, b} : Set V) := by
    intro c hc
    by_cases hca : c = a
    · exact Or.inl hca
    · exact Or.inr (hn c hc hca)
  have hcard : Nat.card (G.neighborSet v) ≤ 2 := by
    calc
      Nat.card (G.neighborSet v) = (G.neighborSet v).ncard := rfl
      _ ≤ ({a, b} : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by by_cases h : a = b <;> simp [h]
  change 3 ≤ Nat.card (G.neighborSet v) at hd
  omega

/-- Add back a vertex with a remaining neighbor to a connected induced graph. -/
lemma connected_add_vertex_after_pair_deletion (v a b : V) (hav : a ≠ v) (hbv : b ≠ v)
    (hc : ((deleteVertex G v).induce {x | x.val ≠ a ∧ x.val ≠ b}).Connected)
    (hd : 3 ≤ FiniteCombinatorics.Graph.degree G v) :
    (G.induce {x | x ≠ a ∧ x ≠ b}).Connected := by
  obtain ⟨c, hvc, hca, hcb⟩ := exists_third_neighbor v a b hd
  let K := G.induce {x | x ≠ a ∧ x ≠ b}
  let r : {x : V // x ≠ a ∧ x ≠ b} := ⟨v, hav.symm, hbv.symm⟩
  let f : (deleteVertex G v).induce {x | x.val ≠ a ∧ x.val ≠ b} →g K := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    map_rel' := fun h => h }
  have hvreach (x : {x : V // x ≠ a ∧ x ≠ b}) : K.Reachable r x := by
    by_cases hxv : x.val = v
    · have he : x = r := Subtype.ext hxv
      rw [he]
    · have he : K.Adj r ⟨c, hca, hcb⟩ := hvc
      exact he.reachable.trans ((hc ⟨⟨c, hvc.ne.symm⟩, hca, hcb⟩
        ⟨⟨x.val, hxv⟩, x.property⟩).map f)
  exact { nonempty := ⟨r⟩, preconnected := fun x y => (hvreach x).symm.trans (hvreach y) }

/-- The structural lemma p204:brooks-order, with its full minimum-degree
hypothesis and no assumption of regularity. -/
theorem two_initial_vertices :
    Specs.FiniteCombinatorics.Graph.Coloring.BrooksOrder.two_initial_verticesType.{u} := by
  intro V _ G hG hn hd
  classical
  by_cases hp : ∀ a b : V, a ≠ b → (G.induce {x | x ≠ a ∧ x ≠ b}).Connected
  · exact two_initial_vertices_of_pair_deletions_connected hG.2.1 hn hp
  push Not at hp
  obtain ⟨v, w, hvw, hdisconn⟩ := hp
  let H := deleteVertex G v
  let w' : {x : V // x ≠ v} := ⟨w, hvw.symm⟩
  have hH : H.Connected := hG.2.2 v
  have hnpre : ¬ (deleteVertex H w').Preconnected := by
    intro hpre
    have he := deletePairIso (G := G) v w hvw.symm
    have hcpre := hpre.map he.toHom he.toEquiv.surjective
    have hcard : (3 : ℕ∞) ≤ ENat.card V := by
      rw [ENat.card_eq_coe_natCard]
      exact_mod_cast hG.1
    obtain ⟨z, hzv, hzw⟩ := ENat.exists_ne_ne_of_three_le hcard v w
    exact hdisconn { preconnected := hcpre, nonempty := ⟨⟨z, hzv, hzw⟩⟩ }
  have hwcut := cutVertex_of_not_preconnected_delete hH w' hnpre
  obtain ⟨B, C, t, s, hBC, hB, hC⟩ := exists_two_leafBlocks hH ⟨w', hwcut⟩
  obtain ⟨a, ha, hat, hva⟩ := exists_neighbor_in_leafBlock hG v B t hB
  obtain ⟨b, hb, hbs, hvb⟩ := exists_neighbor_in_leafBlock hG v C s hC
  obtain ⟨hab, hnab, hconn⟩ := leafBlock_pair_deletion hH B C t s a b hBC hB hC ha hat hb hbs
  have heq : {x : {x : V // x ≠ v} | x ≠ a ∧ x ≠ b} =
      {x | x.val ≠ a.val ∧ x.val ≠ b.val} := by
    ext x
    simp only [Set.mem_ofPred_eq, ne_eq, Subtype.ext_iff]
  rw [heq] at hconn
  exact ⟨v, a.val, b.val, fun he => hab (Subtype.ext he), hva, hvb, hnab,
    connected_add_vertex_after_pair_deletion v a.val b.val a.property b.property hconn (hd v)⟩

end FiniteCombinatorics.Graph.Coloring
