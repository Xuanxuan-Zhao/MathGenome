import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.DegreesLeaves
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.Prufer
import Mathlib.Data.Fintype.Card

universe u

noncomputable section

namespace FiniteCombinatorics.Graph.Trees

open Specs.FiniteCombinatorics.Graph.Trees.Prufer
open Specs.FiniteCombinatorics.Graph.Foundations
open scoped Classical

/-- Deletion of a leaf preserves the tree on the remaining labels. -/
theorem tree_delete_leaf {V : Type u} [Finite V] (G : SimpleGraph V) (hG : G.IsTree)
    (b : V) (hb : degreeValue G b = 1) : (G.induce {b}ᶜ).IsTree := by
  classical
  let := Fintype.ofFinite V
  refine ⟨?_, hG.isAcyclic.induce _⟩
  exact hG.connected.induce_compl_singleton_of_degree_eq_one
    ((degree_mathlib G b).symm.trans hb)

/-- Removing a label decreases the cardinality by one, with no enumeration choice. -/
theorem card_compl_singleton {V : Type u} [Finite V] (b : V) :
    Nat.card ({b}ᶜ : Set V) = Nat.card V - 1 := by
  classical
  let := Fintype.ofFinite V
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_compl_set, Fintype.card_unique (α := ({b} : Set V))]

/-- The least leaf exists on any nontrivial finite labelled tree. -/
theorem exists_smallest_leaf {V : Type u} [Finite V] [LinearOrder V]
    (G : SimpleGraph V) (hG : G.IsTree) (hn : 2 ≤ Nat.card V) :
    ∃ b : V, degreeValue G b = 1 ∧ ∀ v, degreeValue G v = 1 → b ≤ v := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨a, _, _, ha, _⟩ := two_leaves G hG hn
  let s := Finset.univ.filter (fun v => degreeValue G v = 1)
  have hs : s.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (s.min'_mem hs)).2
  · intro v hv
    exact s.min'_le v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)

/-- W41, the forward construction; induction runs over the number of labels. -/
theorem encoding_exists :
    Specs.FiniteCombinatorics.Graph.Trees.Prufer.encoding_existsType.{u} := by
  classical
  suffices ∀ n, ∀ (V : Type u) [Finite V] [LinearOrder V], Nat.card V = n →
      ∀ (G : SimpleGraph V), G.IsTree → 2 ≤ Nat.card V →
        ∃ c : List V, IsPruferCode G c by
    intro V _ _ G hG hn
    exact this (Nat.card V) V rfl G hG hn
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ hV G hG hn
    by_cases htwo : Nat.card V = 2
    · exact ⟨[], .pair G hG htwo⟩
    have hthree : 3 ≤ Nat.card V := by omega
    obtain ⟨b, hb, hmin⟩ := exists_smallest_leaf G hG hn
    let := Fintype.ofFinite V
    obtain ⟨a, ha, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
      ((degree_mathlib G b).symm.trans hb)
    have hless : Nat.card ({b}ᶜ : Set V) < n := by
      rw [card_compl_singleton]; omega
    have hsize : 2 ≤ Nat.card ({b}ᶜ : Set V) := by
      rw [card_compl_singleton]; omega
    obtain ⟨tail, htail⟩ := ih _ hless ({b}ᶜ : Set V) rfl
      (G.induce {b}ᶜ) (tree_delete_leaf G hG b hb) hsize
    exact ⟨a :: tail.map Subtype.val, .step G hG hthree b a hb hmin ha tail htail⟩

/-- W41, the separate singleton-label assertion. Every graph on one label
is the same edgeless tree. -/
theorem singleton_tree_count :
    Specs.FiniteCombinatorics.Graph.Trees.Prufer.singleton_tree_countType := by
  intro V _ hV
  obtain ⟨hsub, hne⟩ := Nat.card_eq_one_iff_unique.mp hV
  let := hsub
  let := hne
  have : Subsingleton (LabelledTree V) := inferInstance
  have : Nonempty (LabelledTree V) := ⟨⟨⊥, SimpleGraph.IsTree.of_subsingleton⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- The exact degree change on deleting a vertex. -/
theorem degree_delete_vertex {V : Type u} [Finite V] (G : SimpleGraph V)
    (b : V) (v : ({b}ᶜ : Set V)) :
    degreeValue G v = degreeValue (G.induce {b}ᶜ) v + if G.Adj v b then 1 else 0 := by
  classical
  let := Fintype.ofFinite V
  have hm := G.map_neighborFinset_induce (s := {b}ᶜ) v
  have he : G.neighborFinset v ∩ ({b}ᶜ : Set V).toFinset =
      (G.neighborFinset v).erase b := by
    ext w
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Set.mem_toFinset,
      Set.mem_compl_iff, Set.mem_singleton_iff, Finset.mem_erase]
    tauto
  have hc := congrArg Finset.card hm
  rw [Finset.card_map, he] at hc
  rw [degree_mathlib G v, degree_mathlib (G.induce {b}ᶜ) v]
  simp only [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hadj : G.Adj v b
  · rw [ite_eq_left hadj, hc]
    exact (Finset.card_erase_add_one (by simpa only [SimpleGraph.mem_neighborFinset] using hadj)).symm
  · rw [ite_eq_right hadj, hc, Finset.erase_eq_of_notMem
      (by simpa only [SimpleGraph.mem_neighborFinset] using hadj), Nat.add_zero]

/-- All degrees of a nontrivial tree are positive. -/
theorem tree_degree_pos {V : Type u} [Finite V] (G : SimpleGraph V)
    (hG : G.IsTree) (hn : 2 ≤ Nat.card V) (v : V) : 0 < degreeValue G v := by
  classical
  let := Fintype.ofFinite V
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp
    (by rw [Nat.card_eq_fintype_card] at hn; omega)
  rw [degree_mathlib]
  exact hG.connected.preconnected.degree_pos_of_nontrivial v

/-- On two labels the unique tree is a single edge. -/
theorem degree_tree_pair {V : Type u} [Finite V] (G : SimpleGraph V)
    (hG : G.IsTree) (hn : Nat.card V = 2) (v : V) : degreeValue G v = 1 := by
  classical
  let := Fintype.ofFinite V
  have hp := tree_degree_pos G hG (by omega) v
  have hlt := G.degree_lt_card_verts v
  rw [← degree_mathlib, ← Nat.card_eq_fintype_card, hn] at hlt
  omega

/-- Occurrences transform exactly as degrees under one leaf deletion. -/
lemma leaf_code_counts {V : Type u} [Finite V] [LinearOrder V]
    (G : SimpleGraph V) (b a : V) (hb : degreeValue G b = 1) (ha : G.Adj b a)
    (tail : List ({b}ᶜ : Set V))
    (hcount : ∀ w, tail.count w + 1 = degreeValue (G.induce {b}ᶜ) w) :
    ∀ v, (a :: tail.map Subtype.val).count v + 1 = degreeValue G v := by
  intro v
  by_cases hv : v = b
  · subst v
    have hab : a ≠ b := ha.ne.symm
    have hnot : b ∉ tail.map Subtype.val := by
      intro hm
      obtain ⟨w, _, he⟩ := List.mem_map.mp hm
      exact w.property (Set.mem_singleton_iff.mpr he)
    rw [List.count_cons, ite_eq_right (by simpa using hab), List.count_eq_zero.mpr hnot]
    simpa only [Nat.zero_add] using hb.symm
  · let w : ({b}ᶜ : Set V) := ⟨v, hv⟩
    have hm : (tail.map Subtype.val).count v = tail.count w :=
      List.count_map_of_injective tail Subtype.val Subtype.val_injective w
    have hd := degree_delete_vertex G b w
    dsimp only [w] at hd
    have hadj : G.Adj v b ↔ v = a := by
      let := Fintype.ofFinite V
      obtain ⟨x, hx, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
        ((degree_mathlib G b).symm.trans hb)
      constructor
      · intro hvb
        exact (huniq v hvb.symm).trans (huniq a ha).symm
      · rintro rfl
        exact ha.symm
    rw [hadj] at hd
    have hw := hcount w
    dsimp only [w] at hw
    rw [List.count_cons, hm]
    dsimp only [w] at *
    by_cases hva : a = v
    · subst v
      simp only [beq_self_eq_true, ↓reduceIte] at *
      omega
    · have hva' := Ne.symm hva
      simp only [beq_iff_eq, hva, hva', ↓reduceIte] at *
      omega

/-- The statistics of any deletion trace; the additive form avoids truncation
at a vertex of positive degree. -/
theorem prufer_code_statistics {V : Type u} [Finite V] [LinearOrder V]
    {G : SimpleGraph V} {c : List V} (h : IsPruferCode G c) :
    c.length = Nat.card V - 2 ∧ ∀ v : V, c.count v + 1 = degreeValue G v := by
  induction h with
  | pair G hG hn =>
    refine ⟨by simp [hn], ?_⟩
    intro v
    simpa only [List.count_nil, Nat.zero_add] using (degree_tree_pair G hG hn v).symm
  | @step V _ _ G hG hn b a hb hmin ha tail htail ih =>
    obtain ⟨hlen, hcount⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [List.length_cons, List.length_map, hlen, card_compl_singleton]
      omega
    · exact leaf_code_counts G b a hb ha tail hcount

/-- W41: code length and the degree-minus-one occurrence formula. -/
theorem encoding_statistics :
    Specs.FiniteCombinatorics.Graph.Trees.Prufer.encoding_statisticsType := by
  intro V _ _ G c hc
  obtain ⟨hlen, hcount⟩ := prufer_code_statistics hc
  refine ⟨hlen, fun v => ?_⟩
  have := hcount v
  omega

/-- Attach the deleted label as a new leaf at a remaining label. -/
def attachLeaf {V : Type u} (b : V) (a : ({b}ᶜ : Set V))
    (H : SimpleGraph ({b}ᶜ : Set V)) : SimpleGraph V :=
  H.spanningCoe ⊔ SimpleGraph.edge b a.val

lemma spanningCoe_not_adj_deleted {V : Type u} (b : V)
    (H : SimpleGraph ({b}ᶜ : Set V)) (v : V) : ¬H.spanningCoe.Adj b v := by
  rw [SimpleGraph.map_adj]
  rintro ⟨x, y, _, hx, _⟩
  exact x.property (Set.mem_singleton_iff.mpr hx)

lemma attachLeaf_adj_deleted {V : Type u} (b : V) (a : ({b}ᶜ : Set V))
    (H : SimpleGraph ({b}ᶜ : Set V)) (v : V) :
    (attachLeaf b a H).Adj b v ↔ v = a.val := by
  rw [attachLeaf, SimpleGraph.sup_adj, or_iff_right (spanningCoe_not_adj_deleted b H v),
    SimpleGraph.edge_adj]
  have ha : a.val ≠ b := a.property
  aesop

lemma attachLeaf_induce {V : Type u} (b : V) (a : ({b}ᶜ : Set V))
    (H : SimpleGraph ({b}ᶜ : Set V)) : (attachLeaf b a H).induce {b}ᶜ = H := by
  ext x y
  change H.spanningCoe.Adj x.val y.val ∨ (SimpleGraph.edge b a.val).Adj x.val y.val ↔ _
  rw [show H.spanningCoe.Adj x.val y.val ↔ H.Adj x y from
    SimpleGraph.map_adj_apply (f := Function.Embedding.subtype _) (a := x) (b := y)]
  have hx : x.val ≠ b := x.property
  have hy : y.val ≠ b := y.property
  simp [SimpleGraph.edge_adj, hx, hy]

lemma attachLeaf_degree_deleted {V : Type u} [Finite V] (b : V) (a : ({b}ᶜ : Set V))
    (H : SimpleGraph ({b}ᶜ : Set V)) : degreeValue (attachLeaf b a H) b = 1 := by
  classical
  let := Fintype.ofFinite V
  rw [degree_mathlib]
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  exact ⟨a.val, (attachLeaf_adj_deleted b a H a.val).mpr rfl,
    fun v hv => (attachLeaf_adj_deleted b a H v).mp hv⟩

lemma attachLeaf_tree {V : Type u} [Finite V] (b : V) (a : ({b}ᶜ : Set V))
    (H : SimpleGraph ({b}ᶜ : Set V)) (hH : H.IsTree) : (attachLeaf b a H).IsTree := by
  classical
  let := Fintype.ofFinite V
  let f : H →g attachLeaf b a H :=
    (SimpleGraph.Hom.ofLE (show H.spanningCoe ≤ attachLeaf b a H from le_sup_left)).comp
      (SimpleGraph.Embedding.spanningCoe H).toHom
  have hreach (v : V) : (attachLeaf b a H).Reachable v a.val := by
    by_cases hv : v = b
    · subst v
      exact ((attachLeaf_adj_deleted b a H a.val).mpr rfl).reachable
    · exact (hH.connected (⟨v, hv⟩ : ({b}ᶜ : Set V)) a).map f
  have hconn : (attachLeaf b a H).Connected :=
    { preconnected := fun v w => (hreach v).trans (hreach w).symm
      nonempty := ⟨b⟩ }
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have hcount := H.spanningCoe.card_edgeFinset_sup_edge
    (spanningCoe_not_adj_deleted b H a.val) (Ne.symm a.property)
  have hmap := SimpleGraph.card_edgeFinset_map (Function.Embedding.subtype (· ∈ ({b}ᶜ : Set V))) H
  have hcount' : Nat.card (attachLeaf b a H).edgeSet = Nat.card H.edgeSet + 1 := by
    simpa only [attachLeaf, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hcount.trans
      (congrArg (· + 1) hmap)
  have hHcount := (SimpleGraph.isTree_iff_connected_and_card.mp hH).2
  have hsize := card_compl_singleton b
  have : Nonempty V := ⟨b⟩
  have hpos : 0 < Nat.card V := Nat.card_pos
  rw [hcount']
  omega

lemma prufer_code_tree {V : Type u} [Finite V] [LinearOrder V]
    {G : SimpleGraph V} {c : List V} (h : IsPruferCode G c) : G.IsTree := by
  cases h with
  | pair _ hG _ => exact hG
  | step _ hG _ _ _ _ _ _ _ _ => exact hG

/-- A short word omits a label, and its omitted labels have a least element. -/
lemma exists_smallest_missing {V : Type u} [Finite V] [LinearOrder V]
    (c : List V) (hc : c.length < Nat.card V) :
    ∃ b : V, b ∉ c ∧ ∀ v, v ∉ c → b ≤ v := by
  classical
  let := Fintype.ofFinite V
  have hex : ∃ b : V, b ∉ c := by
    by_contra h
    have hall : ∀ v : V, v ∈ c := by simpa only [not_exists, not_not] using h
    have he : c.toFinset = Finset.univ := by
      ext v
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      exact hall v
    have hle := c.toFinset_card_le
    rw [he, Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
    omega
  obtain ⟨a, ha⟩ := hex
  let s := Finset.univ.filter (fun v => v ∉ c)
  have hs : s.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (s.min'_mem hs)).2, ?_⟩
  intro v hv
  exact s.min'_le v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)

/-- Decoding works for every word of the required length. -/
theorem decoding_exists : ∀ (V : Type u) [Finite V] [LinearOrder V],
    2 ≤ Nat.card V → ∀ c : List V, c.length = Nat.card V - 2 →
    ∃ G : SimpleGraph V, IsPruferCode G c := by
  classical
  suffices ∀ n, ∀ (V : Type u) [Finite V] [LinearOrder V], Nat.card V = n →
      2 ≤ Nat.card V → ∀ c : List V, c.length = Nat.card V - 2 →
        ∃ G : SimpleGraph V, IsPruferCode G c by
    intro V _ _ hn c hc
    exact this (Nat.card V) V rfl hn c hc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ hV hn c hc
    by_cases htwo : Nat.card V = 2
    · have hnil : c = [] := List.length_eq_zero_iff.mp (by omega)
      subst c
      have : Nonempty V := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card V)).1
      obtain ⟨G, _, hG⟩ := (SimpleGraph.connected_top (V := V)).exists_isTree_le
      exact ⟨G, .pair G hG htwo⟩
    have hthree : 3 ≤ Nat.card V := by omega
    obtain ⟨b, hb, hmin⟩ := exists_smallest_missing c (by omega)
    cases c with
    | nil => simp only [List.length_nil] at hc; omega
    | cons a tail =>
      have hab : a ≠ b := by
        intro h
        subst a
        exact hb (List.mem_cons_self ..)
      have htail (v : V) (hv : v ∈ tail) : v ∈ ({b}ᶜ : Set V) := by
        intro hvb
        have he : v = b := Set.mem_singleton_iff.mp hvb
        subst v
        exact hb (List.mem_cons_of_mem a hv)
      let rest : List ({b}ᶜ : Set V) := tail.attachWith (· ∈ ({b}ᶜ : Set V)) htail
      have hmap : rest.map Subtype.val = tail := List.attachWith_map_subtype_val htail
      have hlen : rest.length = Nat.card ({b}ᶜ : Set V) - 2 := by
        have hm := congrArg List.length hmap
        simp only [List.length_map] at hm
        simp only [List.length_cons] at hc
        rw [card_compl_singleton]
        omega
      have hless : Nat.card ({b}ᶜ : Set V) < n := by rw [card_compl_singleton]; omega
      have hsize : 2 ≤ Nat.card ({b}ᶜ : Set V) := by rw [card_compl_singleton]; omega
      obtain ⟨H, hH⟩ := ih _ hless ({b}ᶜ : Set V) rfl hsize rest hlen
      let aa : ({b}ᶜ : Set V) := ⟨a, hab⟩
      let G := attachLeaf b aa H
      have hG : G.IsTree := attachLeaf_tree b aa H (prufer_code_tree hH)
      have hleaf : degreeValue G b = 1 := attachLeaf_degree_deleted b aa H
      have hadj : G.Adj b a := (attachLeaf_adj_deleted b aa H a).mpr rfl
      have hres : IsPruferCode (G.induce {b}ᶜ) rest := by
        simpa only [G, attachLeaf_induce] using hH
      have hcounts := leaf_code_counts G b a hleaf hadj rest
        (prufer_code_statistics hres).2
      rw [hmap] at hcounts
      have hleast : ∀ v, degreeValue G v = 1 → b ≤ v := by
        intro v hv
        have hz : (a :: tail).count v = 0 := by have := hcounts v; omega
        exact hmin v (List.count_eq_zero.mp hz)
      refine ⟨G, ?_⟩
      have hcode := IsPruferCode.step G hG hthree b a hleaf hleast hadj rest hres
      rwa [hmap] at hcode

lemma adj_leaf_iff {V : Type u} [Finite V] (G : SimpleGraph V)
    (b a : V) (hb : degreeValue G b = 1) (ha : G.Adj b a) (v : V) :
    G.Adj b v ↔ v = a := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨x, hx, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
    ((degree_mathlib G b).symm.trans hb)
  exact ⟨fun hv => (huniq v hv).trans (huniq a ha).symm, fun h => h ▸ ha⟩

lemma tree_pair_eq_top {V : Type u} [Finite V] (G : SimpleGraph V)
    (hG : G.IsTree) (hn : Nat.card V = 2) : G = ⊤ := by
  classical
  let := Fintype.ofFinite V
  ext v w
  rw [SimpleGraph.top_adj]
  refine ⟨SimpleGraph.Adj.ne, ?_⟩
  intro hvw
  have hp := tree_degree_pos G hG (by omega) v
  rw [degree_mathlib] at hp
  obtain ⟨x, hx⟩ := (G.degree_pos_iff_exists_adj v).mp hp
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' v).mp hn
  have he : x = w := (huniq x hx.ne.symm).trans (huniq w hvw.symm).symm
  exact he ▸ hx

/-- The tree is determined by its deleted induced graph and the leaf's neighbor. -/
lemma graph_eq_of_delete_leaf {V : Type u} [Finite V] (G H : SimpleGraph V)
    (b a : V) (hbG : degreeValue G b = 1) (hbH : degreeValue H b = 1)
    (haG : G.Adj b a) (haH : H.Adj b a)
    (he : G.induce {b}ᶜ = H.induce {b}ᶜ) : G = H := by
  ext v w
  by_cases hv : v = b
  · subst v
    rw [adj_leaf_iff G b a hbG haG, adj_leaf_iff H b a hbH haH]
  by_cases hw : w = b
  · subst w
    rw [SimpleGraph.adj_comm, adj_leaf_iff G b a hbG haG,
      SimpleGraph.adj_comm, adj_leaf_iff H b a hbH haH]
  · exact Iff.of_eq (congrArg (fun K : SimpleGraph ({b}ᶜ : Set V) =>
      K.Adj ⟨v, hv⟩ ⟨w, hw⟩) he)

/-- The deletion relation is a function of the tree. -/
theorem encoding_unique {V : Type u} [Finite V] [LinearOrder V]
    {G : SimpleGraph V} {c d : List V} (hc : IsPruferCode G c)
    (hd : IsPruferCode G d) : c = d := by
  induction hc with
  | pair G hG hn =>
    cases hd with
    | pair => rfl
    | step _ _ hthree => omega
  | @step V _ _ G hG hn b a hb hmin ha tail ht ih =>
    cases hd with
    | pair _ _ htwo => omega
    | step _ _ hn' b' a' hb' hmin' ha' tail' ht' =>
      have heqb : b = b' := le_antisymm (hmin b' hb') (hmin' b hb)
      subst b'
      have heqa : a' = a := (adj_leaf_iff G b a hb ha a').mp ha'
      subst a'
      have heqt : tail = tail' := ih ht'
      subst tail'
      rfl

/-- Inverting a nonempty deletion trace exposes its first deleted leaf. -/
lemma prufer_code_cons_inv {V : Type u} [Finite V] [LinearOrder V]
    {G : SimpleGraph V} {a : V} {c : List V} (h : IsPruferCode G (a :: c)) :
    ∃ b : V, G.IsTree ∧ 3 ≤ Nat.card V ∧ degreeValue G b = 1 ∧
      (∀ v, degreeValue G v = 1 → b ≤ v) ∧ G.Adj b a ∧
      ∃ tail : List ({b}ᶜ : Set V), tail.map Subtype.val = c ∧
        IsPruferCode (G.induce {b}ᶜ) tail := by
  cases h with
  | step G hG hn b a hb hmin ha tail ht =>
    exact ⟨b, hG, hn, hb, hmin, ha, tail, rfl, ht⟩

/-- A word determines the tree uniquely. The occurrence formula identifies
its least absent label with the least leaf in either proposed tree. -/
theorem decoding_unique {V : Type u} [Finite V] [LinearOrder V]
    {G H : SimpleGraph V} {c : List V} (hc : IsPruferCode G c)
    (hd : IsPruferCode H c) : G = H := by
  induction hc with
  | pair G hG hn =>
    exact (tree_pair_eq_top G hG hn).trans
      (tree_pair_eq_top H (prufer_code_tree hd) hn).symm
  | @step V _ _ G hG hn b a hb hmin ha tail ht ih =>
    obtain ⟨b', hH, hn', hb', hmin', ha', tail', hmap, ht'⟩ := prufer_code_cons_inv hd
    have hcountG := (prufer_code_statistics
      (IsPruferCode.step G hG hn b a hb hmin ha tail ht)).2
    have hcountH := (prufer_code_statistics hd).2
    have hdeg (v : V) : degreeValue G v = degreeValue H v :=
      (hcountG v).symm.trans (hcountH v)
    have heqb : b = b' := le_antisymm
      (hmin b' ((hdeg b').trans hb'))
      (hmin' b ((hdeg b).symm.trans hb))
    subst b'
    have heqt : tail' = tail := List.map_injective_iff.mpr Subtype.val_injective hmap
    subst tail'
    exact graph_eq_of_delete_leaf G H b a hb hb' ha ha' (ih ht')

/-- W41: the smallest-leaf encoder and decoder give an equivalence, with
occurrences equal to degree minus one at every label. -/
theorem prufer_bijection :
    Specs.FiniteCombinatorics.Graph.Trees.Prufer.prufer_bijectionType.{u} := by
  intro V _ _ hn
  let chosen (T : LabelledTree V) : List V :=
    Classical.choose (encoding_exists V T.val T.property hn)
  have hchosen (T : LabelledTree V) : IsPruferCode T.val (chosen T) :=
    Classical.choose_spec (encoding_exists V T.val T.property hn)
  let enc (T : LabelledTree V) : Sequence V := fun i =>
    (chosen T).get (Fin.cast (prufer_code_statistics (hchosen T)).1.symm i)
  have hlist (T : LabelledTree V) : List.ofFn (enc T) = chosen T :=
    (List.ofFn_congr (prufer_code_statistics (hchosen T)).1 (chosen T).get).symm.trans
      (List.ofFn_get (chosen T))
  have henc (T : LabelledTree V) : IsPruferCode T.val (List.ofFn (enc T)) := by
    rw [hlist]
    exact hchosen T
  have hinj : Function.Injective enc := by
    intro T U hTU
    apply Subtype.ext
    have hT := henc T
    rw [hTU] at hT
    exact decoding_unique hT (henc U)
  have hsurj : Function.Surjective enc := by
    intro code
    obtain ⟨G, hG⟩ := decoding_exists V hn (List.ofFn code) (List.length_ofFn ..)
    let T : LabelledTree V := ⟨G, prufer_code_tree hG⟩
    refine ⟨T, List.ofFn_injective ?_⟩
    exact encoding_unique (henc T) hG
  refine ⟨Equiv.ofBijective enc ⟨hinj, hsurj⟩, ?_⟩
  intro T
  exact ⟨henc T, (encoding_statistics V T.val (List.ofFn (enc T)) (henc T)).2⟩

/-- W41: Cayley's count is obtained from the equivalence only for at least
two labels. In particular, a pair of labels has the unique empty code. -/
theorem cayley : Specs.FiniteCombinatorics.Graph.Trees.Prufer.cayleyType := by
  intro V _ _ hn
  obtain ⟨e, _⟩ := prufer_bijection V hn
  calc
    Nat.card (LabelledTree V) = Nat.card (Sequence V) := Nat.card_congr e
    _ = (Nat.card V) ^ (Nat.card V - 2) := by
      rw [Sequence, Nat.card_fun, Nat.card_fin]

end FiniteCombinatorics.Graph.Trees
