import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.FaceSides
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Plane.Euler
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Plane.FaceSides
/-! Conditional derivations of the edge bounds in W62. -/

universe u v

noncomputable section
namespace FiniteCombinatorics.Graph.Plane.EdgeBounds
open Specs.FiniteCombinatorics.Graph.Plane.Foundations

lemma three_bound_arithmetic (v e f : ℕ) (hv : 3 ≤ v)
    (heuler : (v : ℤ) - e + f = 2) (hsides : 3 * f ≤ 2 * e) :
    e ≤ 3 * v - 6 := by
  omega

lemma four_bound_arithmetic (v e f : ℕ) (hv : 3 ≤ v)
    (heuler : (v : ℤ) - e + f = 2) (hsides : 4 * f ≤ 2 * e) :
    e ≤ 2 * v - 4 := by
  omega

lemma complete_five_vertex_count : Nat.card (Fin 5) = 5 := by simp

lemma complete_five_edge_count :
    Nat.card (⊤ : SimpleGraph (Fin 5)).edgeSet = 10 := by
  classical
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  decide

lemma complete_three_three_vertex_count : Nat.card (Fin 3 ⊕ Fin 3) = 6 := by
  simp

lemma complete_three_three_edge_count :
    Nat.card (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet = 9 := by
  have h := SimpleGraph.encard_edgeSet_completeBipartiteGraph
    (W₁ := Fin 3) (W₂ := Fin 3)
  have hc := congrArg ENat.toNat h
  simpa only [Set.encard, ENat.card_eq_coe_natCard, Nat.card_fin,
    ← Nat.cast_mul, ENat.toNat_natCast] using hc

lemma complete_three_three_bipartite :
    (completeBipartiteGraph (Fin 3) (Fin 3)).IsBipartite :=
  SimpleGraph.IsBipartite.completeBipartiteGraph _ _

/-- Restrict a drawing along a graph embedding. -/
def drawingOfEmbedding {V : Type u} {W : Type v} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (D : Drawing G) (f : H ↪g G) :
    Drawing H where
  point := D.point ∘ f
  point_injective := D.point_injective.comp f.injective
  edge := fun e => D.edge (f.mapEdgeSet e)
  edge_arc := fun a b h => D.edge_arc (f a) (f b) (f.map_adj_iff.mpr h)
  vertex_edge := by
    intro e v
    change D.point (f v) ∈ D.edge (f.mapEdgeSet e) ↔ v ∈ e.val
    rw [D.vertex_edge]
    change f v ∈ Sym2.map f e.val ↔ v ∈ e.val
    simp only [Sym2.mem_map, f.injective.eq_iff, exists_eq_right]
  edge_intersection := by
    intro e e' h
    rw [D.edge_intersection _ _ (fun he => h (f.mapEdgeSet.injective he))]
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply]
    constructor
    · rintro ⟨v, ⟨hv, hv'⟩, rfl⟩
      obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.mp hv
      change f w ∈ Sym2.map f e'.val at hv'
      have hw' : w ∈ e'.val := by
        simpa only [Sym2.mem_map, f.injective.eq_iff, exists_eq_right] using hv'
      exact ⟨w, ⟨hw, hw'⟩, rfl⟩
    · rintro ⟨v, ⟨hv, hv'⟩, rfl⟩
      exact ⟨f v, ⟨Sym2.mem_map.mpr ⟨v, hv, rfl⟩,
        Sym2.mem_map.mpr ⟨v, hv', rfl⟩⟩, rfl⟩

/-- Vertices are the disjoint union of the supports of graph components. -/
def componentVertexEquiv {V : Type u} (G : SimpleGraph V) :
    (Σ C : G.ConnectedComponent, C) ≃ V where
  toFun x := x.2.val
  invFun v := ⟨G.connectedComponentMk v, ⟨v, rfl⟩⟩
  left_inv := by
    rintro ⟨C, v, hv⟩
    have h : G.connectedComponentMk v = C := hv
    subst C
    rfl
  right_inv _ := rfl

/-- Edges are the disjoint union of the edge sets of their components. -/
def componentEdgeEquiv {V : Type u} (G : SimpleGraph V) :
    (Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) ≃ G.edgeSet := by
  classical
  let f : (Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) → G.edgeSet :=
    fun x => x.1.toSimpleGraph_hom.mapEdgeSet x.2
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨C, e⟩ ⟨C', e'⟩ he
    have hev : Sym2.map Subtype.val e.val = Sym2.map Subtype.val e'.val :=
      congrArg Subtype.val he
    let a := e.val.out.1
    have ha : a ∈ e.val := e.val.out_fst_mem
    have ha' : a.val ∈ Sym2.map Subtype.val e'.val := by
      rw [← hev]
      exact Sym2.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := Sym2.mem_map.mp ha'
    have hC : C = C' := by
      exact (C.mem_supp_iff a.val).mp a.property |>.symm.trans
        (hab ▸ (C'.mem_supp_iff b.val).mp b.property)
    subst C'
    have hee : e = e' := Subtype.ext (Sym2.map.injective Subtype.val_injective hev)
    subst e'
    rfl
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with | _ a b =>
      have hab : G.Adj a b := he
      let C := G.connectedComponentMk a
      have ha : a ∈ C.supp := rfl
      have hb : b ∈ C.supp := (C.mem_supp_congr_adj hab).mp ha
      exact ⟨⟨C, ⟨s(⟨a, ha⟩, ⟨b, hb⟩), hab⟩⟩, rfl⟩

lemma vertex_count_components {V : Type u} [Finite V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] :
    Nat.card V = ∑ C : G.ConnectedComponent, Nat.card C := by
  rw [← Nat.card_sigma]
  exact (Nat.card_congr (componentVertexEquiv G)).symm

lemma edge_count_components {V : Type u} [Finite V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] :
    Nat.card G.edgeSet = ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet := by
  rw [← Nat.card_sigma]
  exact (Nat.card_congr (componentEdgeEquiv G)).symm

lemma small_graph_edge_bound {V : Type u} [Finite V] (G : SimpleGraph V)
    (hv : Nat.card V < 3) : Nat.card G.edgeSet ≤ Nat.card V / 2 := by
  classical
  let := Fintype.ofFinite V
  let : DecidableRel G.Adj := Classical.decRel _
  have h : Nat.card G.edgeSet ≤ (Nat.card V).choose 2 := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using
      G.card_edgeFinset_le_card_choose_two
  have hn : Nat.card V = 0 ∨ Nat.card V = 1 ∨ Nat.card V = 2 := by omega
  rcases hn with hn | hn | hn
  all_goals rw [hn] at h ⊢
  all_goals norm_num at h ⊢
  all_goals exact h

/-- The connected Euler calculation uses the actual faces of the drawing. -/
lemma connected_edge_bounds
    (face_bounds : Specs.FiniteCombinatorics.Graph.Plane.FaceSides.face_boundsType.{u})
    {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (hG : G.Connected) (hv : 3 ≤ Nat.card V) :
    Nat.card G.edgeSet ≤ 3 * Nat.card V - 6 ∧
      (G.IsBipartite → Nat.card G.edgeSet ≤ 2 * Nat.card V - 4) := by
  have : Nonempty V := hG.nonempty
  have : Subsingleton G.ConnectedComponent := hG.preconnected.subsingleton_connectedComponent
  have heuler := Euler.euler_formula D
  have hc : Nat.card G.ConnectedComponent = 1 := Nat.card_unique
  rw [hc] at heuler
  obtain ⟨hthree, hfour⟩ := face_bounds D hG hv
  exact ⟨three_bound_arithmetic _ _ _ hv (by simpa using heuler) hthree,
    fun hb => four_bound_arithmetic _ _ _ hv (by simpa using heuler) (hfour hb)⟩

/-- A bound which also records the exceptional graphs with fewer than three vertices. -/
def edgeAllowance (k v : ℕ) : ℕ := if v < 3 then v / 2 else k * v - 2 * k

lemma edgeAllowance_add (k v w : ℕ) (hk : k = 2 ∨ k = 3) :
    edgeAllowance k v + edgeAllowance k w ≤ edgeAllowance k (v + w) := by
  rcases hk with rfl | rfl <;>
    unfold edgeAllowance <;> split_ifs <;> omega

lemma sum_edgeAllowance_le {ι : Type*} (s : Finset ι) (k : ℕ) (v : ι → ℕ)
    (hk : k = 2 ∨ k = 3) :
    ∑ i ∈ s, edgeAllowance k (v i) ≤ edgeAllowance k (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [edgeAllowance]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (Nat.add_le_add_left ih _).trans (edgeAllowance_add k _ _ hk)

/-- The bounds on arbitrary drawings follow by summing component bounds. -/
lemma drawing_edge_bounds
    (face_bounds : Specs.FiniteCombinatorics.Graph.Plane.FaceSides.face_boundsType.{u})
    {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) :
    Nat.card G.edgeSet ≤ edgeAllowance 3 (Nat.card V) ∧
      (G.IsBipartite → Nat.card G.edgeSet ≤ edgeAllowance 2 (Nat.card V)) := by
  classical
  let := Fintype.ofFinite G.ConnectedComponent
  have hcomponent (C : G.ConnectedComponent) :
      Nat.card C.toSimpleGraph.edgeSet ≤ edgeAllowance 3 (Nat.card C) ∧
      (G.IsBipartite →
        Nat.card C.toSimpleGraph.edgeSet ≤ edgeAllowance 2 (Nat.card C)) := by
    by_cases hv : Nat.card C < 3
    · have hs := small_graph_edge_bound C.toSimpleGraph hv
      simp only [edgeAllowance, hv, ite_true]
      exact ⟨hs, fun _ => hs⟩
    · have DC : Drawing C.toSimpleGraph :=
        drawingOfEmbedding D (SimpleGraph.Embedding.induce C.supp)
      obtain ⟨hthree, hfour⟩ :=
        connected_edge_bounds face_bounds DC C.connected_toSimpleGraph (by omega)
      simp only [edgeAllowance, hv, ite_false]
      exact ⟨hthree, fun hb => hfour (hb.of_hom C.toSimpleGraph_hom)⟩
  constructor
  · rw [edge_count_components G, vertex_count_components G]
    exact (Finset.sum_le_sum (fun C _ => (hcomponent C).1)).trans
      (sum_edgeAllowance_le _ 3 _ (Or.inr rfl))
  · intro hb
    rw [edge_count_components G, vertex_count_components G]
    exact (Finset.sum_le_sum (fun C _ => (hcomponent C).2 hb)).trans
      (sum_edgeAllowance_le _ 2 _ (Or.inl rfl))

/-- Conditional draft: the original theorem will be closed by the owner. -/
theorem planar_edge_bound_conditional :
    Specs.FiniteCombinatorics.Graph.Plane.FaceSides.face_boundsType.{u} →
    Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds.planar_edge_boundType.{u} := by
  rintro face_bounds V _ G ⟨D⟩ hv
  simpa only [edgeAllowance, show ¬Nat.card V < 3 by omega, ite_false] using
    (drawing_edge_bounds face_bounds D).1

/-- Conditional draft with no connectedness or minimum-degree assumption. -/
theorem planar_bipartite_edge_bound_conditional :
    Specs.FiniteCombinatorics.Graph.Plane.FaceSides.face_boundsType.{u} →
    Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds.planar_bipartite_edge_boundType.{u} := by
  rintro face_bounds V _ G ⟨D⟩ hv hb
  simpa only [edgeAllowance, show ¬Nat.card V < 3 by omega, ite_false] using
    (drawing_edge_bounds face_bounds D).2 hb

/-- Transport the numerical conclusion through `ULift`, so a premise at any
universe applies to the concrete finite graphs in the nonplanarity statements. -/
lemma lifted_edge_bounds
    (face_bounds : Specs.FiniteCombinatorics.Graph.Plane.FaceSides.face_boundsType.{u})
    {V : Type} [Finite V] {G : SimpleGraph V} (D : Drawing G) (hv : 3 ≤ Nat.card V) :
    Nat.card G.edgeSet ≤ 3 * Nat.card V - 6 ∧
      (G.IsBipartite → Nat.card G.edgeSet ≤ 2 * Nat.card V - 4) := by
  let H : SimpleGraph (ULift.{u} V) := G.comap ULift.down
  let e : H ≃g G := SimpleGraph.Iso.comap Equiv.ulift G
  have DH : Drawing H := drawingOfEmbedding D e.toEmbedding
  have hcV : Nat.card (ULift.{u} V) = Nat.card V := Nat.card_ulift _
  have hcE : Nat.card H.edgeSet = Nat.card G.edgeSet := Nat.card_congr e.mapEdgeSet
  constructor
  · have h := planar_edge_bound_conditional face_bounds
      (G := H) ⟨DH⟩ (by rwa [hcV])
    rwa [hcE, hcV] at h
  · intro hb
    have h := planar_bipartite_edge_bound_conditional face_bounds
      (G := H) ⟨DH⟩ (by rwa [hcV]) (hb.of_hom e.toHom)
    rwa [hcE, hcV] at h

/-- Ten edges on five vertices exceed the planar bound of nine. -/
theorem complete_five_nonplanar_conditional :
    Specs.FiniteCombinatorics.Graph.Plane.FaceSides.face_boundsType.{u} →
    Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds.complete_five_nonplanarType := by
  rintro face_bounds ⟨D⟩
  have h := (lifted_edge_bounds face_bounds D (by simp)).1
  rw [complete_five_edge_count, complete_five_vertex_count] at h
  omega

/-- Nine edges on six vertices exceed the bipartite planar bound of eight. -/
theorem complete_three_three_nonplanar_conditional :
    Specs.FiniteCombinatorics.Graph.Plane.FaceSides.face_boundsType.{u} →
    Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds.complete_three_three_nonplanarType := by
  rintro face_bounds ⟨D⟩
  have h := (lifted_edge_bounds face_bounds D (by simp)).2 complete_three_three_bipartite
  rw [complete_three_three_edge_count, complete_three_three_vertex_count] at h
  omega

end FiniteCombinatorics.Graph.Plane.EdgeBounds

universe v8_closure_6ce8b09891f05d6b_u0
theorem _root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«complete_five_nonplanar» : _root_.«Specs».«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«complete_five_nonplanarType» :=
  @_root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«complete_five_nonplanar_conditional».{0} (@_root_.«FiniteCombinatorics».«Graph».«Plane».«FaceSides».«face_bounds».{0})
theorem _root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«complete_three_three_nonplanar» : _root_.«Specs».«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«complete_three_three_nonplanarType» :=
  @_root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«complete_three_three_nonplanar_conditional».{0} (@_root_.«FiniteCombinatorics».«Graph».«Plane».«FaceSides».«face_bounds».{0})
theorem _root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«planar_bipartite_edge_bound» : _root_.«Specs».«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«planar_bipartite_edge_boundType».{v8_closure_6ce8b09891f05d6b_u0} :=
  @_root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«planar_bipartite_edge_bound_conditional».{v8_closure_6ce8b09891f05d6b_u0} (@_root_.«FiniteCombinatorics».«Graph».«Plane».«FaceSides».«face_bounds».{v8_closure_6ce8b09891f05d6b_u0})
theorem _root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«planar_edge_bound» : _root_.«Specs».«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«planar_edge_boundType».{v8_closure_6ce8b09891f05d6b_u0} :=
  @_root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«planar_edge_bound_conditional».{v8_closure_6ce8b09891f05d6b_u0} (@_root_.«FiniteCombinatorics».«Graph».«Plane».«FaceSides».«face_bounds».{v8_closure_6ce8b09891f05d6b_u0})
