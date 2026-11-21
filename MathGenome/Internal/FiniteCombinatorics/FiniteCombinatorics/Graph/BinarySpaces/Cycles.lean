import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.BinarySpaces.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.ForestsBridges
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.BinarySpaces.Cycles
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.LinearAlgebra.Dimension.Finite

set_option backward.isDefEq.respectTransparency false

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.BinarySpaces
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Specs.FiniteCombinatorics.Graph.BinarySpaces.Foundations
open Specs.FiniteCombinatorics.Graph.BinarySpaces.Cycles

variable {V : Type u} [Finite V] (G : SimpleGraph V)

/-- On nonforest coordinates a fundamental cycle is a coordinate vector. -/
lemma fundamentalCycle_coordinates (F : SpanningForestValue G) (e f : NonforestEdgeValue G F) :
    fundamentalCycleValue G F e f.val = if e = f then 1 else 0 := by
  classical
  have hn : f.val.val ∉ ((forestPathValue G F e.val).val.mapLe F.property.1).edges := by
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    exact fun h => f.property ((forestPathValue G F e.val).val.edges_subset_edgeSet h)
  simp only [fundamentalCycleValue, walkVectorValue, edgeIndicatorValue,
    Set.mem_ofPred_eq, fundamentalCycleWalkValue, SimpleGraph.Walk.edges_cons,
    List.mem_cons, Sym2.mk_fst_out_snd_out, hn, or_false]
  congr 1
  apply propext
  exact ⟨fun h => Subtype.ext (Subtype.ext h.symm),
    fun h => by cases h; rfl⟩

lemma fundamentalCycle_mem (F : SpanningForestValue G) (e : NonforestEdgeValue G F) :
    fundamentalCycleValue G F e ∈ cycleSpaceValue G := by
  apply Submodule.subset_span
  exact ⟨_, fundamentalCycleWalkValue G F e, fundamentalCycle_isCycle G F e, rfl⟩

/-- Nonforest coordinates prove independence before any spanning argument. -/
lemma fundamentalCycles_linearIndependent (F : SpanningForestValue G) :
    LinearIndependent (ZMod 2) (fundamentalCycleValue G F) := by
  classical
  rw [linearIndependent_iff']
  intro s a h e he
  have hx := congrFun h e.val
  simpa [Finset.sum_apply, Pi.smul_apply, fundamentalCycle_coordinates,
    Finset.sum_ite_eq', he] using hx

/-- Binary incidence, as a linear map. -/
def incidenceBoundary : EdgeVectorValue G →ₗ[ZMod 2] (V → ZMod 2) := by
  classical
  letI := Fintype.ofFinite (EdgeValue G)
  exact {
    toFun := fun x v => ∑ e, if v ∈ e.val then x e else 0
    map_add' := by
      intro x y; ext v
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _; split_ifs <;> simp
    map_smul' := by
      intro a x; ext v
      simp only [RingHom.id_apply, Pi.smul_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro e _; split_ifs <;> simp }

/-- The edge subset with its given unordered edges, still on all vertices. -/
def edgeSubsetGraph (S : Set (EdgeValue G)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Subtype.val '' S)

lemma edgeSubsetGraph_le (S : Set (EdgeValue G)) : edgeSubsetGraph G S ≤ G := by
  rw [edgeSubsetGraph, SimpleGraph.fromEdgeSet_le]
  rintro e ⟨⟨x, _, rfl⟩, _⟩
  exact x.property

lemma edgeSubsetGraph_edges (S : Set (EdgeValue G)) (e : Sym2 V) :
    e ∈ (edgeSubsetGraph G S).edgeSet ↔ ∃ h : e ∈ G.edgeSet, (⟨e, h⟩ : EdgeValue G) ∈ S := by
  constructor
  · intro he
    have he' := he
    rw [edgeSubsetGraph, SimpleGraph.edgeSet_fromEdgeSet] at he'
    obtain ⟨⟨x, hx, hxe⟩, _⟩ := he'
    subst e
    exact ⟨x.property, hx⟩
  · rintro ⟨h, hs⟩
    rw [edgeSubsetGraph, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨⟨⟨e, h⟩, hs, rfl⟩, G.not_isDiag_of_mem_edgeSet h⟩

/-- Counting incident edges agrees with the ordinary degree of the edge-subset graph. -/
lemma edgeSubsetGraph_degree (S : Set (EdgeValue G)) (v : V) :
    let : Fintype V := Fintype.ofFinite V
    (edgeSubsetGraph G S).degree v = Nat.card {e : EdgeValue G // e ∈ S ∧ v ∈ e.val} := by
  classical
  dsimp only
  let : Fintype V := Fintype.ofFinite V
  rw [← SimpleGraph.card_incidenceSet_eq_degree, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact {
    toFun := fun e => ⟨⟨e.val, ((edgeSubsetGraph_edges G S e.val).mp e.property.1).choose⟩,
      ((edgeSubsetGraph_edges G S e.val).mp e.property.1).choose_spec, e.property.2⟩
    invFun := fun e => ⟨e.val.val,
      (edgeSubsetGraph_edges G S e.val.val).mpr ⟨e.val.property, e.property.1⟩,
      e.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The incidence of an indicator is its incident-edge count modulo two. -/
lemma incidenceBoundary_indicator (S : Set (EdgeValue G)) (v : V) :
    incidenceBoundary G (edgeIndicatorValue G S) v =
      (Nat.card {e : EdgeValue G // e ∈ S ∧ v ∈ e.val} : ZMod 2) := by
  classical
  let : Fintype (EdgeValue G) := Fintype.ofFinite _
  change (∑ e : EdgeValue G, if v ∈ e.val then (if e ∈ S then (1 : ZMod 2) else 0) else 0) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hv : v ∈ e.val <;> by_cases hs : e ∈ S <;> simp [hv, hs]

lemma incidenceBoundary_eq_zero_iff (S : Set (EdgeValue G)) :
    incidenceBoundary G (edgeIndicatorValue G S) = 0 ↔ EvenDegreeValue G S := by
  rw [funext_iff]
  simp only [incidenceBoundary_indicator, Pi.zero_apply, ZMod.natCast_eq_zero_iff_even]
  rfl

/-- Every vector is the indicator of its support, in the adopted binary coordinates. -/
lemma indicator_support (x : EdgeVectorValue G) :
    edgeIndicatorValue G (edgeSupportValue G x) = x :=
  (edgeSetEquivValue G).apply_symm_apply x

/-- A simple cycle has even incidence at every vertex. -/
lemma cycle_evenDegree {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    EvenDegreeValue G {e | e.val ∈ p.edges} := by
  classical
  intro v
  have hc : Nat.card {e : EdgeValue G // e.val ∈ p.edges ∧ v ∈ e.val} =
      (p.edges.toFinset.filter (fun e => v ∈ e)).card := by
    let t := p.edges.toFinset.filter (fun e => v ∈ e)
    have eqv : {e : EdgeValue G // e.val ∈ p.edges ∧ v ∈ e.val} ≃ t := {
      toFun := fun e => ⟨e.val.val, by
        simpa only [t, Finset.mem_filter, List.mem_toFinset] using e.property⟩
      invFun := fun e =>
        have he : e.val ∈ p.edges ∧ v ∈ e.val := by
          simpa only [t, Finset.mem_filter, List.mem_toFinset] using e.property
        ⟨⟨e.val, p.edges_subset_edgeSet he.1⟩, he⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr eqv).trans (by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe _)
  change Even (Nat.card {e : EdgeValue G // e.val ∈ p.edges ∧ v ∈ e.val})
  rw [hc, hp.isTrail.edges_nodup.card_eq_countP]
  exact (hp.isTrail.even_countP_edges_iff v).mpr (by simp)

lemma cycleSpace_le_ker_incidenceBoundary :
    cycleSpaceValue G ≤ LinearMap.ker (incidenceBoundary G) := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, p, hp, rfl⟩
  exact (incidenceBoundary_eq_zero_iff G _).mpr (cycle_evenDegree G p hp)

/-- A forest whose vertex degrees are all even has no edges. The leaf is
chosen in a component containing an edge, so isolated vertices cause no issue. -/
lemma acyclic_even_degree_eq_bot (H : SimpleGraph V) (hH : H.IsAcyclic)
    (heven : ∀ v, Even (Nat.card (H.neighborSet v))) : H = ⊥ := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro a b hab
  let c := H.connectedComponentMk a
  have ha : a ∈ c.supp := by rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hb : b ∈ c.supp := c.mem_supp_of_adj_mem_supp ha hab
  let va : c := ⟨a, ha⟩
  let vb : c := ⟨b, hb⟩
  have hv : va ≠ vb := fun h => hab.ne (congrArg Subtype.val h)
  have : Nontrivial c := ⟨⟨va, vb, hv⟩⟩
  obtain ⟨v, hv⟩ := (hH.isTree_connectedComponent c).exists_vert_degree_one_of_nontrivial
  have hd : c.toSimpleGraph.degree v = H.degree v := by
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro w hw
    exact c.mem_supp_of_adj_mem_supp v.property hw
  have hev : Even (H.degree v) := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using heven v
  rw [← hd, hv] at hev
  exact (by decide : ¬Even (1 : ℕ)) hev

/-- An even-degree subset contained in a forest is empty. -/
lemma evenDegree_forest_subset_eq_empty (F : SpanningForestValue G)
    (S : Set (EdgeValue G)) (heven : EvenDegreeValue G S)
    (hsub : ∀ e ∈ S, e.val ∈ F.val.edgeSet) : S = ∅ := by
  classical
  let H := edgeSubsetGraph G S
  have hle : H ≤ F.val := by
    apply SimpleGraph.edgeSet_subset_edgeSet.mp
    intro e he
    obtain ⟨h, hs⟩ := (edgeSubsetGraph_edges G S e).mp he
    exact hsub ⟨e, h⟩ hs
  have hbot : H = ⊥ := acyclic_even_degree_eq_bot H
    (F.property.2.1.anti hle) (by
      intro v
      let : Fintype V := Fintype.ofFinite V
      have hd := edgeSubsetGraph_degree G S v
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
      change Even ((edgeSubsetGraph G S).degree v)
      rw [hd]
      exact heven v)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hm := (edgeSubsetGraph_edges G S e.val).mpr ⟨e.property, he⟩
  change e.val ∈ H.edgeSet at hm
  simp [hbot] at hm

lemma forest_supported_ker_eq_zero (F : SpanningForestValue G) (x : EdgeVectorValue G)
    (hx : incidenceBoundary G x = 0)
    (hs : ∀ e : NonforestEdgeValue G F, x e.val = 0) : x = 0 := by
  have heven : EvenDegreeValue G (edgeSupportValue G x) :=
    (incidenceBoundary_eq_zero_iff G _).mp (by rw [indicator_support]; exact hx)
  have hempty : edgeSupportValue G x = ∅ := evenDegree_forest_subset_eq_empty G F _ heven (by
    intro e he
    by_contra hn
    exact he (hs ⟨e, hn⟩))
  rw [← indicator_support G x, hempty]
  ext e
  simp [edgeIndicatorValue]

/-- Eliminate all nonforest coordinates by a finite sum of fundamental cycles. -/
lemma ker_incidenceBoundary_le_span (F : SpanningForestValue G) :
    LinearMap.ker (incidenceBoundary G) ≤
      Submodule.span (ZMod 2) (Set.range (fundamentalCycleValue G F)) := by
  classical
  let : Fintype (NonforestEdgeValue G F) := Fintype.ofFinite _
  intro x hx
  let y := ∑ e : NonforestEdgeValue G F, x e.val • fundamentalCycleValue G F e
  have hy : y ∈ Submodule.span (ZMod 2) (Set.range (fundamentalCycleValue G F)) := by
    apply Submodule.sum_mem
    intro e _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  have hyc : y ∈ cycleSpaceValue G := by
    apply Submodule.sum_mem
    intro e _
    exact Submodule.smul_mem _ _ (fundamentalCycle_mem G F e)
  have hxy : x - y = 0 := forest_supported_ker_eq_zero G F (x - y)
    (by rw [map_sub, hx, cycleSpace_le_ker_incidenceBoundary G hyc, sub_self]) (by
      intro e
      simp [y, Finset.sum_apply, Pi.smul_apply, fundamentalCycle_coordinates])
  rwa [sub_eq_zero.mp hxy]

lemma span_fundamentalCycles_eq (F : SpanningForestValue G) :
    Submodule.span (ZMod 2) (Set.range (fundamentalCycleValue G F)) = cycleSpaceValue G := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact fundamentalCycle_mem G F e
  · exact (cycleSpace_le_ker_incidenceBoundary G).trans (ker_incidenceBoundary_le_span G F)

lemma cycleSpace_eq_ker_incidenceBoundary :
    cycleSpaceValue G = LinearMap.ker (incidenceBoundary G) := by
  obtain ⟨F⟩ := exists_spanningForest G
  exact le_antisymm (cycleSpace_le_ker_incidenceBoundary G)
    ((ker_incidenceBoundary_le_span G F).trans (span_fundamentalCycles_eq G F).le)

/-- W43: all even-degree subsets, and only those, are in the cycle space. -/
theorem cycleSpace_iff_evenDegree : cycleSpace_iff_evenDegreeType := by
  intro V _ G S
  rw [cycleSpace_eq_ker_incidenceBoundary G]
  exact incidenceBoundary_eq_zero_iff G S

/-- W43: the original fundamental cycles give a basis, with no choices of
replacement generators or restrictions on the number of components. -/
theorem fundamentalCycles_basis : fundamentalCycles_basisType := by
  intro V _ G F
  let v : NonforestEdgeValue G F → cycleSpaceValue G :=
    fun e => ⟨fundamentalCycleValue G F e, fundamentalCycle_mem G F e⟩
  have hli : LinearIndependent (ZMod 2) v :=
    LinearIndependent.of_comp (cycleSpaceValue G).subtype (fundamentalCycles_linearIndependent G F)
  have hsp : ⊤ ≤ Submodule.span (ZMod 2) (Set.range v) := by
    exact ((Submodule.span_range_subtype_eq_top_iff (cycleSpaceValue G)
      (fundamentalCycle_mem G F)).mpr (span_fundamentalCycles_eq G F)).ge
  exact ⟨Module.Basis.mk hli hsp, fun e => by rw [Module.Basis.mk_apply]⟩

/-- The forest path is exactly the unique simple path furnished upstream. -/
theorem nonforest_unique_path : nonforest_unique_pathType := by
  intro V _ G F e
  exact ⟨forestPathValue G F e.val, trivial, fun p _ => forestPath_unique G F e.val p⟩

/-- The forest-edge indices are exactly the edges of the spanning subgraph. -/
lemma forestEdge_card (F : SpanningForestValue G) :
    Nat.card (ForestEdgeValue G F) = Nat.card F.val.edgeSet := by
  apply Nat.card_congr
  exact {
    toFun := fun e => ⟨e.val.val, e.property⟩
    invFun := fun e => ⟨⟨e.val, (SimpleGraph.edgeSet_subset_edgeSet.mpr F.property.1) e.property⟩,
      e.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The two complementary edge-index sets partition all the graph's edges. -/
lemma nonforestEdge_card_add_forestEdge_card (F : SpanningForestValue G) :
    Nat.card (NonforestEdgeValue G F) + Nat.card (ForestEdgeValue G F) =
      Nat.card (EdgeValue G) := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl (fun e : EdgeValue G => e.val ∈ F.val.edgeSet))
  rw [Nat.card_sum] at h
  exact (Nat.add_comm _ _).trans h

/-- W43: dimension m - n + c, written additively to include all boundary cases. -/
theorem cycleSpace_dimension : cycleSpace_dimensionType := by
  intro V _ G
  obtain ⟨F⟩ := exists_spanningForest G
  obtain ⟨b, _⟩ := fundamentalCycles_basis G F
  have hd := Module.finrank_eq_nat_card_basis b
  have hc : Nat.card F.val.ConnectedComponent = Nat.card G.ConnectedComponent := by
    change Nat.card (Quot F.val.Reachable) = Nat.card (Quot G.Reachable)
    rw [F.property.2.2]
  have hcn : Nat.card G.ConnectedComponent ≤ Nat.card V :=
    Nat.card_le_card_of_surjective G.connectedComponentMk (fun c => Quot.exists_rep c)
  have hf := Trees.forest_edge_count F.val F.property.2.1
  change Nat.card F.val.edgeSet = Nat.card V - Nat.card F.val.ConnectedComponent at hf
  rw [hc] at hf
  have he := nonforestEdge_card_add_forestEdge_card G F
  rw [forestEdge_card G F, hf] at he
  omega

end FiniteCombinatorics.Graph.BinarySpaces
