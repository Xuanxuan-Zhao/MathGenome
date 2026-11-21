import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.GraphicPolytopes
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.GraphicBridge
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.IndependencePolytope
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.BasePolytope
import Mathlib.Tactic.Linarith

namespace P205.Matroids.Graphic
open _root_.FiniteCombinatorics.Matroid.Graphic
open scoped BigOperators
noncomputable section
universe u v

attribute [local instance] Classical.propDecidable

def vertexInequalities : Specs.P205.Matroids.Graphic.vertexInequalitiesType.{u,v} :=
  @Specs.P205.Matroids.Graphic.vertexInequalitiesValue.{u,v}

def forestIndicators : Specs.P205.Matroids.Graphic.forestIndicatorsType.{u,v} :=
  @Specs.P205.Matroids.Graphic.forestIndicatorsValue.{u,v}

def spanningForestIndicators : Specs.P205.Matroids.Graphic.forestIndicatorsType.{u,v} :=
  @Specs.P205.Matroids.Graphic.spanningForestIndicatorsValue.{u,v}

def spanningTreeIndicators : Specs.P205.Matroids.Graphic.forestIndicatorsType.{u,v} :=
  @Specs.P205.Matroids.Graphic.spanningTreeIndicatorsValue.{u,v}

variable {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFinite G)

/-- Passing to an induced vertex set does not introduce an indexed cycle. -/
lemma forest_induce {S : Set α} {A : Set β} (hA : Forest G A)
    (hAS : A ⊆ inducedEdges G S) : Forest (G.induce S) A := by
  refine ⟨?_, ?_⟩
  · intro e he
    obtain ⟨x, hx, y, hy, hl⟩ := hAS he
    exact ⟨x, y, hl, hx, hy⟩
  · intro n c hc
    let d : Cycle G n := ⟨c.positive, c.vertex, c.edge,
      c.vertex_injective, c.edge_injective, fun i => (c.link i).1⟩
    exact hA.2 n d hc

/-- Every independent set supported on a nonempty induced vertex set has
at most one fewer edge than vertices. -/
lemma induced_rank_le (S : Set α) (hS : S ⊆ G.vertexSet) (hne : S.Nonempty) :
    (rank (graphicMatroid G hG) (inducedEdges G S) : ℝ) ≤ (S.ncard : ℝ) - 1 := by
  obtain ⟨I, hIS, hi, hc⟩ := (rank_maximum (graphicMatroid G hG)
    (inducedEdges G S) (inducedEdges_subset G S)).1
  have hf := forest_induce G ((indep_iff_forest G hG I).mp hi) hIS
  have hfin : IsFinite (G.induce S) := by
    refine ⟨hG.1.subset hS, ?_⟩
    apply hG.2.subset
    rintro e ⟨x, y, hl, _, _⟩
    exact hl.edge_mem
  have hd := forest_cardinality (G.induce S) hfin I hf
  have hpos : 0 < spanningComponentCount (G.induce S) I := by
    let : Fintype (G.induce S).vertexSet := (hG.1.subset hS).fintype
    let : Nonempty (G.induce S).vertexSet := hne.to_subtype
    change 0 < Nat.card (spanningShadow (G.induce S) I).ConnectedComponent
    exact Nat.card_pos
  change I.ncard + spanningComponentCount (G.induce S) I = S.ncard at hd
  have hn : I.ncard + 1 ≤ S.ncard := by omega
  have hr : (I.ncard : ℝ) + 1 ≤ (S.ncard : ℝ) := by exact_mod_cast hn
  change I.ncard = rank (graphicMatroid G hG) (inducedEdges G S) at hc
  rw [← hc]
  linarith

/-- Actual vertex labels in one component of the spanning edge restriction. -/
def componentVertices (A : Set β) (C : (spanningShadow G A).ConnectedComponent) : Set α :=
  Subtype.val '' C.supp

lemma componentVertices_subset (A : Set β) (C : (spanningShadow G A).ConnectedComponent) :
    componentVertices G A C ⊆ G.vertexSet := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

lemma componentVertices_nonempty (A : Set β) (C : (spanningShadow G A).ConnectedComponent) :
    (componentVertices G A C).Nonempty := C.nonempty_supp.image _

/-- Summing component orders counts each actual vertex exactly once. -/
lemma sum_component_orders (A : Set β) [Fintype G.vertexSet]
    [Fintype (spanningShadow G A).ConnectedComponent] :
    ∑ C : (spanningShadow G A).ConnectedComponent,
      ((componentVertices G A C).ncard : ℝ) = (G.vertexSet.ncard : ℝ) := by
  classical
  have hc (C : (spanningShadow G A).ConnectedComponent) :
      ((componentVertices G A C).ncard : ℝ) = ∑ z : G.vertexSet,
        if (spanningShadow G A).connectedComponentMk z = C then (1 : ℝ) else 0 := by
    rw [componentVertices, Set.ncard_image_of_injective _ Subtype.val_injective,
      Finset.sum_boole]
    congr 1
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext z
    simp [SimpleGraph.ConnectedComponent.supp]
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp

/-- Nonnegative edge mass on any edge subset is bounded by the sum of the
masses induced on its component vertex sets. This includes loop edges. -/
lemma subsetSum_le_component_sum (A : Set β) (hA : A ⊆ G.edgeSet)
    (x : G.edgeSet → ℝ) (hx : ∀ e, 0 ≤ x e)
    [Fintype G.vertexSet] [Fintype (spanningShadow G A).ConnectedComponent] :
    subsetSum (graphicMatroid G hG) x A ≤
      ∑ C : (spanningShadow G A).ConnectedComponent,
        subsetSum (graphicMatroid G hG) x (inducedEdges G (componentVertices G A C)) := by
  classical
  let := hG.2.fintype
  change (∑ e : G.edgeSet, if e.val ∈ A then x e else 0) ≤
    ∑ C : (spanningShadow G A).ConnectedComponent,
      ∑ e : G.edgeSet, if e.val ∈ inducedEdges G (componentVertices G A C) then x e else 0
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e _
  have hnn (C : (spanningShadow G A).ConnectedComponent) :
      0 ≤ if e.val ∈ inducedEdges G (componentVertices G A C) then x e else 0 := by
    split_ifs <;> simp_all
  by_cases he : e.val ∈ A
  · rw [ite_eq_left he]
    obtain ⟨a, b, hl⟩ := G.exists_isLink_of_mem_edgeSet (hA he)
    let a' : G.vertexSet := ⟨a, hl.left_mem⟩
    let b' : G.vertexSet := ⟨b, hl.right_mem⟩
    let C := (spanningShadow G A).connectedComponentMk a'
    have ha : a ∈ componentVertices G A C := ⟨a', rfl, rfl⟩
    have hb : b ∈ componentVertices G A C :=
      ⟨b', SimpleGraph.ConnectedComponent.sound (edge_reachable G he hl).symm, rfl⟩
    have hi : e.val ∈ inducedEdges G (componentVertices G A C) := ⟨a, ha, b, hb, hl⟩
    calc
      x e = (if e.val ∈ inducedEdges G (componentVertices G A C) then x e else 0) := by
        rw [ite_eq_left hi]
      _ ≤ _ := Finset.single_le_sum (fun C _ => hnn C) (Finset.mem_univ C)
  · rw [ite_eq_right he]
    exact Finset.sum_nonneg (fun C _ => hnn C)

/-- Vertex-subset bounds imply the rank bound on every edge subset, by
summing over all components of that edge restriction. -/
lemma vertex_bound_on_edges (x : G.edgeSet → ℝ) (hx : x ∈ vertexInequalities G hG)
    (A : Set β) (hA : A ⊆ G.edgeSet) :
    subsetSum (graphicMatroid G hG) x A ≤ (rank (graphicMatroid G hG) A : ℝ) := by
  classical
  let := hG.1.fintype
  let : Fintype (spanningShadow G A).ConnectedComponent := Fintype.ofFinite _
  have hb : ∀ C : (spanningShadow G A).ConnectedComponent,
      subsetSum (graphicMatroid G hG) x (inducedEdges G (componentVertices G A C)) ≤
        ((componentVertices G A C).ncard : ℝ) - 1 :=
    fun C => hx.2 _ (componentVertices_subset G A C) (componentVertices_nonempty G A C)
  have hcount : (Fintype.card (spanningShadow G A).ConnectedComponent : ℝ) =
      (componentCount G A : ℝ) := by
    simp [componentCount, Specs.P205.Matroids.Graphic.componentCountValue,
      spanningComponentCount, Nat.card_eq_fintype_card]
  have hr := rank_add_components G hG A hA
  change rank (graphicMatroid G hG) A + componentCount G A = G.vertexSet.ncard at hr
  have hrr : (rank (graphicMatroid G hG) A : ℝ) + (componentCount G A : ℝ) =
      (G.vertexSet.ncard : ℝ) := by exact_mod_cast hr
  calc
    _ ≤ ∑ C : (spanningShadow G A).ConnectedComponent,
      subsetSum (graphicMatroid G hG) x (inducedEdges G (componentVertices G A C)) :=
        subsetSum_le_component_sum G hG A hA x hx.1
    _ ≤ ∑ C : (spanningShadow G A).ConnectedComponent,
      (((componentVertices G A C).ncard : ℝ) - 1) := Finset.sum_le_sum (fun C _ => hb C)
    _ = (G.vertexSet.ncard : ℝ) - (componentCount G A : ℝ) := by
      rw [Finset.sum_sub_distrib, sum_component_orders]
      simp [hcount]
    _ = _ := by linarith

/-- The vertex-subset description and all graphic rank inequalities agree. -/
theorem vertex_rank_equivalence : Specs.P205.Matroids.Graphic.VertexRankEquivalence := by
  intro α β G hG
  let : (graphicMatroid G hG).Finite := ⟨hG.2⟩
  change vertexInequalities G hG = rankInequalities (graphicMatroid G hG)
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, fun A hA => vertex_bound_on_edges G hG x hx A hA⟩
  · rintro ⟨h0, hS⟩
    refine ⟨h0, ?_⟩
    intro S hSV hne
    exact (hS (inducedEdges G S) (inducedEdges_subset G S)).trans
      (induced_rank_le G hG S hSV hne)

lemma forestIndicators_eq : forestIndicators G = independentIndicators (graphicMatroid G hG) := by
  ext x
  constructor
  · rintro ⟨A, hA, hx⟩
    exact ⟨A, (indep_iff_forest G hG A).mpr hA, funext hx⟩
  · rintro ⟨A, hA, hx⟩
    exact ⟨A, (indep_iff_forest G hG A).mp hA, fun e => congrFun hx e⟩

lemma spanningForestIndicators_eq :
    spanningForestIndicators G = basisIndicators (graphicMatroid G hG) := by
  ext x
  constructor
  · rintro ⟨A, hA, hx⟩
    exact ⟨A, (base_iff_spanningForest G hG A).mpr hA, funext hx⟩
  · rintro ⟨A, hA, hx⟩
    exact ⟨A, (base_iff_spanningForest G hG A).mp hA, fun e => congrFun hx e⟩

lemma spanningTreeIndicators_eq (hC : G.toSimpleGraph.Connected) :
    spanningTreeIndicators G = basisIndicators (graphicMatroid G hG) := by
  ext x
  constructor
  · rintro ⟨A, hA, hx⟩
    exact ⟨A, (connected_base_iff_tree G hG hC A).mpr hA, funext hx⟩
  · rintro ⟨A, hA, hx⟩
    exact ⟨A, (connected_base_iff_tree G hG hC A).mp hA, fun e => congrFun hx e⟩

/-- The ordinary convex hull of forest indicators, including the empty graph. -/
theorem forest_polytope : Specs.P205.Matroids.Graphic.ForestPolytope := by
  intro α β G hG
  let : (graphicMatroid G hG).Finite := ⟨hG.2⟩
  change convexHull ℝ (forestIndicators G) = vertexInequalities G hG
  rw [forestIndicators_eq G hG]
  exact (independence_polytope (graphicMatroid G hG)).trans (vertex_rank_equivalence G hG).symm

/-- Spanning forests impose total edge mass equal to vertices minus all
components, with isolated vertices counted. -/
theorem spanningForest_polytope : Specs.P205.Matroids.Graphic.SpanningForestPolytope := by
  intro α β G hG
  let : (graphicMatroid G hG).Finite := ⟨hG.2⟩
  change convexHull ℝ (spanningForestIndicators G) =
    {x | x ∈ vertexInequalities G hG ∧ subsetSum (graphicMatroid G hG) x G.edgeSet =
      (G.vertexSet.ncard : ℝ) - (componentCount G G.edgeSet : ℝ)}
  rw [spanningForestIndicators_eq G hG]
  have hp : convexHull ℝ (basisIndicators (graphicMatroid G hG)) =
      baseInequalities (graphicMatroid G hG) := base_polytope_eq (graphicMatroid G hG)
  refine hp.trans ?_
  have h := rank_add_components G hG G.edgeSet Set.Subset.rfl
  change rank (graphicMatroid G hG) G.edgeSet + componentCount G G.edgeSet =
    G.vertexSet.ncard at h
  have hr : (rank (graphicMatroid G hG) G.edgeSet : ℝ) =
      (G.vertexSet.ncard : ℝ) - (componentCount G G.edgeSet : ℝ) := by
    have hh : (rank (graphicMatroid G hG) G.edgeSet : ℝ) +
        (componentCount G G.edgeSet : ℝ) = (G.vertexSet.ncard : ℝ) := by exact_mod_cast h
    linarith
  ext x
  change (x ∈ rankInequalities (graphicMatroid G hG) ∧
    subsetSum (graphicMatroid G hG) x G.edgeSet = (rank (graphicMatroid G hG) G.edgeSet : ℝ)) ↔ _
  have heq : vertexInequalities G hG = rankInequalities (graphicMatroid G hG) :=
    vertex_rank_equivalence G hG
  rw [hr, ← heq]
  rfl

/-- Connectedness here includes a vertex, as in the source's tree specialization. -/
theorem spanningTree_polytope : Specs.P205.Matroids.Graphic.SpanningTreePolytope := by
  intro α β G hG hC
  let : (graphicMatroid G hG).Finite := ⟨hG.2⟩
  change convexHull ℝ (spanningTreeIndicators G) =
    {x | x ∈ vertexInequalities G hG ∧ subsetSum (graphicMatroid G hG) x G.edgeSet =
      (G.vertexSet.ncard : ℝ) - 1}
  rw [spanningTreeIndicators_eq G hG hC]
  have hp : convexHull ℝ (basisIndicators (graphicMatroid G hG)) =
      baseInequalities (graphicMatroid G hG) := base_polytope_eq (graphicMatroid G hG)
  refine hp.trans ?_
  have h := rank_add_components G hG G.edgeSet Set.Subset.rfl
  change rank (graphicMatroid G hG) G.edgeSet + componentCount G G.edgeSet =
    G.vertexSet.ncard at h
  have hc : componentCount G G.edgeSet = 1 := connected_components_one G hC
  rw [hc] at h
  have hr : (rank (graphicMatroid G hG) G.edgeSet : ℝ) = (G.vertexSet.ncard : ℝ) - 1 := by
    have hh : (rank (graphicMatroid G hG) G.edgeSet : ℝ) + 1 =
        (G.vertexSet.ncard : ℝ) := by exact_mod_cast h
    linarith
  ext x
  change (x ∈ rankInequalities (graphicMatroid G hG) ∧
    subsetSum (graphicMatroid G hG) x G.edgeSet = (rank (graphicMatroid G hG) G.edgeSet : ℝ)) ↔ _
  have heq : vertexInequalities G hG = rankInequalities (graphicMatroid G hG) :=
    vertex_rank_equivalence G hG
  rw [hr, ← heq]
  rfl

/-- A singleton vertex bound annihilates each loop, retaining its original edge label. -/
theorem loop_zero : Specs.P205.Matroids.Graphic.LoopZero := by
  intro α β G hG x hx e a hl
  let : (graphicMatroid G hG).Finite := ⟨hG.2⟩
  let := hG.2.fintype
  have hs : subsetSum (graphicMatroid G hG) x (inducedEdges G {a}) ≤ 0 := by
    have hs' : subsetSum (graphicMatroid G hG) x (inducedEdges G {a}) ≤
        (({a} : Set α).ncard : ℝ) - 1 :=
      hx.2 {a} (Set.singleton_subset_iff.mpr hl.left_mem) (Set.singleton_nonempty a)
    simpa using hs'
  have hi : e ∈ inducedEdges G {a} := ⟨a, rfl, a, rfl, hl⟩
  have ht : x ⟨e, hl.edge_mem⟩ ≤ subsetSum (graphicMatroid G hG) x (inducedEdges G {a}) := by
    change _ ≤ ∑ f : G.edgeSet, if f.val ∈ inducedEdges G {a} then x f else 0
    have hm := Finset.single_le_sum (s := Finset.univ)
      (f := fun f : G.edgeSet => if f.val ∈ inducedEdges G {a} then x f else 0)
      (fun f _ => by split_ifs <;> simp_all [hx.1 f]) (Finset.mem_univ ⟨e, hl.edge_mem⟩)
    simpa only [ite_eq_left hi] using hm
  exact le_antisymm (ht.trans hs) (hx.1 _)

end
end P205.Matroids.Graphic
