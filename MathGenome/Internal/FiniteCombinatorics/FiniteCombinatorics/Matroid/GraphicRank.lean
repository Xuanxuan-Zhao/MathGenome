import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GraphicRank
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.GraphicIncidence
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ForwardPresentations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

/-! Graphic bases and rank, paper.tex W72 and its subset-rank use in W77.
The incidence span is the kernel of the component-sum map. Rank-nullity gives
v − c over every field; the graph and its edge restrictions retain isolated vertices.
-/
universe u v w
noncomputable section
namespace FiniteCombinatorics.Matroid.Graphic
open Set Submodule
attribute [local instance] Classical.propDecidable
variable {α : Type u} {β : Type v} (G : _root_.Graph α β)
variable (K : Type w) [Field K] (o : Orientation G)

/-- The unit coordinate vector at a real vertex. -/
def vertexUnit (x : G.vertexSet) : G.vertexSet → K :=
  fun y => if y = x then 1 else 0

lemma traversal_column {e : β} {x y : G.vertexSet} (h : G.IsLink e x.val y.val) :
    ∃ t : K, t ≠ 0 ∧ t • column G K o e = vertexUnit G K y - vertexUnit G K x := by
  obtain ⟨t, ht, hcol⟩ := traversal_coefficient G K o h
  refine ⟨t, ht, hcol.trans ?_⟩
  ext z
  simp only [vertexUnit, Pi.sub_apply, Subtype.ext_iff]

lemma reachable_difference_mem_span {A : Set β} {x y : G.vertexSet}
    (h : (spanningShadow G A).Reachable x y) :
    vertexUnit G K y - vertexUnit G K x ∈ span K (column G K o '' A) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons x z y hx p ih =>
    obtain ⟨e, heA, he⟩ := hx.2
    obtain ⟨t, _, ht⟩ := traversal_column G K o he
    have hm := (span K (column G K o '' A)).smul_mem t
      (subset_span (mem_image_of_mem _ heA))
    rw [ht] at hm
    convert (span K (column G K o '' A)).add_mem hm ih using 1; abel

/-- Sum the coordinates separately on each reachability class. -/
def componentSum (A : Set β) [Fintype G.vertexSet] :
    (G.vertexSet → K) →ₗ[K] ((spanningShadow G A).ConnectedComponent → K) where
  toFun f c := ∑ x, if (spanningShadow G A).connectedComponentMk x = c then f x else 0
  map_add' f g := by
    ext c
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  map_smul' a f := by
    ext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp

lemma componentSum_unit (A : Set β) [Fintype G.vertexSet] (x : G.vertexSet)
    (c : (spanningShadow G A).ConnectedComponent) :
    componentSum G K A (vertexUnit G K x) c =
      if (spanningShadow G A).connectedComponentMk x = c then 1 else 0 := by
  change (∑ z, if (spanningShadow G A).connectedComponentMk z = c then (if z = x then (1 : K) else 0) else 0) = _
  rw [Finset.sum_eq_single x]
  · simp
  · intro z _ hz
    simp [hz]
  · simp

lemma edge_reachable {A : Set β} {e : β} (he : e ∈ A) {x y : G.vertexSet}
    (hl : G.IsLink e x.val y.val) : (spanningShadow G A).Reachable x y := by
  by_cases hxy : x = y
  · subst y; rfl
  · exact SimpleGraph.Adj.reachable ⟨hxy, e, he, hl⟩

theorem shadow_reachable_iff :
    Specs.FiniteCombinatorics.Matroid.GraphicRank.shadow_reachable_iff := by
  intro α β G A x y
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | @cons x z y h p ih =>
      have hs : Relation.ReflTransGen
          (fun a b : G.vertexSet => ∃ e ∈ A, G.IsLink e a.val b.val) x z :=
        Relation.ReflTransGen.single h.2
      exact hs.trans ih
  · intro h
    induction h with
    | refl => rfl
    | tail h he ih =>
      obtain ⟨e, heA, he⟩ := he
      exact ih.trans (edge_reachable G heA he)

lemma componentSum_column (A : Set β) [Fintype G.vertexSet] {e : β} (he : e ∈ A)
    (heG : e ∈ G.edgeSet) : componentSum G K A (column G K o e) = 0 := by
  let x : G.vertexSet := ⟨o.tail ⟨e, heG⟩, (o.link ⟨e, heG⟩).left_mem⟩
  let y : G.vertexSet := ⟨o.head ⟨e, heG⟩, (o.link ⟨e, heG⟩).right_mem⟩
  have hc := SimpleGraph.ConnectedComponent.sound
    (edge_reachable G he (show G.IsLink e x.val y.val from o.link ⟨e, heG⟩))
  have hcol : column G K o e = vertexUnit G K y - vertexUnit G K x := by
    ext z
    simp [column, heG, vertexUnit, x, y, Subtype.ext_iff]
  rw [hcol, map_sub]
  ext c
  simp [componentSum_unit, hc]

lemma span_le_componentSum_ker {A : Set β} [Fintype G.vertexSet]
    (hA : A ⊆ G.edgeSet) :
    span K (column G K o '' A) ≤ LinearMap.ker (componentSum G K A) := by
  apply span_le.mpr
  rintro _ ⟨e, he, rfl⟩
  exact componentSum_column G K o A he (hA he)

/-- Choose an actual vertex in each component; this requires no vertex when
there are no components. -/
def componentRoot (A : Set β) (c : (spanningShadow G A).ConnectedComponent) :
    G.vertexSet := Quot.out c

lemma componentRoot_spec (A : Set β) (c : (spanningShadow G A).ConnectedComponent) :
    (spanningShadow G A).connectedComponentMk (componentRoot G A c) = c := Quot.out_eq c

lemma componentSum_surjective (A : Set β) [Fintype G.vertexSet]
    [Fintype (spanningShadow G A).ConnectedComponent] :
    Function.Surjective (componentSum G K A) := by
  intro f
  refine ⟨∑ c, f c • vertexUnit G K (componentRoot G A c), ?_⟩
  rw [map_sum]
  ext d
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    componentSum_unit, componentRoot_spec]
  simp

lemma root_sum_eq_zero (A : Set β) [Fintype G.vertexSet]
    [Fintype (spanningShadow G A).ConnectedComponent] {f : G.vertexSet → K}
    (hf : componentSum G K A f = 0) :
    ∑ x, f x • vertexUnit G K (componentRoot G A
      ((spanningShadow G A).connectedComponentMk x)) = 0 := by
  rw [← Fintype.sum_fiberwise (spanningShadow G A).connectedComponentMk]
  apply Finset.sum_eq_zero
  intro c _
  have hsum : ∑ x : {x // (spanningShadow G A).connectedComponentMk x = c},
      f x.val = 0 := by
    have hc := congrFun hf c
    simpa [componentSum, ← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter] using hc
  simp_rw [show ∀ x : {x // (spanningShadow G A).connectedComponentMk x = c},
    (spanningShadow G A).connectedComponentMk x.val = c from fun x => x.property]
  rw [← Finset.sum_smul, hsum, zero_smul]

/-- Telescoping along walks gives the reverse inclusion: a vector whose sum
on every component vanishes is a sum of incidence columns. -/
lemma span_eq_componentSum_ker {A : Set β} [Fintype G.vertexSet]
    [Fintype (spanningShadow G A).ConnectedComponent] (hA : A ⊆ G.edgeSet) :
    span K (column G K o '' A) = LinearMap.ker (componentSum G K A) := by
  apply le_antisymm (span_le_componentSum_ker G K o hA)
  intro f hf
  have hzero : componentSum G K A f = 0 := hf
  have hsum : ∑ x, f x •
      (vertexUnit G K x - vertexUnit G K (componentRoot G A
        ((spanningShadow G A).connectedComponentMk x))) ∈
        span K (column G K o '' A) := by
    apply Submodule.sum_mem
    intro x _
    apply Submodule.smul_mem
    apply reachable_difference_mem_span
    exact SimpleGraph.ConnectedComponent.exact (componentRoot_spec G A _)
  have hunits : ∑ x, f x • vertexUnit G K x = f := by
    ext y
    simp [vertexUnit]
  simpa only [smul_sub, Finset.sum_sub_distrib, hunits,
    root_sum_eq_zero G K A hzero, sub_zero] using hsum

lemma difference_mem_span_iff {A : Set β} [Fintype G.vertexSet]
    (hA : A ⊆ G.edgeSet) (x y : G.vertexSet) :
    vertexUnit G K y - vertexUnit G K x ∈ span K (column G K o '' A) ↔
      (spanningShadow G A).Reachable x y := by
  constructor
  · intro hm
    have h := span_le_componentSum_ker G K o hA hm
    have hc := congrFun h ((spanningShadow G A).connectedComponentMk x)
    rw [map_sub] at hc
    simp only [Pi.sub_apply, componentSum_unit, Pi.zero_apply] at hc
    by_cases heq : (spanningShadow G A).connectedComponentMk y =
        (spanningShadow G A).connectedComponentMk x
    · exact (SimpleGraph.ConnectedComponent.exact heq).symm
    · simp [heq] at hc
  · exact reachable_difference_mem_span G K o

lemma column_mem_span_iff {A : Set β} [Fintype G.vertexSet]
    (hA : A ⊆ G.edgeSet) {e : β} {x y : G.vertexSet}
    (hl : G.IsLink e x.val y.val) :
    column G K o e ∈ span K (column G K o '' A) ↔
      (spanningShadow G A).Reachable x y := by
  obtain ⟨t, ht, hcol⟩ := traversal_column G K o hl
  rw [← (span K (column G K o '' A)).smul_mem_iff ht, hcol]
  exact difference_mem_span_iff G K o hA x y

lemma shadow_mono {A B : Set β} (h : B ⊆ A) :
    spanningShadow G B ≤ spanningShadow G A := by
  rintro x y ⟨hne, e, heB, he⟩
  exact ⟨hne, e, h heB, he⟩

lemma basis_span {hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G}
    {B A : Set β} (hB : (incidenceMatroid G hG K o).IsBasis B A) :
    span K (column G K o '' A) = span K (column G K o '' B) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    by_contra hn
    have hi : B ⊆ G.edgeSet ∧ LinearIndepOn K (column G K o) B := hB.indep
    have hins : (incidenceMatroid G hG K o).Indep (insert e B) :=
      ⟨insert_subset (hB.subset_ground he) hi.1, hi.2.insert hn⟩
    exact hn (subset_span ⟨e, hB.mem_of_insert_indep he hins, rfl⟩)
  · exact span_mono (image_mono hB.subset)

theorem basis_iff_spanningForest :
    Specs.FiniteCombinatorics.Matroid.GraphicRank.basis_iff_spanningForest := by
  intro α β G hG K _ o B A hA
  let : Finite G.vertexSet := hG.1.to_subtype
  let : Fintype G.vertexSet := Fintype.ofFinite _
  constructor
  · intro hB
    have hBF := (incidenceMatroid_indep G hG K o B).mp hB.indep
    refine ⟨hB.subset, hBF, ?_⟩
    intro x y hxy
    obtain ⟨p⟩ := hxy
    induction p with
    | nil => rfl
    | @cons x z y hx p ih =>
      obtain ⟨e, heA, he⟩ := hx.2
      have hcol : column G K o e ∈ span K (column G K o '' B) := by
        rw [← basis_span G K o hB]
        exact subset_span ⟨e, heA, rfl⟩
      exact ((column_mem_span_iff G K o hBF.1 he).mp hcol).trans ih
  · rintro ⟨hBA, hBF, hconn⟩
    have hi := (incidenceMatroid_indep G hG K o B).mpr hBF
    have hli : LinearIndepOn K (column G K o) B := hi.2
    apply hi.isBasis_of_forall_insert hBA
    rintro e ⟨heA, heB⟩
    obtain ⟨x, y, he⟩ := G.exists_isLink_of_mem_edgeSet (hA heA)
    let x' : G.vertexSet := ⟨x, he.left_mem⟩
    let y' : G.vertexSet := ⟨y, he.right_mem⟩
    have hr : (spanningShadow G B).Reachable x' y' :=
      hconn x' y' (edge_reachable G heA he)
    have hcol := (column_mem_span_iff G K o hBF.1 he).mpr hr
    refine ⟨?_, insert_subset (hA heA) hBF.1⟩
    intro hins
    exact heB ((hli.mem_span_iff.mp hcol) hins.2)

theorem base_iff_spanningForest :
    Specs.FiniteCombinatorics.Matroid.GraphicRank.base_iff_spanningForest := by
  intro α β G hG K _ o B
  rw [← _root_.Matroid.isBasis_ground_iff]
  exact basis_iff_spanningForest G hG K o B G.edgeSet Subset.rfl

theorem component_tree : Specs.FiniteCombinatorics.Matroid.GraphicRank.component_tree := by
  intro α β G B A hB C
  let D := (spanningShadow G B).connectedComponentMk (componentRoot G A C)
  have hs : D.supp = C.supp := by
    ext x
    change ((spanningShadow G B).connectedComponentMk x = D) ↔
      (spanningShadow G A).connectedComponentMk x = C
    rw [← componentRoot_spec G A C]
    constructor
    · intro h
      apply SimpleGraph.ConnectedComponent.sound
      exact (SimpleGraph.ConnectedComponent.exact h).mono (shadow_mono G hB.1)
    · intro h
      exact SimpleGraph.ConnectedComponent.sound
        (hB.2.2 x _ (SimpleGraph.ConnectedComponent.exact h))
  rw [← hs]
  exact ⟨D.connected_toSimpleGraph, hB.2.1.shadow_acyclic G |>.induce D.supp⟩

/-- For a simple indexed graph, acyclicity of its adjacency shadow also
excludes every indexed cycle. Lengths one and two are excluded by simplicity. -/
lemma forest_of_simple_shadow (H : _root_.Graph α β) [H.Simple]
    (hH : H.toSimpleGraph.IsAcyclic) : Forest H H.edgeSet := by
  refine ⟨Subset.rfl, ?_⟩
  intro n c _
  have hn : 3 ≤ n := by
    match n with
    | 0 => exact False.elim (Nat.not_lt_zero _ c.positive)
    | 1 =>
      have h : H.IsLink (c.edge 0) (c.vertex 0) (c.vertex 0) := by
        simpa only [finRotate_one, Equiv.refl_apply] using c.link 0
      exact False.elim (h.ne rfl)
    | 2 =>
      have h0 : H.IsLink (c.edge 0) (c.vertex 0) (c.vertex 1) := by
        simpa [finRotate_apply] using c.link 0
      have h1 : H.IsLink (c.edge 1) (c.vertex 0) (c.vertex 1) := by
        simpa [finRotate_apply] using (c.link 1).symm
      exact False.elim (by simpa using c.edge_injective (h0.eq h1))
    | _ + 3 => omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  let f (i : Fin (m + 3)) : H.vertexSet := ⟨c.vertex i, (c.link i).left_mem⟩
  apply (SimpleGraph.isAcyclic_iff_free_cycleGraph.mp hH) (m + 3) (by omega)
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    have hij' : j = i - 1 ∨ j = i + 1 := by
      have hj : j ∈ (SimpleGraph.cycleGraph (m + 3)).neighborSet i := hij
      rw [SimpleGraph.cycleGraph_neighborSet] at hj
      exact hj
    have hlink : ∃ e, H.IsLink e (f i).val (f j).val := by
      rcases hij' with rfl | rfl
      · refine ⟨c.edge (i - 1), ?_⟩
        simpa [f, finRotate_apply] using (c.link (i - 1)).symm
      · exact ⟨c.edge i, by simpa [f, finRotate_apply] using c.link i⟩
    obtain ⟨e, he⟩ := hlink
    exact ⟨fun h => he.ne (congrArg Subtype.val h), e, he⟩
  · intro i j h
    exact c.vertex_injective (congrArg Subtype.val h)

lemma shadow_acyclic_of_component_trees {B A : Set β} (hBA : B ⊆ A)
    (hT : ∀ C : (spanningShadow G A).ConnectedComponent,
      ((spanningShadow G B).induce C.supp).IsTree) :
    (spanningShadow G B).IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_free_cycleGraph.mpr
  intro n hn ⟨f⟩
  let i₀ : Fin n := ⟨0, by omega⟩
  let C := (spanningShadow G A).connectedComponentMk (f i₀)
  have hf (i : Fin n) : f i ∈ C.supp := by
    apply SimpleGraph.ConnectedComponent.sound
    exact ((SimpleGraph.preconnected_cycleGraph i i₀).map f.toHom).mono (shadow_mono G hBA)
  apply (SimpleGraph.isAcyclic_iff_free_cycleGraph.mp (hT C).isAcyclic) n hn
  refine ⟨⟨⟨fun i => ⟨f i, hf i⟩, fun {_ _} h => f.toHom.map_adj h⟩, ?_⟩⟩
  intro i j h
  exact f.injective (congrArg Subtype.val h)

theorem basis_iff_component_trees :
    Specs.FiniteCombinatorics.Matroid.GraphicRank.basis_iff_component_trees := by
  intro α β G hG K _ o B A hA
  rw [basis_iff_spanningForest G hG K o B A hA]
  constructor
  · intro hB
    exact ⟨hB.1, hB.2.1.restrict_simple G, component_tree G B A hB⟩
  · rintro ⟨hBA, hsimple, hT⟩
    let : (G.restrict B).Simple := hsimple
    have ha := shadow_acyclic_of_component_trees G hBA hT
    have hF : Forest G B := by
      apply (forest_restrict G B).mp
      have hE : (G.restrict B).edgeSet = B :=
        inter_eq_right.mpr (hBA.trans hA)
      simpa only [hE] using forest_of_simple_shadow (G.restrict B) ha
    refine ⟨hBA, hF, ?_⟩
    intro x y hxy
    let C := (spanningShadow G A).connectedComponentMk x
    have hy : y ∈ C.supp := SimpleGraph.ConnectedComponent.sound hxy.symm
    have hr := (hT C).connected.preconnected ⟨x, rfl⟩ ⟨y, hy⟩
    exact hr.map (SimpleGraph.Embedding.induce C.supp).toHom

theorem base_iff_component_trees :
    Specs.FiniteCombinatorics.Matroid.GraphicRank.base_iff_component_trees := by
  intro α β G hG K _ o B
  rw [← _root_.Matroid.isBasis_ground_iff]
  exact basis_iff_component_trees G hG K o B G.edgeSet Subset.rfl

theorem forest_extension : Specs.FiniteCombinatorics.Matroid.GraphicRank.forest_extension := by
  intro α β G hG I A hI hIA hA
  obtain ⟨o⟩ := orientation_exists G
  have hi := (incidenceMatroid_indep G hG ℚ o I).mpr hI
  obtain ⟨B, hB, hIB⟩ := basisExtension (incidenceMatroid G hG ℚ o) I A hi hIA hA
  exact ⟨B, hIB, (basis_iff_spanningForest G hG ℚ o B A hA).mp hB⟩

theorem rank_eq_vertices_sub_components :
    Specs.FiniteCombinatorics.Matroid.GraphicRank.rank_eq_vertices_sub_components := by
  intro α β G hG K _ o A hA
  let : Finite G.vertexSet := hG.1.to_subtype
  let : Fintype G.vertexSet := Fintype.ofFinite _
  let : Fintype (spanningShadow G A).ConnectedComponent := Fintype.ofFinite _
  have hd := (componentSum G K A).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (componentSum_surjective G K A),
    finrank_top, Module.finrank_pi, Module.finrank_pi,
    ← span_eq_componentSum_ker G K o hA] at hd
  have hr := vectorRank K G.edgeSet hG.2 (column G K o) A hA
  change Expected.rank (incidenceMatroid G hG K o) A = _ at hr
  rw [hr]
  have hc : Fintype.card (spanningShadow G A).ConnectedComponent =
      spanningComponentCount G A := by simp [spanningComponentCount, Nat.card_eq_fintype_card]
  have hv : Fintype.card G.vertexSet = G.vertexSet.ncard := Set.fintypeCard_eq_ncard _
  rw [hc, hv] at hd
  exact (show (Module.finrank K (span K (column G K o '' A)) : ℤ) =
    (G.vertexSet.ncard : ℤ) - (spanningComponentCount G A : ℤ) by omega)

theorem total_rank : Specs.FiniteCombinatorics.Matroid.GraphicRank.total_rank := by
  intro α β G hG K _ o
  have hr := rank_eq_vertices_sub_components G hG K o G.edgeSet Subset.rfl
  change Expected.rank (incidenceMatroid G hG K o) G.edgeSet =
    (G.vertexSet.ncard : ℤ) - (Nat.card (G.restrict G.edgeSet).toSimpleGraph.ConnectedComponent : ℤ) at hr
  rw [_root_.Graph.restrict_self] at hr
  exact hr

theorem forest_cardinality :
    Specs.FiniteCombinatorics.Matroid.GraphicRank.forest_cardinality := by
  intro α β G hG A hA
  obtain ⟨o⟩ := orientation_exists G
  have hi := (incidenceMatroid_indep G hG ℚ o A).mpr hA
  have hr := rank_eq_vertices_sub_components G hG ℚ o A hA.1
  have hc := basisCardinality (incidenceMatroid G hG ℚ o) A A hi.isBasis_self
  change (A.ncard : ℤ) = Expected.rank (incidenceMatroid G hG ℚ o) A at hc
  rw [← hc] at hr
  omega

end FiniteCombinatorics.Matroid.Graphic
