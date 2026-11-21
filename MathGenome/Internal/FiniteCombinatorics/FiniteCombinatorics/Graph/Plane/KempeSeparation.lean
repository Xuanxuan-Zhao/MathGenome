import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Plane.RealizationGeometry
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Euler.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Topology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Applications.JordanBrouwer

/-! Polygonal Kempe separation for W63. Walk traces are the actual drawn edge
sets. An embedded circle, its Jordan common boundary, and two local angular
sectors prove the alternating-spoke and disjoint-palette obstructions. -/

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Plane
open Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation

abbrev walkTrace := @Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation.walkTrace

theorem walk_trace_vertex : walk_trace_vertexType := by
  intro V _ G D a b p v
  induction p with
  | nil => simp [Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation.walkTrace,
      D.point_injective.eq_iff]
  | @cons a b c h p ih =>
    change D.point v ∈ D.edge ⟨s(a,b), h⟩ ∪ walkTrace D p ↔ v ∈ a :: p.support
    rw [Set.mem_union, vertex_on_edge D a b v h, ih, List.mem_cons]
    constructor
    · rintro ((rfl | rfl) | hv)
      · exact Or.inl rfl
      · exact Or.inr p.start_mem_support
      · exact Or.inr hv
    · rintro (rfl | hv)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hv

theorem walk_trace_compact : walk_trace_compactType := by
  intro V _ G D a b p
  induction p with
  | nil => exact isCompact_singleton
  | cons h p ih => exact (edge_compact D ⟨_, h⟩).union ih

lemma polygonal_union {s t : Set Point} (hs : IsPolygonal s) (ht : IsPolygonal t) :
    IsPolygonal (s ∪ t) := by
  obtain ⟨n, a, b, rfl⟩ := hs
  obtain ⟨m, c, d, rfl⟩ := ht
  let e := (Finite.equivFin (Fin n ⊕ Fin m)).symm
  refine ⟨_, (Sum.elim a c) ∘ e, (Sum.elim b d) ∘ e, ?_⟩
  ext z
  simp only [Set.mem_union, Set.mem_iUnion, Function.comp_apply]
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨e.symm (Sum.inl i), by simpa using hi⟩
    · exact ⟨e.symm (Sum.inr i), by simpa using hi⟩
  · rintro ⟨i, hi⟩
    cases h : e i with
    | inl j => exact Or.inl ⟨j, by simpa [h] using hi⟩
    | inr j => exact Or.inr ⟨j, by simpa [h] using hi⟩

theorem walk_trace_polygonal : walk_trace_polygonalType := by
  intro V _ G D a b p
  induction p with
  | @nil a => exact ⟨1, fun _ => D.point a, fun _ => D.point a, by
      simp [Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation.walkTrace]⟩
  | cons h p ih => exact polygonal_union (D.edge_arc _ _ h).1 ih

theorem closed_walk_cycle : closed_walk_cycleType := by
  intro V _ G x a c ha hc p hac hp hx
  apply (cycle_iff G x _).mpr
  constructor
  · cases p with
    | nil => exact False.elim (hac rfl)
    | cons h q => simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]; omega
  · have hn : (x :: p.support).Nodup := List.nodup_cons.mpr ⟨hx, hp.support_nodup⟩
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
      ← List.cons_append, List.dropLast_concat]
    exact hn

theorem walk_trace_joined : walk_trace_joinedType := by
  intro V _ G D a b p
  induction p with
  | nil => exact JoinedIn.refl (Set.mem_singleton _)
  | cons h p ih =>
    obtain ⟨_, q, _, hq⟩ := D.edge_arc _ _ h
    have hfirst : JoinedIn (D.edge ⟨_, h⟩) _ _ :=
      ⟨q, fun t => hq ▸ Set.mem_range_self t⟩
    exact (hfirst.mono Set.subset_union_left).trans (ih.mono Set.subset_union_right)

section TraceDisjointness
variable {V : Type u} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)

/-- Nonincident drawn edges cannot intersect. -/
lemma disjoint_edges_of_endpoints {e f : G.edgeSet}
    (h : ∀ v : V, v ∈ e.val → v ∉ f.val) : Disjoint (D.edge e) (D.edge f) := by
  have hef : e ≠ f := by
    intro hef
    obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.val
    have ha : a ∈ e.val := hab ▸ Sym2.mem_mk_left a b
    exact h a ha (hef ▸ ha)
  apply Set.disjoint_left.mpr
  intro z he hf
  have hz : z ∈ D.point '' {v | v ∈ e.val ∧ v ∈ f.val} := by
    rw [← D.edge_intersection e f hef]
    exact ⟨he, hf⟩
  obtain ⟨v, hv, _⟩ := hz
  exact h v hv.1 hv.2

lemma edge_disjoint_walk_trace {e : G.edgeSet} {a b : V} (p : G.Walk a b)
    (h : ∀ v : V, v ∈ e.val → v ∉ p.support) :
    Disjoint (D.edge e) (walkTrace D p) := by
  induction p with
  | nil =>
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have heq : z = D.point _ := hz'
    subst z
    exact h _ ((D.vertex_edge e _).mp hz) (by simp)
  | @cons a b c hab p ih =>
    apply Set.disjoint_union_right.mpr
    constructor
    · apply disjoint_edges_of_endpoints D
      intro v hv hv'
      rcases Sym2.mem_iff.mp hv' with rfl | rfl
      · exact h _ hv (by simp)
      · exact h _ hv (by simp [p.start_mem_support])
    · exact ih (fun v hv hmem => h v hv (List.mem_cons_of_mem _ hmem))

end TraceDisjointness

theorem disjoint_walk_traces : disjoint_walk_tracesType := by
  intro V _ G D a b c d p q hpq
  induction p with
  | nil =>
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have heq : z = D.point _ := hz
    subst z
    exact hpq (by simp) ((walk_trace_vertex D q _).mp hz')
  | @cons a b c hab p ih =>
    apply Set.disjoint_union_left.mpr
    constructor
    · apply edge_disjoint_walk_trace D q
      intro v hv hvq
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hpq (by simp) hvq
      · exact hpq (by simp [p.start_mem_support]) hvq
    · exact ih (fun v hv hvq => hpq (List.mem_cons_of_mem _ hv) hvq)

theorem walk_avoiding_set : walk_avoiding_setType := by
  intro V _ G D a b p K hd
  have hj : JoinedIn Kᶜ (D.point a) (D.point b) :=
    (walk_trace_joined D p).mono (fun z hz => fun hzK => Set.disjoint_left.mp hd hz hzK)
  obtain ⟨q, hq⟩ := hj
  have hc : IsPreconnected (Set.range q) := isPreconnected_range q.continuous
  apply connectedComponentIn_eq
  apply hc.subset_connectedComponentIn
    (show D.point a ∈ Set.range q from ⟨0, q.source⟩)
    (by rintro z ⟨t, rfl⟩; exact hq t)
  exact ⟨1, q.target⟩

theorem local_sectors_distinct : local_sectors_distinctType := by
  intro X _ S U A B x a b p q hU hxU hcover hAS hBS hA hB ha hb hxp hxq hpq hab
  have hAsub : A ⊆ connectedComponentIn S a := hA.subset_connectedComponentIn ha hAS
  have hBsub : B ⊆ connectedComponentIn S a := by
    rw [hab]
    exact hB.subset_connectedComponentIn hb hBS
  have hlocal : U ∩ S ⊆ connectedComponentIn S a := by
    intro z hz
    exact (hcover hz).elim (fun h => hAsub h) (fun h => hBsub h)
  have heq (r : X) (hxr : x ∈ closure (connectedComponentIn S r)) :
      connectedComponentIn S r = connectedComponentIn S a := by
    obtain ⟨z, hzU, hzr⟩ := mem_closure_iff.mp hxr U hU hxU
    have hza := hlocal ⟨hzU, connectedComponentIn_subset S r hzr⟩
    exact (connectedComponentIn_eq hzr).trans (connectedComponentIn_eq hza).symm
  exact hpq ((heq p hxp).trans (heq q hxq).symm)

theorem punctured_path_component : punctured_path_componentType := by
  intro X _ x y p K hK t ht
  have htpos : (0 : unitInterval) < t := lt_of_le_of_ne (unitInterval.nonneg t) ht.symm
  have hpre : IsPreconnected (p '' (Set.Ioi (0 : unitInterval))) :=
    isPreconnected_Ioi.image p p.continuous.continuousOn
  have hsub : p '' (Set.Ioi (0 : unitInterval)) ⊆ Kᶜ := by
    rintro z ⟨s, hs, rfl⟩
    exact hK s (ne_of_gt hs)
  have hmem : p t ∈ connectedComponentIn Kᶜ y := by
    apply hpre.subset_connectedComponentIn
      (show y ∈ p '' (Set.Ioi (0 : unitInterval)) from ⟨1, by simp, p.target⟩) hsub
    exact ⟨t, htpos, rfl⟩
  exact (connectedComponentIn_eq hmem).symm

theorem disjoint_palette_traces : disjoint_palette_tracesType := by
  intro V _ G D a b c d p q C color A B hAB hp hq
  apply disjoint_walk_traces D p q
  intro v hvp hvq
  exact Set.disjoint_left.mp hAB (hp v hvp) (hq v hvq)

theorem closed_trace_vertex : closed_trace_vertexType := by
  intro V _ G D x a c ha hc p v
  unfold closedTrace
  rw [Set.mem_union, Set.mem_union, vertex_on_edge D x a v ha,
    vertex_on_edge D x c v hc, walk_trace_vertex D p v]
  have hpa := p.start_mem_support
  have hpc := p.end_mem_support
  aesop

theorem closed_trace_polygonal : closed_trace_polygonalType := by
  intro V _ G D x a c ha hc p
  exact polygonal_union (polygonal_union (D.edge_arc _ _ ha).1
    (walk_trace_polygonal D p)) (D.edge_arc _ _ hc).1


/-- Concatenating two embedded arcs which meet only at their common endpoint
preserves injectivity. This includes the joining parameter itself. -/
lemma path_trans_injective {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : _root_.Path a b) (q : _root_.Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hi : Set.range p ∩ Set.range q ⊆ {b}) :
    Function.Injective (p.trans q) := by
  have cross (s t : unitInterval) (hst : p s = q t) : s = 1 ∧ t = 0 := by
    have hb : p s = b := hi ⟨⟨s, rfl⟩, ⟨t, hst.symm⟩⟩
    exact ⟨hp (hb.trans p.target.symm), hq (hst.symm.trans (hb.trans q.source.symm))⟩
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have hh := congrArg Subtype.val (hp hst)
    apply Subtype.ext
    dsimp at hh
    linarith
  · obtain ⟨hh, hh'⟩ := cross _ _ hst
    have h1 := congrArg Subtype.val hh
    have h2 := congrArg Subtype.val hh'
    apply Subtype.ext
    dsimp at h1 h2
    linarith
  · obtain ⟨hh, hh'⟩ := cross _ _ hst.symm
    have h1 := congrArg Subtype.val hh
    have h2 := congrArg Subtype.val hh'
    apply Subtype.ext
    dsimp at h1 h2
    linarith
  · have hh := congrArg Subtype.val (hq hst)
    apply Subtype.ext
    dsimp at hh
    linarith

/-- If one endpoint of an edge is absent from a walk, that edge can meet the
walk only at its other endpoint. -/
lemma edge_walk_trace_intersection {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) {a b c d : V} (h : G.Adj a b) (p : G.Walk c d)
    (ha : a ∉ p.support) :
    D.edge ⟨s(a,b), h⟩ ∩ walkTrace D p ⊆ {D.point b} := by
  induction p with
  | nil =>
    rintro z ⟨hz, hz'⟩
    have heq : z = D.point _ := hz'
    subst z
    rcases (vertex_on_edge D a b _ h).mp hz with he | he
    · subst_vars
      exact False.elim (ha (by simp))
    · exact congrArg D.point he
  | @cons c d e hcd p ih =>
    have hac : a ≠ c := fun hac => ha (by simp [hac])
    have hap : a ∉ p.support := fun hp => ha (List.mem_cons_of_mem _ hp)
    have hef : (⟨s(a,b), h⟩ : G.edgeSet) ≠ ⟨s(c,d), hcd⟩ := by
      intro hef
      have ham : a ∈ (⟨s(a,b), h⟩ : G.edgeSet).val := Sym2.mem_mk_left a b
      rw [hef] at ham
      rcases Sym2.mem_iff.mp ham with h | h
      · exact hac h
      · exact hap (h ▸ p.start_mem_support)
    rintro z ⟨hz, hz'⟩
    rcases hz' with hz' | hz'
    · have hzv : z ∈ D.point '' {v | v ∈ s(a,b) ∧ v ∈ s(c,d)} := by
        rw [← D.edge_intersection _ _ hef]
        exact ⟨hz, hz'⟩
      obtain ⟨v, hv, rfl⟩ := hzv
      rcases Sym2.mem_iff.mp hv.1 with rfl | rfl
      · rcases Sym2.mem_iff.mp hv.2 with h | h
        · exact False.elim (hac h)
        · exact False.elim (hap (h ▸ p.start_mem_support))
      · rfl
    · exact ih hap ⟨hz, hz'⟩

/-- A nonconstant vertex-simple graph path has an embedded interval as its exact
geometric trace. The one-edge base case avoids a constant terminal pause. -/
theorem path_trace_arc {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hab : a ≠ b) :
    IsSimplePolygonalArc (D.point a) (D.point b) (walkTrace D p) := by
  refine ⟨walk_trace_polygonal D p, ?_⟩
  induction p with
  | nil => exact False.elim (hab rfl)
  | @cons a b c h p ih =>
    have hn := List.nodup_cons.mp hp.support_nodup
    have hpp : p.IsPath := (SimpleGraph.Walk.isPath_def p).mpr hn.2
    obtain ⟨_, q, hq, hqr⟩ := D.edge_arc a b h
    cases p with
    | nil =>
      refine ⟨q, hq, ?_⟩
      change Set.range q = D.edge ⟨s(a,b), h⟩ ∪ {D.point b}
      rw [hqr]
      symm
      apply Set.union_eq_left.mpr
      exact Set.singleton_subset_iff.mpr (polygonal_arc_endpoints (D.edge_arc a b h)).2
    | @cons b d c hbd p =>
      have hbc : b ≠ c := by
        intro hbc
        subst c
        exact (List.nodup_cons.mp hpp.support_nodup).1 p.end_mem_support
      obtain ⟨r, hr, hrr⟩ := ih hpp hbc
      refine ⟨q.trans r, path_trans_injective q r hq hr ?_, ?_⟩
      · rw [hqr, hrr]
        exact edge_walk_trace_intersection D h _ hn.1
      · rw [Path.trans_range, hqr, hrr]
        rfl


/-- The concatenation of two arcs with precisely their endpoints in common is
injective before the closing parameter. -/
lemma path_loop_injOn {X : Type*} [TopologicalSpace X] {a b : X}
    (p : _root_.Path a b) (q : _root_.Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hi : Set.range p ∩ Set.range q ⊆ {a,b}) :
    Set.InjOn (p.trans q) {t : unitInterval | (t : ℝ) < 1} := by
  have cross (s t : unitInterval) (hst : p s = q t) :
      (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    have hb : p s ∈ ({a,b} : Set X) := hi ⟨⟨s, rfl⟩, ⟨t, hst.symm⟩⟩
    rcases hb with hb | hb
    · exact Or.inl ⟨hp (hb.trans p.source.symm),
        hq (hst.symm.trans (hb.trans q.target.symm))⟩
    · exact Or.inr ⟨hp (hb.trans p.target.symm),
        hq (hst.symm.trans (hb.trans q.source.symm))⟩
  intro s hs' t ht' hst
  change (s : ℝ) < 1 at hs'
  change (t : ℝ) < 1 at ht'
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have hh := congrArg Subtype.val (hp hst)
    apply Subtype.ext
    dsimp at hh
    linarith
  · rcases cross _ _ hst with ⟨hh, hh'⟩ | ⟨hh, hh'⟩ <;>
      have h1 := congrArg Subtype.val hh <;>
      have h2 := congrArg Subtype.val hh' <;>
      apply Subtype.ext <;> dsimp at h1 h2 <;> linarith
  · rcases cross _ _ hst.symm with ⟨hh, hh'⟩ | ⟨hh, hh'⟩ <;>
      have h1 := congrArg Subtype.val hh <;>
      have h2 := congrArg Subtype.val hh' <;>
      apply Subtype.ext <;> dsimp at h1 h2 <;> linarith
  · have hh := congrArg Subtype.val (hq hst)
    apply Subtype.ext
    dsimp at hh
    linarith

/-- Descent of a simple loop to the additive circle, using the actual quotient
of the interval which identifies just its two endpoints. -/
lemma simple_loop_circle {X : Type*} [TopologicalSpace X] [T2Space X]
    {a : X} (p : _root_.Path a a)
    (hp : Set.InjOn p {t : unitInterval | (t : ℝ) < 1}) :
    ∃ e : AddCircle (1 : ℝ) → X,
      Topology.IsEmbedding e ∧ Set.range e = Set.range p := by
  let e := AddCircle.liftIco (1 : ℝ) 0 p.extend
  have he : Continuous e := AddCircle.liftIco_zero_continuous
    (by simp) p.continuous_extend.continuousOn
  have hrepr (x : AddCircle (1 : ℝ)) :
      e x = p ⟨(AddCircle.equivIco (1 : ℝ) 0 x).val, by
        have h := (AddCircle.equivIco (1 : ℝ) 0 x).property
        exact ⟨h.1, by simpa using h.2.le⟩⟩ := by
    apply Path.extend_apply
  have hinj : Function.Injective e := by
    intro x y hxy
    rw [hrepr, hrepr] at hxy
    have hh := hp (by
      change ((AddCircle.equivIco (1 : ℝ) 0 x).val : ℝ) < 1
      simpa using (AddCircle.equivIco (1 : ℝ) 0 x).property.2)
      (by
        change ((AddCircle.equivIco (1 : ℝ) 0 y).val : ℝ) < 1
        simpa using (AddCircle.equivIco (1 : ℝ) 0 y).property.2) hxy
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    exact congrArg (fun t : unitInterval => (t : ℝ)) hh
  refine ⟨e, he.isClosedEmbedding hinj |>.isEmbedding, ?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨_, hrepr x |>.symm⟩
  · rintro z ⟨t, rfl⟩
    by_cases ht : (t : ℝ) < 1
    · refine ⟨((t : ℝ) : AddCircle (1 : ℝ)), ?_⟩
      change AddCircle.liftIco (1 : ℝ) 0 p.extend _ = _
      rw [AddCircle.liftIco_zero_coe_apply ⟨t.property.1, ht⟩]
      exact p.extend_extends' t
    · have ht1 : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
      subst t
      refine ⟨0, ?_⟩
      change AddCircle.liftIco (1 : ℝ) 0 p.extend 0 = p 1
      rw [show (0 : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) from rfl,
        AddCircle.liftIco_zero_coe_apply (by norm_num)]
      simp

/-- The Euclidean unit circle and the standard additive circle are the same
topological model, with all metric norms retained. -/
def euclideanCircleHomeomorph :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ AddCircle (1 : ℝ) :=
  ((Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    (fun x => by
      change x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
        Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
        LinearIsometryEquiv.norm_map])).trans
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm)

/-- Two embedded arcs sharing only their endpoints form an embedded circle. -/
lemma two_arcs_circle {X : Type*} [TopologicalSpace X] [T2Space X] {a b : X}
    (p : _root_.Path a b) (q : _root_.Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hi : Set.range p ∩ Set.range q ⊆ {a,b}) :
    ∃ e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → X,
      Topology.IsEmbedding e ∧ Set.range e = Set.range p ∪ Set.range q := by
  obtain ⟨e, he, hr⟩ := simple_loop_circle (p.trans q) (path_loop_injOn p q hp hq hi)
  refine ⟨e ∘ euclideanCircleHomeomorph, he.comp euclideanCircleHomeomorph.isEmbedding, ?_⟩
  rw [Set.range_comp, euclideanCircleHomeomorph.surjective.range_eq, Set.image_univ,
    hr, Path.trans_range]


/-- Circle parametrization in the plane, before adjoining infinity. -/
theorem plane_closed_trace_circle {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (x : V) {a c : V} (ha : G.Adj x a) (hc : G.Adj x c)
    (p : G.Walk a c) (hac : a ≠ c) (hp : p.IsPath) (hx : x ∉ p.support) :
    ∃ e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → Point,
      Topology.IsEmbedding e ∧ Set.range e = closedTrace D x ha hc p := by
  have hpath : (SimpleGraph.Walk.cons ha p).IsPath := by
    apply (SimpleGraph.Walk.isPath_def _).mpr
    exact List.nodup_cons.mpr ⟨hx, hp.support_nodup⟩
  obtain ⟨_, q, hq, hqr⟩ := path_trace_arc D (SimpleGraph.Walk.cons ha p) hpath hc.ne
  obtain ⟨_, r, hr, hrr⟩ := D.edge_arc x c hc
  have hef : (⟨s(x,a), ha⟩ : G.edgeSet) ≠ ⟨s(x,c), hc⟩ := by
    intro hef
    have ham : a ∈ (⟨s(x,a), ha⟩ : G.edgeSet).val := Sym2.mem_mk_right x a
    rw [hef] at ham
    rcases Sym2.mem_iff.mp ham with ham | ham
    · exact ha.ne ham.symm
    · exact hac ham
  have hi : Set.range q ∩ Set.range r.symm ⊆ {D.point x, D.point c} := by
    rw [hqr, r.symm_range, hrr]
    rintro z ⟨hz, hzr⟩
    rcases hz with hz | hz
    · have hzv : z ∈ D.point '' {v | v ∈ s(x,a) ∧ v ∈ s(x,c)} := by
        rw [← D.edge_intersection _ _ hef]
        exact ⟨hz, hzr⟩
      obtain ⟨v, hv, rfl⟩ := hzv
      rcases Sym2.mem_iff.mp hv.1 with rfl | rfl
      · exact Set.mem_insert _ _
      · rcases Sym2.mem_iff.mp hv.2 with hax | hac'
        · exact False.elim (ha.ne hax.symm)
        · exact False.elim (hac hac')
    · exact Set.mem_insert_of_mem _ (edge_walk_trace_intersection D hc p hx ⟨hzr, hz⟩)
  obtain ⟨e, he, her⟩ := two_arcs_circle q r.symm hq
    (hr.comp unitInterval.symm_involutive.injective) hi
  refine ⟨e, he, ?_⟩
  rw [her, hqr, r.symm_range, hrr]
  rfl

theorem closed_trace_circle : closed_trace_circleType := by
  intro V _ G D x a c ha hc p hac hp hx
  obtain ⟨e, he, her⟩ := plane_closed_trace_circle D x ha hc p hac hp hx
  refine ⟨OnePoint.some ∘ e, OnePoint.isOpenEmbedding_coe.isEmbedding.comp he, ?_⟩
  rw [Set.range_comp, her]
  rfl


/-- Jordan separation for the actual closed trace, including the full common
frontier conclusion in the drawing's compactified-plane model. -/
theorem closed_trace_jordan {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (x : V) {a c : V} (ha : G.Adj x a) (hc : G.Adj x c)
    (p : G.Walk a c) (hac : a ≠ c) (hp : p.IsPath) (hx : x ∉ p.support) :
    Nonempty (ConnectedComponents ((sphereClosedTrace D x ha hc p)ᶜ : Set Sphere) ≃ Fin 2) ∧
    ∀ y ∈ (sphereClosedTrace D x ha hc p)ᶜ,
      frontier (connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ y) =
        sphereClosedTrace D x ha hc p := by
  obtain ⟨e, he, her⟩ := closed_trace_circle D x ha hc p hac hp hx
  let h := sphereHomeomorph
  let f := h ∘ e
  have hf : Topology.IsEmbedding f := h.isEmbedding.comp he
  obtain ⟨⟨E⟩, hfront⟩ := P202.JordanBrouwer.separation 2 (by norm_num) f hf
  have hfr : Set.range f = h '' sphereClosedTrace D x ha hc p := by
    rw [Set.range_comp, her]
  have hcompl : h '' (sphereClosedTrace D x ha hc p)ᶜ = (Set.range f)ᶜ := by
    rw [h.image_compl, hfr]
  let H := (h.image (sphereClosedTrace D x ha hc p)ᶜ).trans (Homeomorph.setCongr hcompl)
  refine ⟨⟨(homeomorphComponentsEquiv H).trans E⟩, ?_⟩
  intro y hy
  apply h.injective.image_injective
  rw [h.image_frontier, h.image_connectedComponentIn hy, hcompl]
  rw [hfront (h y) (hcompl ▸ Set.mem_image_of_mem h hy), hfr]


/-- A polygonal arc contains a nonconstant straight segment starting at its
initial endpoint. Segments away from that endpoint are excluded by finiteness. -/
lemma arc_contains_initial_segment {a b : Point} {S : Set Point}
    (hS : IsSimplePolygonalArc a b S) :
    ∃ y : Point, y ≠ a ∧ segment ℝ a y ⊆ S := by
  classical
  obtain ⟨⟨n, u, v, hpoly⟩, p, hp, hpr⟩ := hS
  let K : Set Point := ⋃ i : {i : Fin n // a ∉ segment ℝ (u i) (v i)},
    segment ℝ (u i.val) (v i.val)
  have hK : _root_.IsClosed K := by
    apply isClosed_iUnion_of_finite
    intro i
    rw [segment_eq_image']
    exact (isCompact_Icc.image (continuous_const.add
      (continuous_id.smul continuous_const))).isClosed
  have haK : a ∉ K := by
    rintro ha
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    exact i.property hi
  have hneigh : p ⁻¹' Kᶜ ∈ nhds (0 : unitInterval) :=
    p.continuous.continuousAt.preimage_mem_nhds
      (hK.isOpen_compl.mem_nhds (by simpa only [p.source, Set.mem_compl_iff] using haK))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hneigh
  let t : unitInterval := ⟨min δ 1 / 2, by
    constructor
    · exact div_nonneg (le_min hδ.le zero_le_one) (by norm_num)
    · have hh := min_le_right δ (1 : ℝ)
      linarith⟩
  have htpos : (0 : ℝ) < t := div_pos (lt_min hδ zero_lt_one) (by norm_num)
  have htδ : dist t (0 : unitInterval) < δ := by
    change dist (min δ 1 / 2 : ℝ) 0 < δ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg htpos.le]
    change min δ 1 / 2 < δ
    have hh := min_le_left δ (1 : ℝ)
    linarith
  have hptK : p t ∉ K := hδsub htδ
  have hpt : p t ∈ S := hpr ▸ Set.mem_range_self t
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hpoly ▸ hpt)
  have hai : a ∈ segment ℝ (u i) (v i) := by
    by_contra hn
    exact hptK (Set.mem_iUnion.mpr ⟨⟨i, hn⟩, hi⟩)
  refine ⟨p t, ?_, ?_⟩
  · intro heq
    have ht := congrArg (fun s : unitInterval => (s : ℝ)) (hp (heq.trans p.source.symm))
    exact (ne_of_gt htpos) ht
  · exact ((convex_segment (u i) (v i)).segment_subset hai hi).trans
      (fun z hz => hpoly ▸ Set.mem_iUnion.mpr ⟨i, hz⟩)

/-- An initial straight segment of an embedded arc contains a whole relative
neighborhood of its endpoint. This follows from connectedness in interval coordinates. -/
lemma initial_segment_neighborhood {a b y : Point} {S : Set Point}
    (hS : IsSimplePolygonalArc a b S) (hya : y ≠ a) (hseg : segment ℝ a y ⊆ S) :
    ∃ ε : ℝ, 0 < ε ∧ S ∩ Metric.ball a ε ⊆ segment ℝ a y := by
  obtain ⟨h, h0, h1⟩ := arc_interval hS
  let g : segment ℝ a y → S := fun z => ⟨z.val, hseg z.property⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  let t : unitInterval := h.symm ⟨y, hseg (right_mem_segment ℝ a y)⟩
  have htne : t ≠ 0 := by
    intro ht
    have heq := congrArg (fun z : S => z.val) (h.apply_symm_apply
      ⟨y, hseg (right_mem_segment ℝ a y)⟩)
    change (h t).val = y at heq
    rw [ht, h0] at heq
    exact hya heq.symm
  have htpos : (0 : unitInterval) < t := lt_of_le_of_ne (unitInterval.nonneg t) htne.symm
  have hc : IsPreconnected (Set.range (h.symm ∘ g)) := by
    haveI : PreconnectedSpace (segment ℝ a y) :=
      isPreconnected_iff_preconnectedSpace.mp (convex_segment a y).isPreconnected
    exact isPreconnected_range (h.symm.continuous.comp hg)
  have hzero : (0 : unitInterval) ∈ Set.range (h.symm ∘ g) := by
    refine ⟨⟨a, left_mem_segment ℝ a y⟩, ?_⟩
    change h.symm ⟨a, _⟩ = 0
    apply h.injective
    rw [h.apply_symm_apply]
    exact Subtype.ext h0.symm
  have htmem : t ∈ Set.range (h.symm ∘ g) :=
    ⟨⟨y, right_mem_segment ℝ a y⟩, rfl⟩
  have hinit (r : unitInterval) (hrt : r ≤ t) : (h r).val ∈ segment ℝ a y := by
    obtain ⟨z, hz⟩ := hc.Icc_subset hzero htmem ⟨unitInterval.nonneg r, hrt⟩
    have heq : g z = h r := by
      apply h.symm.injective
      exact hz.trans (h.symm_apply_apply r).symm
    exact (congrArg Subtype.val heq) ▸ z.property
  have hW : h.symm ⁻¹' Set.Iio t ∈ nhds (h 0) :=
    (isOpen_Iio.preimage h.symm.continuous).mem_nhds (by simpa using htpos)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨ε, hε, ?_⟩
  rintro z ⟨hz, hzb⟩
  let zS : S := ⟨z, hz⟩
  have hzd : zS ∈ Metric.ball (h 0) ε := by
    change dist z (h 0).val < ε
    rw [h0]
    exact hzb
  have hzt : h.symm zS < t := hεsub hzd
  have hzseg := hinit (h.symm zS) hzt.le
  simpa only [h.apply_symm_apply] using hzseg

/-- A straight segment agrees near its first endpoint with its extending ray. -/
lemma segment_ray_ball {a y : Point} (hya : y ≠ a) {ε : ℝ}
    (hε : ε ≤ ‖y - a‖) :
    segment ℝ a y ∩ Metric.ball a ε = rayFrom a (y - a) ∩ Metric.ball a ε := by
  ext z
  constructor
  · rintro ⟨hz, hzb⟩
    rw [segment_eq_image'] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨⟨t, ht.1, rfl⟩, hzb⟩
  · rintro ⟨⟨t, ht, rfl⟩, hzb⟩
    refine ⟨?_, hzb⟩
    rw [segment_eq_image']
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    have hnorm : 0 < ‖y - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hya)
    have hb : t * ‖y - a‖ < ε := by
      have hh := Metric.mem_ball.mp hzb
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht] at hh
      exact hh
    nlinarith

theorem initial_direction_exists : initial_direction_existsType := by
  intro V _ G D x y h
  have hS := D.edge_arc x y h
  obtain ⟨z, hz, hseg⟩ := arc_contains_initial_segment hS
  obtain ⟨ε, hε, hlocal⟩ := initial_segment_neighborhood hS hz hseg
  refine ⟨z - D.point x, sub_ne_zero.mpr hz, min ε ‖z - D.point x‖,
    lt_min hε (norm_pos_iff.mpr (sub_ne_zero.mpr hz)), ?_⟩
  rw [← segment_ray_ball hz (min_le_right _ _)]
  apply Set.Subset.antisymm
  · rintro w ⟨hw, hwb⟩
    exact ⟨hlocal ⟨hw, Metric.ball_subset_ball (min_le_left _ _) hwb⟩, hwb⟩
  · rintro w ⟨hw, hwb⟩
    exact ⟨hseg hw, hwb⟩

end FiniteCombinatorics.Graph.Plane

section
open Set Complex
open scoped Real
namespace FiniteCombinatorics.Graph.Plane.PolygonalSectors

def polar (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)

def sector (R α β : ℝ) : Set ℂ := polar '' (Ioo 0 R ×ˢ Ioo α β)

def ray (a : ℂ) : Set ℂ := {z | ∃ t : ℝ, 0 ≤ t ∧ z = t * a}

lemma continuous_polar : Continuous polar := by
  unfold polar
  fun_prop

lemma sector_preconnected (R α β : ℝ) : IsPreconnected (sector R α β) := by
  exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ continuous_polar.continuousOn

lemma norm_polar {ρ θ : ℝ} (hρ : 0 ≤ ρ) : ‖polar (ρ, θ)‖ = ρ := by
  simp [polar, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hρ]

lemma polar_angle_injective {α θ φ ρ σ : ℝ}
    (hθ : θ ∈ Ico α (α + 2 * Real.pi))
    (hφ : φ ∈ Ico α (α + 2 * Real.pi))
    (hρ : 0 < ρ) (hσ : 0 < σ)
    (heq : polar (ρ, θ) = polar (σ, φ)) : θ = φ := by
  have hn : ρ = σ := by
    simpa only [norm_polar hρ.le, norm_polar hσ.le] using congrArg norm heq
  subst σ
  have he : Complex.exp (θ * Complex.I) = Complex.exp (φ * Complex.I) := by
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hρ.ne')
    exact heq
  apply Circle.exp_injOn_Ico (a := α) (b := α + 2 * Real.pi) (by linarith) hθ hφ
  exact Subtype.ext he

lemma polar_not_ray {α θ φ ρ : ℝ} {a : ℂ}
    (ha : a ≠ 0) (harg : a.arg = φ)
    (hθ : θ ∈ Ico α (α + 2 * Real.pi))
    (hφ : φ ∈ Ico α (α + 2 * Real.pi))
    (hne : θ ≠ φ) (hρ : 0 < ρ) : polar (ρ, θ) ∉ ray a := by
  rintro ⟨t, ht, he⟩
  have hp : polar (ρ, θ) ≠ 0 := by
    intro hz
    have := norm_polar (θ := θ) hρ.le
    simp [hz] at this
    linarith
  have ht' : 0 < t := lt_of_le_of_ne ht (by intro h; apply hp; simp [h.symm] at he; exact he)
  have hr : 0 < t * ‖a‖ := mul_pos ht' (norm_pos_iff.mpr ha)
  have he' : polar (ρ, θ) = polar (t * ‖a‖, φ) := by
    rw [he]
    simp only [polar, ← harg, Complex.ofReal_mul, mul_assoc, Complex.norm_mul_exp_arg_mul_I]
  exact hne (polar_angle_injective hθ hφ hρ hr he')
end FiniteCombinatorics.Graph.Plane.PolygonalSectors
namespace FiniteCombinatorics.Graph.Plane.PolygonalSectors

lemma mem_ray_of_arg_eq {a z : ℂ} (ha : a ≠ 0) (harg : z.arg = a.arg) :
    z ∈ ray a := by
  refine ⟨‖z‖ / ‖a‖, div_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  calc
    z = (‖z‖ : ℂ) * Complex.exp (a.arg * Complex.I) := by
      rw [← harg, Complex.norm_mul_exp_arg_mul_I]
    _ = (‖z‖ / ‖a‖ : ℝ) * a := by
      calc
        _ = (‖z‖ / ‖a‖ : ℝ) * ((‖a‖ : ℂ) * Complex.exp (a.arg * Complex.I)) := by
          rw [Complex.ofReal_div, ← mul_assoc, div_mul_cancel₀ _
            (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha))]
        _ = _ := by rw [Complex.norm_mul_exp_arg_mul_I]

lemma polar_periodic (ρ θ : ℝ) : polar (ρ, θ + 2 * Real.pi) = polar (ρ, θ) := by
  have he : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      Complex.exp (θ * Complex.I) := congrArg Subtype.val (Circle.exp_add_two_pi θ)
  simp only [polar, he]

lemma sector_subset {R α γ lo hi : ℝ} {a c : ℂ}
    (ha : a ≠ 0) (hc : c ≠ 0) (hα : a.arg = α) (hγ : c.arg = γ)
    (hγJ : γ ∈ Ico α (α + 2 * Real.pi))
    (hθ : ∀ θ ∈ Ioo lo hi, θ ∈ Ico α (α + 2 * Real.pi) ∧ θ ≠ α ∧ θ ≠ γ) :
    sector R lo hi ⊆ Metric.ball 0 R \ (ray a ∪ ray c) := by
  rintro z ⟨⟨ρ, θ⟩, ⟨hρ, ht⟩, rfl⟩
  obtain ⟨hJ, hna, hnc⟩ := hθ θ ht
  refine ⟨?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_zero_right, norm_polar hρ.1.le] using hρ.2
  · rintro (hz | hz)
    · exact polar_not_ray ha hα hJ ⟨le_rfl, by linarith [Real.pi_pos]⟩ hna hρ.1 hz
    · exact polar_not_ray hc hγ hJ hγJ hnc hρ.1 hz
end FiniteCombinatorics.Graph.Plane.PolygonalSectors
namespace FiniteCombinatorics.Graph.Plane.PolygonalSectors

lemma arg_lt_arg_add_two_pi (a z : ℂ) : z.arg < a.arg + 2 * Real.pi := by
  linarith [Complex.neg_pi_lt_arg a, Complex.arg_le_pi z]

lemma mem_sector_of_arg {R α β : ℝ} {z : ℂ} (hz : z ≠ 0)
    (hR : ‖z‖ < R) (hθ : z.arg ∈ Ioo α β) : z ∈ sector R α β := by
  refine ⟨(‖z‖, z.arg), ⟨⟨norm_pos_iff.mpr hz, hR⟩, hθ⟩, ?_⟩
  simpa only [polar] using Complex.norm_mul_exp_arg_mul_I z

lemma mem_sector_of_arg_shift {R α β : ℝ} {z : ℂ} (hz : z ≠ 0)
    (hR : ‖z‖ < R) (hθ : z.arg + 2 * Real.pi ∈ Ioo α β) :
    z ∈ sector R α β := by
  refine ⟨(‖z‖, z.arg + 2 * Real.pi), ⟨⟨norm_pos_iff.mpr hz, hR⟩, hθ⟩, ?_⟩
  rw [polar_periodic]
  simpa only [polar] using Complex.norm_mul_exp_arg_mul_I z

lemma sector_cover {R : ℝ} {a c : ℂ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hac : a.arg < c.arg) :
    Metric.ball 0 R \ (ray a ∪ ray c) ⊆
      sector R a.arg c.arg ∪ sector R c.arg (a.arg + 2 * Real.pi) := by
  intro z hz
  have hza : z ∉ ray a := fun h => hz.2 (Or.inl h)
  have hzc : z ∉ ray c := fun h => hz.2 (Or.inr h)
  have hz0 : z ≠ 0 := by
    intro h
    apply hza
    exact ⟨0, le_rfl, by simp [h]⟩
  have hR : ‖z‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hz.1
  have harg_a : z.arg ≠ a.arg := fun h => hza (mem_ray_of_arg_eq ha h)
  have harg_c : z.arg ≠ c.arg := fun h => hzc (mem_ray_of_arg_eq hc h)
  by_cases hza' : a.arg < z.arg
  · by_cases hzc' : z.arg < c.arg
    · exact Or.inl (mem_sector_of_arg hz0 hR ⟨hza', hzc'⟩)
    · exact Or.inr (mem_sector_of_arg hz0 hR
        ⟨lt_of_le_of_ne (le_of_not_gt hzc') harg_c.symm, arg_lt_arg_add_two_pi a z⟩)
  · apply Or.inr
    apply mem_sector_of_arg_shift hz0 hR
    constructor
    · linarith [arg_lt_arg_add_two_pi z c]
    · linarith [lt_of_le_of_ne (le_of_not_gt hza') harg_a]

lemma sector_pair_subsets {R : ℝ} {a c : ℂ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hac : a.arg < c.arg) :
    sector R a.arg c.arg ⊆ Metric.ball 0 R \ (ray a ∪ ray c) ∧
    sector R c.arg (a.arg + 2 * Real.pi) ⊆ Metric.ball 0 R \ (ray a ∪ ray c) := by
  have hcJ : c.arg ∈ Ico a.arg (a.arg + 2 * Real.pi) :=
    ⟨hac.le, arg_lt_arg_add_two_pi a c⟩
  constructor
  · exact sector_subset ha hc rfl rfl hcJ (by
      intro θ hθ
      refine ⟨⟨hθ.1.le, lt_trans hθ.2 hcJ.2⟩, ?_, ?_⟩ <;> linarith [hθ.1, hθ.2])
  · exact sector_subset ha hc rfl rfl hcJ (by
      intro θ hθ
      refine ⟨⟨le_trans hac.le hθ.1.le, hθ.2⟩, ?_, ?_⟩ <;> linarith [hθ.1])

lemma scalar_mem_sector {R α β t : ℝ} {z : ℂ} (hz : z ≠ 0)
    (ht : 0 < t) (htR : t * ‖z‖ < R) (harg : z.arg ∈ Ioo α β) :
    (t : ℂ) * z ∈ sector R α β := by
  refine ⟨(t * ‖z‖, z.arg), ⟨⟨mul_pos ht (norm_pos_iff.mpr hz), htR⟩, harg⟩, ?_⟩
  simp only [polar, Complex.ofReal_mul, mul_assoc, Complex.norm_mul_exp_arg_mul_I]

lemma alternating_sectors {R : ℝ} {a b c d : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a.arg < b.arg) (hbc : b.arg < c.arg) (hcd : c.arg < d.arg) :
    ∃ A B : Set ℂ, IsPreconnected A ∧ IsPreconnected B ∧
      Metric.ball 0 R \ (ray a ∪ ray c) ⊆ A ∪ B ∧
      A ⊆ Metric.ball 0 R \ (ray a ∪ ray c) ∧
      B ⊆ Metric.ball 0 R \ (ray a ∪ ray c) ∧
      (∀ t : ℝ, 0 < t → t * ‖b‖ < R → (t : ℂ) * b ∈ A) ∧
      (∀ t : ℝ, 0 < t → t * ‖d‖ < R → (t : ℂ) * d ∈ B) := by
  refine ⟨sector R a.arg c.arg, sector R c.arg (a.arg + 2 * Real.pi),
    sector_preconnected _ _ _, sector_preconnected _ _ _,
    sector_cover ha hc (lt_trans hab hbc), ?_, ?_, ?_, ?_⟩
  · exact (sector_pair_subsets ha hc (lt_trans hab hbc)).1
  · exact (sector_pair_subsets ha hc (lt_trans hab hbc)).2
  · intro t ht htR
    exact scalar_mem_sector hb ht htR ⟨hab, hbc⟩
  · intro t ht htR
    exact scalar_mem_sector hd ht htR ⟨hcd, arg_lt_arg_add_two_pi a d⟩

end FiniteCombinatorics.Graph.Plane.PolygonalSectors
namespace FiniteCombinatorics.Graph.Plane.PolygonalSectors

/-- Two sectors in any open coordinate chart, using the actual local curve equation. -/
lemma chart_alternating_sectors {X : Type*} [TopologicalSpace X]
    (e : ℂ → X) (he : Topology.IsOpenEmbedding e) {R : ℝ} (hR : 0 < R)
    (K : Set X) {a b c d : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a.arg < b.arg) (hbc : b.arg < c.arg) (hcd : c.arg < d.arg)
    (hK : ∀ z ∈ Metric.ball (0 : ℂ) R, e z ∈ K ↔ z ∈ ray a ∪ ray c) :
    ∃ U A B : Set X, _root_.IsOpen U ∧ e 0 ∈ U ∧ U ∩ Kᶜ ⊆ A ∪ B ∧
      A ⊆ Kᶜ ∧ B ⊆ Kᶜ ∧ IsPreconnected A ∧ IsPreconnected B ∧
      (∀ t : ℝ, 0 < t → t * ‖b‖ < R → e ((t : ℂ) * b) ∈ A) ∧
      (∀ t : ℝ, 0 < t → t * ‖d‖ < R → e ((t : ℂ) * d) ∈ B) := by
  obtain ⟨A, B, hAc, hBc, hcover, hA, hB, hbA, hdB⟩ :=
    alternating_sectors (R := R) ha hb hc hd hab hbc hcd
  refine ⟨e '' Metric.ball 0 R, e '' A, e '' B,
    he.isOpenMap _ Metric.isOpen_ball, ?_, ?_, ?_, ?_,
    hAc.image _ he.continuous.continuousOn, hBc.image _ he.continuous.continuousOn,
    ?_, ?_⟩
  · exact ⟨0, by simpa using hR, rfl⟩
  · rintro y ⟨⟨z, hz, rfl⟩, hyK⟩
    have hzK : z ∉ ray a ∪ ray c := fun h => hyK ((hK z hz).2 h)
    obtain hzA | hzB := hcover ⟨hz, hzK⟩
    · exact Or.inl ⟨z, hzA, rfl⟩
    · exact Or.inr ⟨z, hzB, rfl⟩
  · rintro y ⟨z, hz, rfl⟩ hy
    exact (hA hz).2 ((hK z (hA hz).1).1 hy)
  · rintro y ⟨z, hz, rfl⟩ hy
    exact (hB hz).2 ((hK z (hB hz).1).1 hy)
  · intro t ht htR
    exact ⟨(t : ℂ) * b, hbA t ht htR, rfl⟩
  · intro t ht htR
    exact ⟨(t : ℂ) * d, hdB t ht htR, rfl⟩

end FiniteCombinatorics.Graph.Plane.PolygonalSectors

end

namespace FiniteCombinatorics.Graph.Plane
open Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation
/-- Separation rules out every complementary continuous path. -/
theorem kempe_no_complementary_path_of_separation
    (hseparation : kempe_separationType.{u}) : kempe_no_complementary_pathType.{u} := by
  intro V _ G D x a b c d ha hb hc hd p hn hcyc hp hx hbp hdp hj
  apply hseparation D x a b c d ha hb hc hd p hn hcyc hp hx hbp hdp
  obtain ⟨q, hq⟩ := hj
  apply connectedComponentIn_eq
  apply (isPreconnected_range q.continuous).subset_connectedComponentIn
    (show OnePoint.some (D.point b) ∈ Set.range q from ⟨0, q.source⟩)
    (by rintro z ⟨t, rfl⟩; exact hq t)
  exact ⟨1, q.target⟩

/-- The palette obstruction applies to arbitrary walks: shorten only the first
walk, retain its support containment, and keep the whole second walk. -/
theorem alternating_color_paths_of_separation
    (hseparation : kempe_separationType.{u}) : alternating_color_pathsType.{u} := by
  intro V _ G D x a b c d ha hb hc hd color hn hcyc hca hcb hcc hcd
  rintro ⟨⟨p, hpx, hpcol⟩, q, hqx, hqcol⟩
  obtain ⟨p', hp', _, hsub⟩ := walk_to_path G a c p
  have hpcol' : ∀ v ∈ p'.support, color v = 0 ∨ color v = 2 :=
    fun v hv => hpcol v (hsub.subset hv)
  have hpx' : x ∉ p'.support := fun hx => hpx (hsub.subset hx)
  have hbp : b ∉ p'.support := by
    intro h
    rcases hpcol' b h with h | h <;> simp_all
  have hdp : d ∉ p'.support := by
    intro h
    rcases hpcol' d h with h | h <;> simp_all
  have haq : a ∉ q.support := by
    intro h
    rcases hqcol a h with h | h <;> simp_all
  have hcq : c ∉ q.support := by
    intro h
    rcases hqcol c h with h | h <;> simp_all
  have hdisjoint : Disjoint (walkTrace D p') (walkTrace D q) := by
    apply disjoint_walk_traces D p' q
    intro v hvp hvq
    rcases hpcol' v hvp with h0 | h2 <;>
      rcases hqcol v hvq with h1 | h3 <;> simp_all
  have hxa : Disjoint (D.edge ⟨s(x,a), ha⟩) (walkTrace D q) := by
    apply edge_disjoint_walk_trace D q
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hqx
    · exact haq
  have hxc : Disjoint (D.edge ⟨s(x,c), hc⟩) (walkTrace D q) := by
    apply edge_disjoint_walk_trace D q
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hqx
    · exact hcq
  have hclosed : Disjoint (walkTrace D q) (closedTrace D x ha hc p') := by
    exact (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨hxa, hdisjoint⟩, hxc⟩).symm
  have hjoined : JoinedIn (sphereClosedTrace D x ha hc p')ᶜ
      (OnePoint.some (D.point b)) (OnePoint.some (D.point d)) := by
    apply ((walk_trace_joined D q).map OnePoint.continuous_coe.continuousOn).mono
    rintro z ⟨w, hw, rfl⟩ hz
    obtain ⟨w', hw', heq⟩ := hz
    have hw_eq : w' = w := OnePoint.coe_injective heq
    exact Set.disjoint_left.mp hclosed hw (hw_eq ▸ hw')
  exact kempe_no_complementary_path_of_separation hseparation D x a b c d
    ha hb hc hd p' hn hcyc hp' hpx' hbp hdp hjoined

/-- Complex coordinates translated to a chosen point and multiplied by a nonzero scalar. -/
def centeredComplexHomeomorph (c : Point) (r : ℂ) (hr : r ≠ 0) : Point ≃ₜ ℂ :=
  (Homeomorph.addRight (-c)).trans
    (Complex.equivRealProdCLM.symm.toHomeomorph.trans (Homeomorph.mulLeft₀ r hr))

@[simp] theorem centeredComplexHomeomorph_apply (c p : Point) (r : ℂ) (hr : r ≠ 0) :
    centeredComplexHomeomorph c r hr p = r * (⟨p.1 - c.1, p.2 - c.2⟩ : ℂ) := by
  rfl

@[simp] theorem centeredComplexHomeomorph_center (c : Point) (r : ℂ) (hr : r ≠ 0) :
    centeredComplexHomeomorph c r hr c = 0 := by
  rw [centeredComplexHomeomorph_apply]
  have hzero : (⟨c.1 - c.1, c.2 - c.2⟩ : ℂ) = 0 := by
    apply Complex.ext <;> simp
  rw [hzero, mul_zero]

@[simp] theorem centeredComplexHomeomorph_ray (c v : Point) (t : ℝ)
    (r : ℂ) (hr : r ≠ 0) :
    centeredComplexHomeomorph c r hr (c + t • v) =
      (t : ℂ) * (r * (⟨v.1, v.2⟩ : ℂ)) := by
  rw [centeredComplexHomeomorph_apply]
  apply Complex.ext <;> simp <;> ring

@[simp] theorem centeredComplexHomeomorph_mem_ray (c p v : Point)
    (r : ℂ) (hr : r ≠ 0) :
    centeredComplexHomeomorph c r hr p ∈ PolygonalSectors.ray (r * (⟨v.1, v.2⟩ : ℂ)) ↔
      p ∈ rayFrom c v := by
  constructor
  · rintro ⟨t, ht, heq⟩
    refine ⟨t, ht, ?_⟩
    apply (centeredComplexHomeomorph c r hr).injective
    rw [centeredComplexHomeomorph_ray]
    exact heq
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, centeredComplexHomeomorph_ray c v t r hr⟩

@[simp] theorem complex_direction_ne_zero (v : Point) (r : ℂ) (hr : r ≠ 0) :
    r * (⟨v.1, v.2⟩ : ℂ) ≠ 0 ↔ v ≠ 0 := by
  rw [mul_ne_zero_iff, and_iff_right hr]
  have heq : (⟨v.1, v.2⟩ : ℂ) = 0 ↔ v = 0 := by
    constructor
    · intro h
      apply Prod.ext
      · exact congrArg Complex.re h
      · exact congrArg Complex.im h
    · rintro rfl
      rfl
  exact not_congr heq

end FiniteCombinatorics.Graph.Plane

namespace FiniteCombinatorics.Graph.Plane
open Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation

/-- The graph path is away from its omitted vertex; the two incident edges are
therefore the complete local geometry of the closed trace. -/
lemma closed_trace_local_rays {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (x : V) {a c : V} (ha : G.Adj x a) (hc : G.Adj x c)
    (p : G.Walk a c) (hx : x ∉ p.support) {va vc : Point}
    (hva : IsInitialDirection D x a ha va) (hvc : IsInitialDirection D x c hc vc) :
    ∃ ε : ℝ, 0 < ε ∧ closedTrace D x ha hc p ∩ Metric.ball (D.point x) ε =
      (rayFrom (D.point x) va ∪ rayFrom (D.point x) vc) ∩ Metric.ball (D.point x) ε := by
  obtain ⟨εa, hεa, hga⟩ := hva.2
  obtain ⟨εc, hεc, hgc⟩ := hvc.2
  have hxtrace : D.point x ∉ walkTrace D p := fun h => hx ((walk_trace_vertex D p x).mp h)
  have hnhds : (walkTrace D p)ᶜ ∈ nhds (D.point x) :=
    (walk_trace_compact D p).isClosed.isOpen_compl.mem_nhds hxtrace
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨min δ (min εa εc), lt_min hδ (lt_min hεa hεc), ?_⟩
  have hsubδ := Metric.ball_subset_ball (min_le_left δ (min εa εc)) (x := D.point x)
  have hsuba := Metric.ball_subset_ball
    ((min_le_right δ (min εa εc)).trans (min_le_left εa εc)) (x := D.point x)
  have hsubc := Metric.ball_subset_ball
    ((min_le_right δ (min εa εc)).trans (min_le_right εa εc)) (x := D.point x)
  ext z
  constructor
  · rintro ⟨(hz | hz) | hz, hzb⟩
    · exact ⟨Or.inl ((hga ▸ (show z ∈ D.edge ⟨s(x,a), ha⟩ ∩ Metric.ball (D.point x) εa from
        ⟨hz, hsuba hzb⟩)).1), hzb⟩
    · exact False.elim ((hδsub (hsubδ hzb)) hz)
    · exact ⟨Or.inr ((hgc ▸ (show z ∈ D.edge ⟨s(x,c), hc⟩ ∩ Metric.ball (D.point x) εc from
        ⟨hz, hsubc hzb⟩)).1), hzb⟩
  · rintro ⟨hz | hz, hzb⟩
    · exact ⟨Or.inl (Or.inl ((hga.symm ▸
        (show z ∈ rayFrom (D.point x) va ∩ Metric.ball (D.point x) εa from
          ⟨hz, hsuba hzb⟩)).1)), hzb⟩
    · exact ⟨Or.inr ((hgc.symm ▸
        (show z ∈ rayFrom (D.point x) vc ∩ Metric.ball (D.point x) εc from
          ⟨hz, hsubc hzb⟩)).1), hzb⟩

/-- Different incident graph edges meet only at their common vertex. -/
lemma incident_edges_intersection {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) {x a b : V} (ha : G.Adj x a) (hb : G.Adj x b)
    (hab : a ≠ b) : D.edge ⟨s(x,a), ha⟩ ∩ D.edge ⟨s(x,b), hb⟩ ⊆ {D.point x} := by
  have hef : (⟨s(x,a), ha⟩ : G.edgeSet) ≠ ⟨s(x,b), hb⟩ := by
    intro heq
    have hm : a ∈ (⟨s(x,a), ha⟩ : G.edgeSet).val := Sym2.mem_mk_right x a
    rw [heq] at hm
    exact (Sym2.mem_iff.mp hm).elim (fun h => ha.ne h.symm) hab
  rw [D.edge_intersection _ _ hef]
  rintro z ⟨v, hv, rfl⟩
  rcases Sym2.mem_iff.mp hv.1 with rfl | rfl
  · rfl
  · rcases Sym2.mem_iff.mp hv.2 with h | h
    · exact congrArg D.point h
    · exact False.elim (hab h)

/-- The third spoke avoids both closing edges and the intervening walk except
at its initial endpoint, by the drawing incidence axioms alone. -/
lemma spoke_avoids_closed_trace {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) {x a b c : V} (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (p : G.Walk a c) (hba : b ≠ a) (hbc : b ≠ c)
    (hx : x ∉ p.support) (hbpath : b ∉ p.support) :
    ∀ z ∈ D.edge ⟨s(x,b), hb⟩, z ≠ D.point x → z ∉ closedTrace D x ha hc p := by
  have hd : Disjoint (D.edge ⟨s(x,b), hb⟩) (walkTrace D p) := by
    apply edge_disjoint_walk_trace D p
    intro v hv
    exact (Sym2.mem_iff.mp hv).elim (fun h => h ▸ hx) (fun h => h ▸ hbpath)
  intro z hzb hzx hzk
  rcases hzk with (hza | hzp) | hzc
  · exact hzx (incident_edges_intersection D hb ha hba ⟨hzb, hza⟩)
  · exact Set.disjoint_left.mp hd hzb hzp
  · exact hzx (incident_edges_intersection D hb hc hbc ⟨hzb, hzc⟩)

lemma ray_point_near {x v : Point} (hv : v ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ rayFrom x v, z ≠ x ∧ z ∈ Metric.ball x ε := by
  let t : ℝ := ε / (2 * (‖v‖ + 1))
  have hd : 0 < 2 * (‖v‖ + 1) := by positivity
  have ht : 0 < t := div_pos hε hd
  have hnorm : t * ‖v‖ < ε := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).mpr
    nlinarith [norm_nonneg v]
  refine ⟨x + t • v, ⟨t, ht.le, rfl⟩, ?_, ?_⟩
  · intro heq
    have hz : t • v = 0 := (add_right_inj x).mp (heq.trans (add_zero x).symm)
    exact (smul_ne_zero ht.ne' hv) hz
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg ht.le]
    exact hnorm

/-- Any chosen initial direction has points arbitrarily near the vertex that
lie on the spoke and propagate in the sphere complement to the other endpoint. -/
lemma spoke_complement_point_near {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) {x a b c : V} (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (p : G.Walk a c) (hba : b ≠ a) (hbc : b ≠ c)
    (hx : x ∉ p.support) (hbpath : b ∉ p.support) {vb : Point}
    (hvb : IsInitialDirection D x b hb vb) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ rayFrom (D.point x) vb, z ≠ D.point x ∧ z ∈ Metric.ball (D.point x) ε ∧
      OnePoint.some z ∉ sphereClosedTrace D x ha hc p ∧
      connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ (OnePoint.some z) =
        connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ (OnePoint.some (D.point b)) := by
  obtain ⟨δ, hδ, hlocal⟩ := hvb.2
  obtain ⟨z, hzray, hzx, hzb⟩ := ray_point_near hvb.1 (lt_min hε hδ)
  have hzedge : z ∈ D.edge ⟨s(x,b), hb⟩ := by
    exact (hlocal.symm ▸ (show z ∈ rayFrom (D.point x) vb ∩ Metric.ball (D.point x) δ from
      ⟨hzray, Metric.ball_subset_ball (min_le_right ε δ) hzb⟩)).1
  obtain ⟨_, q, hq, hqr⟩ := D.edge_arc x b hb
  obtain ⟨t, hqt⟩ := hqr.symm ▸ hzedge
  have ht : t ≠ 0 := by
    intro ht
    exact hzx (hqt.symm.trans (ht ▸ q.source))
  have havoid : ∀ t : unitInterval, t ≠ 0 → q t ∉ closedTrace D x ha hc p := by
    intro t ht
    apply spoke_avoids_closed_trace D ha hb hc p hba hbc hx hbpath
      (q t) (hqr ▸ Set.mem_range_self t)
    intro htx
    exact ht (hq (htx.trans q.source.symm))
  let r : _root_.Path (OnePoint.some (D.point x) : Sphere) (OnePoint.some (D.point b)) :=
    q.map OnePoint.continuous_coe
  have hravoid : ∀ t : unitInterval, t ≠ 0 → r t ∉ sphereClosedTrace D x ha hc p := by
    intro t ht hmem
    obtain ⟨w, hw, heq⟩ := hmem
    have heqw : w = q t := OnePoint.coe_injective heq
    exact havoid t ht (heqw ▸ hw)
  refine ⟨z, hzray, hzx, Metric.ball_subset_ball (min_le_left ε δ) hzb, ?_, ?_⟩
  · have hh := hravoid t ht
    simpa only [r, Path.map_coe, Function.comp_apply, hqt] using hh
  · have hh := punctured_path_component r (sphereClosedTrace D x ha hc p) hravoid t ht
    simpa only [r, Path.map_coe, Function.comp_apply, hqt] using hh

end FiniteCombinatorics.Graph.Plane

namespace FiniteCombinatorics.Graph.Plane
open Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation

/-- In centered complex coordinates, the actual closed trace agrees with its
two initial rays in a small complex disk. -/
lemma closed_trace_local_complex_rays {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (x : V) {a c : V} (ha : G.Adj x a) (hc : G.Adj x c)
    (p : G.Walk a c) (hx : x ∉ p.support) {va vc : Point}
    (hva : IsInitialDirection D x a ha va) (hvc : IsInitialDirection D x c hc vc)
    (r : ℂ) (hr : r ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ Metric.ball (0 : ℂ) R,
      (centeredComplexHomeomorph (D.point x) r hr).symm z ∈ closedTrace D x ha hc p ↔
        z ∈ PolygonalSectors.ray (r * (⟨va.1, va.2⟩ : ℂ)) ∪
          PolygonalSectors.ray (r * (⟨vc.1, vc.2⟩ : ℂ)) := by
  let h := centeredComplexHomeomorph (D.point x) r hr
  have hcenter : h.symm 0 = D.point x := by
    apply h.injective
    rw [h.apply_symm_apply]
    exact (centeredComplexHomeomorph_center _ _ _).symm
  obtain ⟨ε, hε, hlocal⟩ := closed_trace_local_rays D x ha hc p hx hva hvc
  have hnhds : h.symm ⁻¹' Metric.ball (D.point x) ε ∈ nhds (0 : ℂ) := by
    apply h.symm.continuous.continuousAt.preimage_mem_nhds
    rw [hcenter]
    exact Metric.ball_mem_nhds _ hε
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨R, hR, ?_⟩
  intro z hz
  have hzb : h.symm z ∈ Metric.ball (D.point x) ε := hRsub hz
  have hm : h.symm z ∈ closedTrace D x ha hc p ↔
      h.symm z ∈ rayFrom (D.point x) va ∪ rayFrom (D.point x) vc := by
    have hh := Set.ext_iff.mp hlocal (h.symm z)
    simpa only [Set.mem_inter_iff, hzb, and_true] using hh
  have hva' := centeredComplexHomeomorph_mem_ray (D.point x) (h.symm z) va r hr
  have hvc' := centeredComplexHomeomorph_mem_ray (D.point x) (h.symm z) vc r hr
  change h (h.symm z) ∈ PolygonalSectors.ray _ ↔ _ at hva'
  change h (h.symm z) ∈ PolygonalSectors.ray _ ↔ _ at hvc'
  rw [h.apply_symm_apply] at hva' hvc'
  exact hm.trans (or_congr hva'.symm hvc'.symm)

/-- The nearby point on a third spoke may be chosen in any centered complex
disk, while preserving its complementary component all the way to its endpoint. -/
lemma spoke_complement_point_complex_near {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) {x a b c : V} (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (p : G.Walk a c) (hba : b ≠ a) (hbc : b ≠ c)
    (hx : x ∉ p.support) (hbpath : b ∉ p.support) {vb : Point}
    (hvb : IsInitialDirection D x b hb vb) (r : ℂ) (hr : r ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ z ∈ rayFrom (D.point x) vb, z ≠ D.point x ∧
      ‖centeredComplexHomeomorph (D.point x) r hr z‖ < R ∧
      OnePoint.some z ∉ sphereClosedTrace D x ha hc p ∧
      connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ (OnePoint.some z) =
        connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ (OnePoint.some (D.point b)) := by
  let h := centeredComplexHomeomorph (D.point x) r hr
  have hnhds : h ⁻¹' Metric.ball (0 : ℂ) R ∈ nhds (D.point x) := by
    apply h.continuous.continuousAt.preimage_mem_nhds
    change Metric.ball 0 R ∈ nhds (centeredComplexHomeomorph (D.point x) r hr (D.point x))
    rw [centeredComplexHomeomorph_center]
    exact Metric.ball_mem_nhds _ hR
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨z, hzray, hzx, hzball, hzavoid, hzcomp⟩ :=
    spoke_complement_point_near D ha hb hc p hba hbc hx hbpath hvb hε
  refine ⟨z, hzray, hzx, ?_, hzavoid, hzcomp⟩
  have hh : h z ∈ Metric.ball 0 R := hεsub hzball
  simpa only [Metric.mem_ball, dist_zero_right] using hh

/-- Choose a point in a centered chart while retaining the endpoint component. -/
lemma spoke_complement_point_chart {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) {x a b c : V} (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (p : G.Walk a c) (hba : b ≠ a) (hbc : b ≠ c)
    (hx : x ∉ p.support) (hbpath : b ∉ p.support) {vb : Point}
    (hvb : IsInitialDirection D x b hb vb) (r : ℂ) (hr : r ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ z ∈ rayFrom (D.point x) vb, z ≠ D.point x ∧
      ‖centeredComplexHomeomorph (D.point x) r hr z‖ < R ∧
      connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ (OnePoint.some z) =
        connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ (OnePoint.some (D.point b)) := by
  obtain ⟨z, hzray, hzx, hznorm, _, hzcomp⟩ :=
    spoke_complement_point_complex_near D ha hb hc p hba hbc hx hbpath hvb r hr hR
  exact ⟨z, hzray, hzx, hznorm, hzcomp⟩

end FiniteCombinatorics.Graph.Plane

namespace FiniteCombinatorics.Graph.Plane
open Set
open Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation

lemma exists_distinct_components {X : Type*} [TopologicalSpace X] (S : Set X)
    (h : Nonempty (ConnectedComponents S ≃ Fin 2)) :
    ∃ p ∈ S, ∃ q ∈ S, connectedComponentIn S p ≠ connectedComponentIn S q := by
  obtain ⟨e⟩ := h
  obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe (e.symm 0)
  obtain ⟨q, hq⟩ := ConnectedComponents.surjective_coe (e.symm 1)
  refine ⟨p.val, p.property, q.val, q.property, ?_⟩
  intro heq
  have hm : q.val ∈ connectedComponentIn S p.val := heq ▸ mem_connectedComponentIn q.property
  rw [connectedComponentIn_eq_image p.property] at hm
  obtain ⟨z, hz, hze⟩ := hm
  have hzq : z = q := Subtype.ext hze
  subst z
  have hpq : ConnectedComponents.mk q = ConnectedComponents.mk p :=
    ConnectedComponents.coe_eq_coe'.mpr hz
  have he01 : (0 : Fin 2) = 1 := by
    apply e.symm.injective
    exact hp.symm.trans (hpq.symm.trans hq)
  exact (by decide : (0 : Fin 2) ≠ 1) he01

/-- Jordan's two components and common boundary force two connected local
sectors into different components. -/
lemma jordan_local_sectors {X : Type} [TopologicalSpace X]
    (K U A B : Set X) (x a b : X)
    (hU : _root_.IsOpen U) (hxU : x ∈ U) (hxK : x ∈ K)
    (hcover : U ∩ Kᶜ ⊆ A ∪ B) (hA : A ⊆ Kᶜ) (hB : B ⊆ Kᶜ)
    (hcA : IsPreconnected A) (hcB : IsPreconnected B) (ha : a ∈ A) (hb : b ∈ B)
    (htwo : Nonempty (ConnectedComponents (Kᶜ : Set X) ≃ Fin 2))
    (hfront : ∀ y ∈ Kᶜ, frontier (connectedComponentIn Kᶜ y) = K) :
    connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b := by
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_distinct_components Kᶜ htwo
  exact local_sectors_distinct Kᶜ U A B x a b p q hU hxU hcover hA hB hcA hcB ha hb
    (frontier_subset_closure ((hfront p hp).symm ▸ hxK))
    (frontier_subset_closure ((hfront q hq).symm ▸ hxK)) hpq

end FiniteCombinatorics.Graph.Plane

namespace FiniteCombinatorics.Graph.Plane
open Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation

lemma ray_chart_membership (c v z : Point) (r : ℂ) (hr : r ≠ 0)
    {R : ℝ} (A : Set Sphere)
    (hA : ∀ t : ℝ, 0 < t → t * ‖r * (⟨v.1,v.2⟩ : ℂ)‖ < R →
      OnePoint.some ((centeredComplexHomeomorph c r hr).symm
        ((t : ℂ) * (r * (⟨v.1,v.2⟩ : ℂ)))) ∈ A)
    (hz : z ∈ rayFrom c v) (hzne : z ≠ c)
    (hzR : ‖centeredComplexHomeomorph c r hr z‖ < R) : OnePoint.some z ∈ A := by
  obtain ⟨t, ht, rfl⟩ := hz
  have htpos : 0 < t := lt_of_le_of_ne ht (by
    intro ht0
    exact hzne (by simp [ht0.symm]))
  have htR : t * ‖r * (⟨v.1,v.2⟩ : ℂ)‖ < R := by
    rw [centeredComplexHomeomorph_ray, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht] at hzR
    exact hzR
  have hh := hA t htpos htR
  rw [← centeredComplexHomeomorph_ray c v t r hr,
    (centeredComplexHomeomorph c r hr).symm_apply_apply] at hh
  exact hh

/-- The geometric cyclic order puts the two other spokes in different global
components of the actual closed curve. -/
lemma kempe_separation_ordered {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (x a b c d : V) (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (hd : G.Adj x d) (p : G.Walk a c)
    (hac : a ≠ c) (hba : b ≠ a) (hbc : b ≠ c) (hda : d ≠ a) (hdc : d ≠ c)
    {va vb vc vd : Point}
    (hva : IsInitialDirection D x a ha va) (hvb : IsInitialDirection D x b hb vb)
    (hvc : IsInitialDirection D x c hc vc) (hvd : IsInitialDirection D x d hd vd)
    (hcyc : CyclicDirections va vb vc vd)
    (hp : p.IsPath) (hx : x ∉ p.support) (hbp : b ∉ p.support) (hdp : d ∉ p.support) :
    connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ (OnePoint.some (D.point b)) ≠
      connectedComponentIn (sphereClosedTrace D x ha hc p)ᶜ (OnePoint.some (D.point d)) := by
  obtain ⟨r, hr, hab, hbc', hcd⟩ := hcyc
  let h := centeredComplexHomeomorph (D.point x) r hr
  let e : ℂ → Sphere := OnePoint.some ∘ h.symm
  let K := sphereClosedTrace D x ha hc p
  obtain ⟨R, hR, hlocal⟩ := closed_trace_local_complex_rays D x ha hc p hx hva hvc r hr
  have he : Topology.IsOpenEmbedding e :=
    OnePoint.isOpenEmbedding_coe.comp h.symm.isOpenEmbedding
  have heK : ∀ z ∈ Metric.ball (0 : ℂ) R, e z ∈ K ↔
      z ∈ PolygonalSectors.ray (r * (⟨va.1,va.2⟩ : ℂ)) ∪
        PolygonalSectors.ray (r * (⟨vc.1,vc.2⟩ : ℂ)) := by
    intro z hz
    change OnePoint.some (h.symm z) ∈ sphereClosedTrace D x ha hc p ↔ _
    have hm : OnePoint.some (h.symm z) ∈ sphereClosedTrace D x ha hc p ↔
        h.symm z ∈ closedTrace D x ha hc p := by
      constructor
      · rintro ⟨w, hw, heq⟩
        exact OnePoint.coe_injective heq ▸ hw
      · intro hw
        exact ⟨h.symm z, hw, rfl⟩
    exact hm.trans (hlocal z hz)
  obtain ⟨U, A, B, hU, h0U, hcover, hA, hB, hcA, hcB, hbA, hdB⟩ :=
    PolygonalSectors.chart_alternating_sectors e he hR K
      ((complex_direction_ne_zero va r hr).mpr hva.1)
      ((complex_direction_ne_zero vb r hr).mpr hvb.1)
      ((complex_direction_ne_zero vc r hr).mpr hvc.1)
      ((complex_direction_ne_zero vd r hr).mpr hvd.1) hab hbc' hcd heK
  obtain ⟨zb, hzbray, hzbne, hzbR, hzbcomp⟩ :=
    spoke_complement_point_chart D ha hb hc p hba hbc hx hbp hvb r hr hR
  obtain ⟨zd, hzdray, hzdne, hzdR, hzdcomp⟩ :=
    spoke_complement_point_chart D ha hd hc p hda hdc hx hdp hvd r hr hR
  have hzbA : OnePoint.some zb ∈ A :=
    ray_chart_membership (D.point x) vb zb r hr A hbA hzbray hzbne hzbR
  have hzdB : OnePoint.some zd ∈ B :=
    ray_chart_membership (D.point x) vd zd r hr B hdB hzdray hzdne hzdR
  have he0 : e 0 = OnePoint.some (D.point x) := by
    change OnePoint.some (h.symm 0) = OnePoint.some (D.point x)
    congr 1
    apply h.injective
    rw [h.apply_symm_apply]
    exact (centeredComplexHomeomorph_center _ _ _).symm
  have hxK : OnePoint.some (D.point x) ∈ K := by
    refine ⟨D.point x, ?_, rfl⟩
    exact (closed_trace_vertex D x ha hc p x).mpr (Or.inl rfl)
  obtain ⟨htwo, hfront⟩ := closed_trace_jordan D x ha hc p hac hp hx
  have hneq := jordan_local_sectors K U A B (OnePoint.some (D.point x))
    (OnePoint.some zb) (OnePoint.some zd) hU (he0 ▸ h0U) hxK
    hcover hA hB hcA hcB hzbA hzdB htwo hfront
  rw [hzbcomp, hzdcomp] at hneq
  exact hneq

theorem kempe_separation : kempe_separationType := by
  intro V _ G D x a b c d ha hb hc hd p hn hcyc hp hx hbp hdp
  have hac : a ≠ c := by rintro rfl; simp at hn
  have hba : b ≠ a := by rintro rfl; simp at hn
  have hbc : b ≠ c := by rintro rfl; simp at hn
  have hda : d ≠ a := by rintro rfl; simp at hn
  have hdc : d ≠ c := by rintro rfl; simp at hn
  obtain ⟨va, vb, vc, vd, hva, hvb, hvc, hvd, horder | horder⟩ := hcyc
  · exact kempe_separation_ordered D x a b c d ha hb hc hd p
      hac hba hbc hda hdc hva hvb hvc hvd horder hp hx hbp hdp
  · exact (kempe_separation_ordered D x a d c b ha hd hc hb p
      hac hda hdc hba hbc hva hvd hvc hvb horder hp hx hdp hbp).symm

theorem kempe_no_complementary_path : kempe_no_complementary_pathType :=
  kempe_no_complementary_path_of_separation kempe_separation

theorem alternating_color_paths : alternating_color_pathsType :=
  alternating_color_paths_of_separation kempe_separation

end FiniteCombinatorics.Graph.Plane

