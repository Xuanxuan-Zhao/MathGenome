import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.MultigraphFoundation

/-! Shared indexed undirected graph interface for edge coloring and graphic matroids.
The actual graph is Mathlib's `Graph α β`; the finite package restricts its real
vertex and edge sets, without requiring finite ambient label types. In particular,
two edges with the same ends remain two elements of β. The simple graph obtained
by `underlying` records only adjacency between distinct real vertices.
-/

universe u v
noncomputable section

namespace FiniteCombinatorics.Graph.Multigraph

abbrev IsFinite : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue

abbrev FiniteIndexedGraph : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.FiniteIndexedGraphType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.FiniteIndexedGraphValue

abbrev Vertex : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.VertexType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.VertexValue

abbrev Edge : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.EdgeType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.EdgeValue

abbrev Incidence : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IncidenceType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IncidenceValue

abbrev incidentEdges : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.incidentEdgesType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.incidentEdgesValue

abbrev loopEdges : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.loopEdgesType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.loopEdgesValue

abbrev degree : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degreeType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degreeValue

abbrev Loopless : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.LooplessType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.LooplessValue

abbrev Simple : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.SimpleType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.SimpleValue

abbrev underlying : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.underlyingType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.underlyingValue

abbrev ofSimpleGraph : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraphType :=
  Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraphValue

theorem finite_vertices : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.finite_verticesType := by
  intro α β G h
  exact h.1.to_subtype

theorem finite_edges : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.finite_edgesType := by
  intro α β G h
  exact h.2.to_subtype

instance finiteIndexedGraphVertex {α : Type u} {β : Type v}
    (G : FiniteIndexedGraph α β) : Finite (Vertex G.val) :=
  finite_vertices G.val G.property

instance finiteIndexedGraphEdge {α : Type u} {β : Type v}
    (G : FiniteIndexedGraph α β) : Finite (Edge G.val) :=
  finite_edges G.val G.property

theorem finite_incidentEdges : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.finite_incidentEdgesType := by
  intro α β G h x
  exact h.2.subset (G.incidenceSet_subset_edgeSet x)

theorem finite_loopEdges : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.finite_loopEdgesType := by
  intro α β G h x
  exact (finite_incidentEdges G h x).subset (G.loopSet_subset_incidenceSet x)

theorem isLink_endpoints : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.isLink_endpointsType := by
  intro α β G e x y h
  exact ⟨h.edge_mem, h.left_mem, h.right_mem⟩

theorem isLink_symmetry : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.isLink_symmetryType := by
  intro α β G e x y
  exact _root_.Graph.isLink_comm

theorem edge_iff_isLink : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.edge_iff_isLinkType := by
  intro α β G e
  exact G.edge_mem_iff_exists_isLink e

theorem incidence_iff : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.incidence_iffType := by
  intro α β G e x
  rfl

theorem incidence_membership : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.incidence_membershipType := by
  intro α β G e x
  rfl

theorem loop_membership : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.loop_membershipType := by
  intro α β G e x
  rfl

theorem degree_formula : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degree_formulaType := by
  intro α β G x
  rfl

/-- Each nonloop incidence contributes one, and each loop contributes two. -/
theorem degree_nonloop_and_loops : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degree_nonloop_and_loopsType := by
  intro α β G h x
  have hs : G.incidenceSet x \ G.loopSet x = {e | G.IsNonloopAt e x} := by
    ext e
    exact (_root_.Graph.isNonloopAt_iff_inc_not_isLoopAt).symm
  have hc := Set.ncard_sdiff_add_ncard_of_subset (G.loopSet_subset_incidenceSet x)
    (finite_incidentEdges G h x)
  rw [hs] at hc
  change Nat.card (G.incidenceSet x) + Nat.card (G.loopSet x) = _
  change Nat.card {e : β // G.IsNonloopAt e x} + Nat.card (G.loopSet x) =
    Nat.card (G.incidenceSet x) at hc
  omega

theorem degree_loopless : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degree_looplessType := by
  intro α β G _ x
  have h : G.loopSet x = ∅ := by ext e; simp [_root_.Graph.mem_loopSet]
  change Nat.card (G.incidenceSet x) + Nat.card (G.loopSet x) = _
  simp [h]

theorem degree_outside : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degree_outsideType := by
  intro α β G x hx
  have hi : G.incidenceSet x = ∅ := by
    ext e
    exact ⟨fun h => (hx h.vertex_mem).elim, fun h => h.elim⟩
  have hl : G.loopSet x = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact fun e h => hx h.vertex_mem
  change Nat.card (G.incidenceSet x) + Nat.card (G.loopSet x) = 0
  simp [hi, hl]

theorem underlying_adjacency : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.underlying_adjacencyType := by
  intro α β G x y
  rfl

theorem underlying_loopless_adjacency : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.underlying_loopless_adjacencyType := by
  intro α β G _ x y
  exact _root_.Graph.toSimpleGraph_adj_iff x y

theorem simple_edge_unique : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.simple_edge_uniqueType := by
  intro α β G _ e f x y h h'
  exact h.eq h'

/-- The bijection sends an incident edge to its other endpoint. -/
theorem simple_incidence_bijection : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.simple_incidence_bijectionType := by
  intro α β G _ x
  let f : G.incidenceSet x.val → (underlying G).neighborSet x := fun e =>
    ⟨⟨e.property.other, e.property.inc_other.vertex_mem⟩,
      (_root_.Graph.toSimpleGraph_adj_iff _ _).mpr ⟨e.val, e.property.isLink_other⟩⟩
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro e e' he
    apply Subtype.ext
    have hval := congrArg (fun z : (underlying G).neighborSet x => z.val.val) he
    change e.property.other = e'.property.other at hval
    exact e.property.isLink_other.eq (hval.symm ▸ e'.property.isLink_other)
  · intro y
    obtain ⟨e, he⟩ := (_root_.Graph.toSimpleGraph_adj_iff x y.val).mp y.property
    refine ⟨⟨e, he.inc_left⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact he.inc_left.isLink_other.right_unique he
  · intro e
    exact e.property.isLink_other

theorem underlying_simple_adjacency : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.underlying_simple_adjacencyType := by
  intro α β G _ x y
  rw [underlying_loopless_adjacency]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, he, fun f hf => hf.eq he⟩
  · rintro ⟨e, he, _⟩
    exact ⟨e, he⟩

theorem degree_simple_underlying : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degree_simple_underlyingType := by
  intro α β G _ x _
  rw [degree_loopless]
  obtain ⟨f, hf, _⟩ := simple_incidence_bijection G x
  exact (Nat.card_eq_of_bijective f hf).trans
    ((Nat.card_eq_fintype_card).trans ((underlying G).card_neighborSet_eq_degree x))

theorem ofSimpleGraph_vertices : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraph_verticesType := by
  intro α G
  rfl

theorem ofSimpleGraph_edges : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraph_edgesType := by
  intro α G
  rfl

theorem ofSimpleGraph_isLink : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraph_isLinkType := by
  intro α G e x y
  change (e = s(x, y) ∧ e ∈ G.edgeSet) ↔ _
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, h⟩

theorem ofSimpleGraph_adjacency : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraph_adjacencyType := by
  intro α G x y
  exact _root_.Graph.ofSimpleGraph_adj_iff x y

theorem ofSimpleGraph_incidence : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraph_incidenceType := by
  intro α G e x
  constructor
  · rintro ⟨y, h⟩
    obtain ⟨rfl, hy⟩ := (ofSimpleGraph_isLink G e x y).mp h
    exact (G.mem_incidenceSet x y).mpr hy
  · intro h
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨hab, hx⟩ := G.mk'_mem_incidenceSet_iff.mp h
      rcases hx with rfl | rfl
      · exact ⟨b, (ofSimpleGraph_isLink G _ _ _).mpr ⟨rfl, hab⟩⟩
      · exact ⟨a, (ofSimpleGraph_isLink G _ _ _).mpr ⟨Sym2.eq_swap, hab.symm⟩⟩

theorem ofSimpleGraph_simple : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraph_simpleType := by
  intro α G
  refine { not_isLoopAt := ?_, eq_of_isLink := ?_ }
  · intro e x h
    exact G.loopless.irrefl x ((ofSimpleGraph_isLink G e x x).mp h).2
  · intro e f x y he hf
    exact ((ofSimpleGraph_isLink G e x y).mp he).1.trans
      ((ofSimpleGraph_isLink G f x y).mp hf).1.symm

instance ofSimpleGraphSimple {α : Type u} (G : SimpleGraph α) :
    (_root_.Graph.ofSimpleGraph G).Simple :=
  ofSimpleGraph_simple G

theorem ofSimpleGraph_finite : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraph_finiteType := by
  intro α _ G
  exact ⟨Set.toFinite _, Set.toFinite _⟩

theorem ofSimpleGraph_iso : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraph_isoType := by
  intro α G
  exact ⟨_root_.Graph.toSimpleGraphOfSimpleGraphIso G⟩

theorem degree_ofSimpleGraph : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degree_ofSimpleGraphType := by
  intro α _ G x
  classical
  rw [degree_loopless]
  have hi : (ofSimpleGraph G).incidenceSet x = G.incidenceSet x := by
    ext e
    exact ofSimpleGraph_incidence G e x
  rw [hi]
  exact Nat.card_congr (G.incidenceSetEquivNeighborSet x)

theorem degree_ofSimpleGraph_mathlib : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degree_ofSimpleGraph_mathlibType := by
  intro α G x _
  classical
  rw [degree_loopless]
  have hi : (ofSimpleGraph G).incidenceSet x = G.incidenceSet x := by
    ext e
    exact ofSimpleGraph_incidence G e x
  rw [hi]
  exact (Nat.card_congr (G.incidenceSetEquivNeighborSet x)).trans
    ((Nat.card_eq_fintype_card).trans (G.card_neighborSet_eq_degree x))

/-- Arbitrarily many distinct indexed edges may have the same two ends. -/
theorem banana_links : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.banana_linksType := by
  intro α β x y s e
  simp [_root_.Graph.banana_isLink]

theorem banana_finite : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.banana_finiteType := by
  intro α β x y s hs
  exact ⟨(Set.finite_singleton y).insert x, hs⟩

theorem banana_degree : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.banana_degreeType := by
  intro α β x y s hxy
  have hi : (_root_.Graph.banana x y s).incidenceSet x = s := by
    ext e
    simp [_root_.Graph.mem_incidenceSet]
  have hl : (_root_.Graph.banana x y s).loopSet x = ∅ := by
    ext e
    simp [_root_.Graph.mem_loopSet, hxy]
  change Nat.card ((_root_.Graph.banana x y s).incidenceSet x) +
    Nat.card ((_root_.Graph.banana x y s).loopSet x) = _
  simp [hi, hl]

theorem loop_banana_degree : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.loop_banana_degreeType := by
  intro α β x s
  have hi : (_root_.Graph.banana x x s).incidenceSet x = s := by
    ext e
    simp [_root_.Graph.mem_incidenceSet]
  have hl : (_root_.Graph.banana x x s).loopSet x = s := by
    ext e
    simp [_root_.Graph.mem_loopSet]
  change Nat.card ((_root_.Graph.banana x x s).incidenceSet x) +
    Nat.card ((_root_.Graph.banana x x s).loopSet x) = _
  rw [hi, hl, two_mul]

end FiniteCombinatorics.Graph.Multigraph
