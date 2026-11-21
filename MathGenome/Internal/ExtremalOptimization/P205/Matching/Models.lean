import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.Models
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Public canonical allowed-edge interface, with exact transports to Mathlib
subgraphs and MathGenome edge matchings. -/
set_option linter.unusedSectionVars false

universe u v
noncomputable section
open scoped BigOperators
namespace P205.Matching

abbrev BipartiteGraph : Specs.P205.Matching.BipartiteGraphType.{u, v} :=
  @Specs.P205.Matching.BipartiteGraph.{u, v}

abbrev Edge : Specs.P205.Matching.EdgeType.{u, v} :=
  @Specs.P205.Matching.Edge.{u, v}

abbrev graph : Specs.P205.Matching.graphType.{u, v} :=
  @Specs.P205.Matching.graph.{u, v}

abbrev incident : Specs.P205.Matching.incidentType.{u, v} :=
  @Specs.P205.Matching.incident.{u, v}

abbrev IsMatching : Specs.P205.Matching.IsMatchingType.{u, v} :=
  @Specs.P205.Matching.IsMatching.{u, v}

abbrev Covered : Specs.P205.Matching.CoveredType.{u, v} :=
  @Specs.P205.Matching.Covered.{u, v}

abbrev IsPerfectMatching : Specs.P205.Matching.IsPerfectMatchingType.{u, v} :=
  @Specs.P205.Matching.IsPerfectMatching.{u, v}

abbrev indicator : Specs.P205.Matching.indicatorType.{u, v} :=
  @Specs.P205.Matching.indicator.{u, v}

abbrev incidence : Specs.P205.Matching.incidenceType.{u, v} :=
  @Specs.P205.Matching.incidence.{u, v}

abbrev degree : Specs.P205.Matching.degreeType.{u, v} :=
  @Specs.P205.Matching.degree.{u, v}

abbrev load : Specs.P205.Matching.loadType.{u, v} :=
  @Specs.P205.Matching.load.{u, v}

abbrev matchingWeight : Specs.P205.Matching.matchingWeightType.{u, v} :=
  @Specs.P205.Matching.matchingWeight.{u, v}

abbrev totalWeight : Specs.P205.Matching.totalWeightType.{u, v} :=
  @Specs.P205.Matching.totalWeight.{u, v}

abbrev potentialSum : Specs.P205.Matching.potentialSumType.{u, v} :=
  @Specs.P205.Matching.potentialSum.{u, v}

abbrev FreeFeasible : Specs.P205.Matching.FreeFeasibleType.{u, v} :=
  @Specs.P205.Matching.FreeFeasible.{u, v}

abbrev NonnegativeFeasible : Specs.P205.Matching.NonnegativeFeasibleType.{u, v} :=
  @Specs.P205.Matching.NonnegativeFeasible.{u, v}

abbrev slack : Specs.P205.Matching.slackType.{u, v} :=
  @Specs.P205.Matching.slack.{u, v}

abbrev Tight : Specs.P205.Matching.TightType.{u, v} :=
  @Specs.P205.Matching.Tight.{u, v}

abbrev UsesTightEdges : Specs.P205.Matching.UsesTightEdgesType.{u, v} :=
  @Specs.P205.Matching.UsesTightEdges.{u, v}

abbrev edgePair : Specs.P205.Matching.edgePairType.{u, v} :=
  @Specs.P205.Matching.edgePair.{u, v}

abbrev edgeSet : Specs.P205.Matching.edgeSetType.{u, v} :=
  @Specs.P205.Matching.edgeSet.{u, v}

abbrev coordinates : Specs.P205.Matching.coordinatesType.{u, v} :=
  @Specs.P205.Matching.coordinates.{u, v}

abbrev subgraph : Specs.P205.Matching.subgraphType.{u, v} :=
  @Specs.P205.Matching.subgraph.{u, v}

variable {L : Type u} {R : Type v} {G : BipartiteGraph L R}

@[simp] theorem graph_adj_lr (i : L) (j : R) :
    (graph G).Adj (.inl i) (.inr j) ↔ G i j := Iff.rfl

@[simp] theorem graph_adj_ll (i k : L) : ¬ (graph G).Adj (.inl i) (.inl k) :=
  id

@[simp] theorem graph_adj_rr (j k : R) : ¬ (graph G).Adj (.inr j) (.inr k) :=
  id

@[simp] theorem edgePair_injective : Function.Injective (@edgePair L R G) := by
  intro e f h
  apply Subtype.ext
  have h' := Sym2.eq_iff.mp h
  have h'' : e.val.1 = f.val.1 ∧ e.val.2 = f.val.2 := by
    simpa [edgePair, Specs.P205.Matching.edgePair] using h'
  exact Prod.ext h''.1 h''.2

@[simp] theorem edgePair_mem_graph (e : Edge G) : edgePair e ∈ (graph G).edgeSet :=
  e.property

/-- Every actual unordered edge has exactly one allowed coordinate. -/
theorem edgePair_range : Set.range (@edgePair L R G) = (graph G).edgeSet := by
  ext d
  induction d using Sym2.ind with
  | _ a b =>
    cases a with
    | inl i =>
      cases b with
      | inl k => simp [edgePair, Specs.P205.Matching.edgePair, graph,
          Specs.P205.Matching.graph]
      | inr j =>
        constructor
        · rintro ⟨e, he⟩; rw [← he]; exact e.property
        · intro h; exact ⟨⟨(i,j), h⟩, rfl⟩
    | inr j =>
      cases b with
      | inl i =>
        constructor
        · rintro ⟨e, he⟩; rw [← he]; exact e.property
        · intro h; exact ⟨⟨(i,j), h⟩, Sym2.eq_swap⟩
      | inr k => simp [edgePair, Specs.P205.Matching.edgePair, graph,
          Specs.P205.Matching.graph]

/-- A bijection, including for an empty allowed-edge set. -/
def edgeEquiv : Edge G ≃ (graph G).edgeSet :=
  Equiv.ofBijective (fun e => ⟨edgePair e, edgePair_mem_graph e⟩) (by
    constructor
    · intro e f h; exact edgePair_injective (congrArg Subtype.val h)
    · rintro ⟨d, hd⟩
      obtain ⟨e, he⟩ := edgePair_range.symm ▸ hd
      exact ⟨e, Subtype.ext he⟩)

@[simp] theorem edgeSet_subset (M : Set (Edge G)) : edgeSet M ⊆ (graph G).edgeSet := by
  rintro d ⟨e, he, rfl⟩; exact edgePair_mem_graph e

@[simp] theorem subgraph_edgeSet (M : Set (Edge G)) : (subgraph M).edgeSet = edgeSet M := by
  ext d
  induction d using Sym2.ind with
  | _ a b =>
    change (∃ e ∈ M, (a = Sum.inl e.val.1 ∧ b = Sum.inr e.val.2) ∨
      (a = Sum.inr e.val.2 ∧ b = Sum.inl e.val.1)) ↔ _
    simp only [edgeSet, Specs.P205.Matching.edgeSet, Set.mem_image,
      Specs.P205.Matching.edgePair, Sym2.eq_iff]
    aesop

@[simp] theorem coordinates_subgraph (M : Set (Edge G)) :
    coordinates (subgraph M) = M := by
  ext e
  change (∃ f ∈ M, (Sum.inl e.val.1 = Sum.inl f.val.1 ∧
    Sum.inr e.val.2 = Sum.inr f.val.2) ∨
    (Sum.inl e.val.1 = Sum.inr f.val.2 ∧ Sum.inr e.val.2 = Sum.inl f.val.1)) ↔ _
  simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, or_false]
  constructor
  · rintro ⟨f, hf, h₁, h₂⟩
    have : e = f := Subtype.ext (Prod.ext h₁ h₂)
    simpa [this] using hf
  · intro he; exact ⟨e, he, rfl, rfl⟩

@[simp] theorem edgeSet_coordinates (H : (graph G).Subgraph) :
    edgeSet (coordinates H) = H.edgeSet := by
  ext d
  constructor
  · rintro ⟨e, he, rfl⟩; exact he
  · intro hd
    obtain ⟨e, he⟩ : d ∈ Set.range (@edgePair L R G) := by
      rw [edgePair_range]; exact H.edgeSet_subset hd
    refine ⟨e, ?_, he⟩
    have hd' : edgePair e ∈ H.edgeSet := he.symm ▸ hd
    exact hd'

variable [Fintype L] [Fintype R]

/-- Endpoint incidence is preserved, including vertices not used by a matching. -/
theorem covered_iff_saturated (M : Set (Edge G)) (v : L ⊕ R) :
    Covered M v ↔ FiniteCombinatorics.Graph.Matching.Saturated (edgeSet M) v := by
  change (∃ e ∈ M, incident v e) ↔ ∃ d ∈ edgeSet M, v ∈ d
  simp only [edgeSet, Specs.P205.Matching.edgeSet, Set.mem_image]
  constructor
  · rintro ⟨e, he, hv⟩
    refine ⟨edgePair e, ⟨e, he, rfl⟩, ?_⟩
    cases v <;> simpa [edgePair, Specs.P205.Matching.edgePair,
      incident, Specs.P205.Matching.incident] using hv
  · rintro ⟨d, ⟨e, he, rfl⟩, hv⟩
    refine ⟨e, he, ?_⟩
    cases v <;> simpa [edgePair, Specs.P205.Matching.edgePair,
      incident, Specs.P205.Matching.incident] using hv

/-- Exact comparison with MathGenome's unordered-edge matching object. -/
theorem matching_iff_mathGenome (M : Set (Edge G)) :
    IsMatching M ↔ FiniteCombinatorics.Graph.Matching.IsMatching (graph G) (edgeSet M) := by
  constructor
  · intro h
    refine ⟨edgeSet_subset M, ?_⟩
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ v hve hvf
    apply congrArg edgePair
    cases v with
    | inl i =>
      have h₁ : i = e.val.1 := by simpa [edgePair, Specs.P205.Matching.edgePair] using hve
      have h₂ : i = f.val.1 := by simpa [edgePair, Specs.P205.Matching.edgePair] using hvf
      exact h.1 e he f hf (h₁.symm.trans h₂)
    | inr j =>
      have h₁ : j = e.val.2 := by simpa [edgePair, Specs.P205.Matching.edgePair] using hve
      have h₂ : j = f.val.2 := by simpa [edgePair, Specs.P205.Matching.edgePair] using hvf
      exact h.2 e he f hf (h₁.symm.trans h₂)
  · intro h
    constructor
    · intro e he f hf heq
      apply edgePair_injective
      exact h.2 _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ (.inl e.val.1)
        (Sym2.mem_mk_left _ _) (by simp [edgePair, Specs.P205.Matching.edgePair, heq])
    · intro e he f hf heq
      apply edgePair_injective
      exact h.2 _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ (.inr e.val.2)
        (Sym2.mem_mk_right _ _) (by simp [edgePair, Specs.P205.Matching.edgePair, heq])

/-- Our subgraph uses precisely the endpoint support required by Mathlib. -/
theorem subgraph_eq_mathGenome (M : Set (Edge G)) :
    subgraph M = FiniteCombinatorics.Graph.Matching.edgeSubgraph
      (graph G) (edgeSet M) (edgeSet_subset M) := by
  apply SimpleGraph.Subgraph.ext
  · ext v; exact covered_iff_saturated M v
  · funext a b
    apply propext
    change (subgraph M).Adj a b ↔ s(a,b) ∈ edgeSet M
    rw [← subgraph_edgeSet]
    rfl

/-- Exact comparison with Mathlib matching subgraphs. -/
theorem matching_iff_mathlib (M : Set (Edge G)) :
    IsMatching M ↔ (subgraph M).IsMatching := by
  rw [subgraph_eq_mathGenome,
    FiniteCombinatorics.Graph.Matching.edgeSubgraph_isMatching]
  exact matching_iff_mathGenome M

theorem perfect_iff_mathGenome (M : Set (Edge G)) :
    IsPerfectMatching M ↔
      FiniteCombinatorics.Graph.Matching.IsPerfectMatching (graph G) (edgeSet M) := by
  change (IsMatching M ∧ ∀ v, Covered M v) ↔ _
  simp only [matching_iff_mathGenome, covered_iff_saturated]
  rfl

theorem perfect_iff_mathlib (M : Set (Edge G)) :
    IsPerfectMatching M ↔ (subgraph M).IsPerfectMatching := by
  rw [FiniteCombinatorics.Graph.Matching.perfect_subgraph_iff, subgraph_edgeSet]
  exact perfect_iff_mathGenome M

/-- Any Mathlib matching is recovered with its actual vertex and edge sets. -/
theorem subgraph_coordinates {H : (graph G).Subgraph} (h : H.IsMatching) :
    subgraph (coordinates H) = H := by
  have hs := (FiniteCombinatorics.Graph.Matching.matching_subgraph_iff _ H).mp h
  rw [subgraph_eq_mathGenome]
  apply SimpleGraph.Subgraph.ext
  · rw [hs.2]
    simp only [FiniteCombinatorics.Graph.Matching.edgeSubgraph,
      Specs.FiniteCombinatorics.Graph.Matching.Foundations.edgeSubgraphValue,
      edgeSet_coordinates]
  · funext a b
    apply propext
    change s(a,b) ∈ edgeSet (coordinates H) ↔ H.Adj a b
    rw [edgeSet_coordinates]
    rfl

/-- Finite representation transport for all Mathlib matching subgraphs. -/
def matchingEquiv : {M : Set (Edge G) // IsMatching M} ≃
    {H : (graph G).Subgraph // H.IsMatching} where
  toFun M := ⟨subgraph M.val, (matching_iff_mathlib M.val).mp M.property⟩
  invFun H := ⟨coordinates H.val, (matching_iff_mathlib _).mpr (by
    rw [subgraph_coordinates H.property]; exact H.property)⟩
  left_inv M := Subtype.ext (coordinates_subgraph M.val)
  right_inv H := Subtype.ext (subgraph_coordinates H.property)

/-- The same transport restricts to perfect matchings without deleting isolates. -/
def perfectMatchingEquiv : {M : Set (Edge G) // IsPerfectMatching M} ≃
    {H : (graph G).Subgraph // H.IsPerfectMatching} where
  toFun M := ⟨subgraph M.val, (perfect_iff_mathlib M.val).mp M.property⟩
  invFun H := ⟨coordinates H.val, (perfect_iff_mathlib _).mpr (by
    rw [subgraph_coordinates H.property.1]; exact H.property)⟩
  left_inv M := Subtype.ext (coordinates_subgraph M.val)
  right_inv H := Subtype.ext (subgraph_coordinates H.property.1)

/-- Incidence vectors use only zero and one, regardless of edge weights. -/
theorem indicator_zero_one (M : Set (Edge G)) (e : Edge G) :
    indicator M e = 0 ∨ indicator M e = 1 := by
  classical
  by_cases he : e ∈ M <;> simp [indicator, Specs.P205.Matching.indicator, he]

@[simp] theorem incidence_left (e : Edge G) :
    incidence G (.inl e.val.1) e = 1 := by
  simp [incidence, Specs.P205.Matching.incidence, Specs.P205.Matching.incident]

@[simp] theorem incidence_right (e : Edge G) :
    incidence G (.inr e.val.2) e = 1 := by
  simp [incidence, Specs.P205.Matching.incidence, Specs.P205.Matching.incident]

@[simp] theorem empty_matching : IsMatching (∅ : Set (Edge G)) := by
  constructor <;> intro e he <;> exact False.elim he

/-- Degree constraints characterize matchings on the actual allowed edges. -/
theorem matching_iff_degree (M : Set (Edge G)) :
    IsMatching M ↔ ∀ v, degree M v ≤ 1 := by
  simp only [degree, Specs.P205.Matching.degree, Finite.card_le_one_iff_subsingleton]
  constructor
  · intro h v
    constructor
    rintro ⟨e, he, hve⟩ ⟨f, hf, hvf⟩
    apply Subtype.ext
    cases v with
    | inl i => exact h.1 e he f hf (hve.symm.trans hvf)
    | inr j => exact h.2 e he f hf (hve.symm.trans hvf)
  · intro h
    constructor
    · intro e he f hf heq
      have hs := h (.inl e.val.1)
      exact congrArg Subtype.val (hs.elim ⟨e, he, rfl⟩ ⟨f, hf, heq⟩)
    · intro e he f hf heq
      have hs := h (.inr e.val.2)
      exact congrArg Subtype.val (hs.elim ⟨e, he, rfl⟩ ⟨f, hf, heq⟩)

theorem covered_iff_degree_pos (M : Set (Edge G)) (v : L ⊕ R) :
    Covered M v ↔ 0 < degree M v := by
  rw [degree, Specs.P205.Matching.degree, Nat.card_pos_iff]
  constructor
  · rintro ⟨e, he, hv⟩; exact ⟨⟨⟨e, he, hv⟩⟩, inferInstance⟩
  · rintro ⟨⟨⟨e, he, hv⟩⟩, _⟩; exact ⟨e, he, hv⟩

theorem perfect_iff_degree (M : Set (Edge G)) :
    IsPerfectMatching M ↔ ∀ v, degree M v = 1 := by
  change (IsMatching M ∧ ∀ v, Covered M v) ↔ _
  rw [matching_iff_degree]
  simp only [covered_iff_degree_pos]
  constructor
  · rintro ⟨h₁, h₂⟩ v
    exact Nat.le_antisymm (h₁ v) (h₂ v)
  · intro h
    exact ⟨fun v => (h v).le, fun v => by rw [h v]; exact Nat.zero_lt_one⟩

/-- Existence of the exact coordinate-to-unordered-edge equivalence. -/
theorem edge_transport : ∃ f : Edge G ≃ (graph G).edgeSet,
    ∀ e, (f e).val = edgePair e := ⟨edgeEquiv, fun _ => rfl⟩

theorem matching_transport : ∃ f : {M : Set (Edge G) // IsMatching M} ≃
    {H : (graph G).Subgraph // H.IsMatching},
    (∀ M, (f M).val = subgraph M.val) ∧
    (∀ H, (f.symm H).val = coordinates H.val) :=
  ⟨matchingEquiv, (fun _ => rfl), (fun _ => rfl)⟩

theorem perfect_transport : ∃ f : {M : Set (Edge G) // IsPerfectMatching M} ≃
    {H : (graph G).Subgraph // H.IsPerfectMatching},
    (∀ M, (f M).val = subgraph M.val) ∧
    (∀ H, (f.symm H).val = coordinates H.val) :=
  ⟨perfectMatchingEquiv, (fun _ => rfl), (fun _ => rfl)⟩

/-- The real degree used in the LP is the degree of the selected edge set. -/
theorem load_indicator (M : Set (Edge G)) (v : L ⊕ R) :
    load (indicator M) v = (degree M v : ℝ) := by
  classical
  let : Fintype {e : Edge G // e ∈ M ∧ incident v e} := Fintype.ofFinite _
  have hcard : (degree M v : ℝ) =
      ∑ e : Edge G, if e ∈ M ∧ incident v e then (1 : ℝ) else 0 := by
    rw [degree, Specs.P205.Matching.degree, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    exact Finset.natCast_card_filter _ _
  rw [hcard]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hM : e ∈ M <;> by_cases hv : incident v e <;>
    simp [Specs.P205.Matching.incidence, indicator,
      Specs.P205.Matching.indicator, hM, hv]

/-- Pullback is inverse to the unordered-edge image on coordinate subsets. -/
theorem preimage_edgeSet (M : Set (Edge G)) :
    edgePair ⁻¹' edgeSet M = M := by
  ext e
  constructor
  · rintro ⟨f, hf, he⟩
    exact (edgePair_injective he) ▸ hf
  · intro he; exact ⟨e, he, rfl⟩

/-- Every subset of actual graph edges is recovered, with no new edges. -/
theorem edgeSet_preimage (S : Set (Sym2 (L ⊕ R))) (hS : S ⊆ (graph G).edgeSet) :
    edgeSet ((@edgePair L R G) ⁻¹' S) = S := by
  change edgePair '' ((@edgePair L R G) ⁻¹' S) = S
  rw [Set.image_preimage_eq_iff, edgePair_range]
  exact hS

/-- Reverse comparison for arbitrary MathGenome edge sets. -/
theorem matching_preimage_mathGenome (S : Set (Sym2 (L ⊕ R)))
    (hS : S ⊆ (graph G).edgeSet) :
    IsMatching ((@edgePair L R G) ⁻¹' S) ↔
      FiniteCombinatorics.Graph.Matching.IsMatching (graph G) S := by
  rw [matching_iff_mathGenome, edgeSet_preimage S hS]

theorem perfect_preimage_mathGenome (S : Set (Sym2 (L ⊕ R)))
    (hS : S ⊆ (graph G).edgeSet) :
    IsPerfectMatching ((@edgePair L R G) ⁻¹' S) ↔
      FiniteCombinatorics.Graph.Matching.IsPerfectMatching (graph G) S := by
  rw [perfect_iff_mathGenome, edgeSet_preimage S hS]

end P205.Matching
