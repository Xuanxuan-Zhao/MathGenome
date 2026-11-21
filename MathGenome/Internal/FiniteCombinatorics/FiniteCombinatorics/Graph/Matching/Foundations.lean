import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.Foundations

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Matching

abbrev IsMatching : Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsMatchingType :=
  Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsMatchingValue
abbrev EdgeMatching : Specs.FiniteCombinatorics.Graph.Matching.Foundations.EdgeMatchingType :=
  Specs.FiniteCombinatorics.Graph.Matching.Foundations.EdgeMatchingValue
abbrev Saturated : Specs.FiniteCombinatorics.Graph.Matching.Foundations.SaturatedType :=
  Specs.FiniteCombinatorics.Graph.Matching.Foundations.SaturatedValue
abbrev IsPerfectMatching : Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsPerfectMatchingType :=
  Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsPerfectMatchingValue
abbrev IsVertexCover : Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsVertexCoverType :=
  Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsVertexCoverValue
abbrev IsAugmentingPath : Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsAugmentingPathType :=
  Specs.FiniteCombinatorics.Graph.Matching.Foundations.IsAugmentingPathValue
abbrev edgeSubgraph : Specs.FiniteCombinatorics.Graph.Matching.Foundations.edgeSubgraphType :=
  Specs.FiniteCombinatorics.Graph.Matching.Foundations.edgeSubgraphValue

variable {V : Type u} [Finite V]

theorem saturated_iff_neighbor :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.saturated_iff_neighborType := by
  intro V _ M v
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
    exact ⟨w, he⟩
  · rintro ⟨w, hw⟩
    exact ⟨s(v, w), hw, Sym2.mem_mk_left v w⟩

theorem matching_iff_neighbors :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.matching_iff_neighborsType := by
  intro V _ G M
  constructor
  · rintro ⟨hsub, hd⟩
    refine ⟨hsub, fun a b c hab hac => ?_⟩
    exact (Sym2.mkEmbedding a).injective
      (hd _ hab _ hac a (Sym2.mem_mk_left a b) (Sym2.mem_mk_left a c))
  · rintro ⟨hsub, hd⟩
    refine ⟨hsub, fun e he f hf v hve hvf => ?_⟩
    obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp hve
    obtain ⟨c, rfl⟩ := Sym2.mem_iff_exists.mp hvf
    rw [hd v b c he hf]

theorem edgeSubgraph_edgeSet :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.edgeSubgraph_edgeSetType := by
  intro V _ G M h
  ext e
  induction e using Sym2.ind with
  | _ a b => rfl

theorem matching_subgraph_iff :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.matching_subgraph_iffType := by
  intro V _ G H
  constructor
  · intro h
    refine ⟨(matching_iff_neighbors G H.edgeSet).mpr ⟨H.edgeSet_subset,
      fun a b c hab hac => h.eq_of_adj_left hab hac⟩, ?_⟩
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, _⟩ := h hv
      exact ⟨s(v, w), hw, Sym2.mem_mk_left v w⟩
    · rintro ⟨e, he, hv⟩
      exact H.mem_verts_of_mem_edge he hv
  · rintro ⟨hm, hv⟩ v hvm
    have hs : Saturated H.edgeSet v := by simpa only [hv, Set.mem_ofPred_eq] using hvm
    obtain ⟨w, hw⟩ := (saturated_iff_neighbor H.edgeSet v).mp hs
    exact ⟨w, hw, fun y hy =>
      ((matching_iff_neighbors G H.edgeSet).mp hm).2 v y w hy hw⟩

theorem edgeSubgraph_isMatching :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.edgeSubgraph_isMatchingType := by
  intro V _ G M h
  rw [matching_subgraph_iff, edgeSubgraph_edgeSet]
  exact and_iff_left rfl

theorem perfect_subgraph_iff :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.perfect_subgraph_iffType := by
  intro V _ G H
  constructor
  · rintro ⟨hm, hspan⟩
    have hb := (matching_subgraph_iff G H).mp hm
    refine ⟨hb.1, fun v => ?_⟩
    have hv : v ∈ H.verts := hspan v
    simpa only [hb.2, Set.mem_ofPred_eq] using hv
  · rintro ⟨hm, hsat⟩
    have hv : H.verts = {v | Saturated H.edgeSet v} := by
      ext v
      exact ⟨fun _ => hsat v, fun _ => by
        obtain ⟨e, he, hv⟩ := hsat v
        exact H.mem_verts_of_mem_edge he hv⟩
    exact ⟨(matching_subgraph_iff G H).mpr ⟨hm, hv⟩, fun v => by
      rw [hv]
      exact hsat v⟩

theorem vertexCover_mathlib :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.vertexCover_mathlibType := by
  intro V _ G C
  constructor
  · intro h a b hab
    obtain ⟨v, hvC, hve⟩ := h s(a, b) hab
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · exact Or.inl hvC
    · exact Or.inr hvC
  · intro h e he
    induction e using Sym2.ind with
    | _ a b =>
      rcases h he with ha | hb
      · exact ⟨a, ha, Sym2.mem_mk_left a b⟩
      · exact ⟨b, hb, Sym2.mem_mk_right a b⟩

theorem empty_matching :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.empty_matchingType := by
  intro V _ G
  exact ⟨Set.empty_subset _, fun e he => False.elim he⟩

theorem empty_perfect :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.empty_perfectType := by
  intro V _ _ G
  exact ⟨empty_matching G, fun v => isEmptyElim v⟩

theorem covered_endpoint_injection :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.covered_endpoint_injectionType := by
  intro V _ G M C hm hc
  classical
  have h : ∀ e : M, ∃ v : C, v.val ∈ e.val := by
    intro e
    obtain ⟨v, hvC, hve⟩ := hc e.val (hm.1 e.property)
    exact ⟨⟨v, hvC⟩, hve⟩
  choose f hf using h
  refine ⟨f, ?_, hf⟩
  intro e d hed
  apply Subtype.ext
  exact hm.2 e.val e.property d.val d.property (f e).val (hf e)
    (by rw [hed]; exact hf d)

theorem matching_le_cover :
    Specs.FiniteCombinatorics.Graph.Matching.Foundations.matching_le_coverType := by
  intro V _ G M C hm hc
  obtain ⟨f, hf, _⟩ := covered_endpoint_injection G M C hm hc
  exact Nat.card_le_card_of_injective f hf

end FiniteCombinatorics.Graph.Matching
