import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Matching.Hall
import Mathlib.Combinatorics.SimpleGraph.Hall

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Matching
open Alternating

variable {V : Type u} [Fintype V] {G : SimpleGraph V} {L R : Set V}

omit [Fintype V] in
/-- The shared bipartition gives the corresponding Mathlib bipartition. -/
lemma bipartition_mathlib (hB : Bipartition G L R) : G.IsBipartiteWith L R :=
  ⟨hB.disjoint, hB.crosses⟩

omit [Fintype V] in
/-- On a left subset, the shared neighbors are exactly the union of the
Mathlib neighbor sets. In particular, restricting neighbors to R loses none. -/
lemma neighbors_eq_union (hB : Bipartition G L R) {X : Set V} (hX : X ⊆ L) :
    neighbors G R X = ⋃ x ∈ X, G.neighborSet x := by
  ext y
  simp only [neighbors, Set.mem_ofPred_eq, Set.mem_iUnion, SimpleGraph.mem_neighborSet]
  constructor
  · rintro ⟨_, x, hx, hxy⟩
    exact ⟨x, hx, hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨(bipartition_mathlib hB).mem_of_mem_adj (hX hx) hxy, x, hx, hxy⟩

/-- Matching partners inject any saturated left subset into its neighbors. -/
lemma card_le_neighbors_of_saturated (hB : Bipartition G L R)
    {M : Set (Sym2 V)} (hM : IsMatching G M)
    (hsat : ∀ x ∈ L, Saturated M x) {X : Set V} (hX : X ⊆ L) :
    Nat.card X ≤ Nat.card (neighbors G R X) := by
  classical
  have hp : ∀ x : X, ∃ y : ↥(neighbors G R X), s(x.val, y.val) ∈ M := by
    intro x
    obtain ⟨y, hxy⟩ := (saturated_iff_neighbor M x.val).mp (hsat x.val (hX x.property))
    have hadj : G.Adj x.val y := hM.1 hxy
    have hyR := (bipartition_mathlib hB).mem_of_mem_adj (hX x.property) hadj
    exact ⟨⟨y, hyR, x.val, x.property, hadj⟩, hxy⟩
  choose f hf using hp
  apply Nat.card_le_card_of_injective f
  intro x z hxz
  apply Subtype.ext
  have hyx : s((f x).val, x.val) ∈ M := by
    simpa only [Sym2.eq_swap] using hf x
  have hyz : s((f x).val, z.val) ∈ M := by
    rw [hxz]
    simpa only [Sym2.eq_swap] using hf z
  exact ((matching_iff_neighbors G M).mp hM).2 _ _ _ hyx hyz

/-- Hall's marriage theorem, for a matching saturating L, also when either
part is empty. The sufficient direction uses Mathlib's single-part theorem. -/
theorem hall : Specs.FiniteCombinatorics.Graph.Matching.Hall.hallType := by
  intro V _ G L R hB
  classical
  constructor
  · rintro ⟨M, hM, hsat⟩ X hX
    exact card_le_neighbors_of_saturated hB hM hsat hX
  · intro h
    have hcard : ∀ X ⊆ L, X.ncard ≤ (⋃ x ∈ X, G.neighborSet x).ncard := by
      intro X hX
      have hc := h X hX
      rw [neighbors_eq_union hB hX] at hc
      exact hc
    obtain ⟨H, hLH, hH⟩ :=
      SimpleGraph.exists_isMatching_of_forall_ncard_le (bipartition_mathlib hB) hcard
    obtain ⟨hm, hv⟩ := (matching_subgraph_iff G H).mp hH
    refine ⟨H.edgeSet, hm, fun x hx => ?_⟩
    have hxH := hLH hx
    rw [hv] at hxH
    exact hxH

end FiniteCombinatorics.Graph.Matching
