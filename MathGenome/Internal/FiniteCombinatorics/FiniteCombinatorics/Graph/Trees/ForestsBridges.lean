import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.Characterizations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.ForestsBridges

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Trees

attribute [local instance] Classical.propDecidable

abbrev Bridge : Specs.FiniteCombinatorics.Graph.Trees.ForestsBridges.BridgeType :=
  fun {_} _ G e => componentCount G < componentCount (G.deleteEdges {e})

/-- Removing edges increases the component count exactly when some
previously reachable pair is separated. This uses finiteness, including the
possibility of no vertices. -/
lemma component_count_lt_iff {V : Type u} [Finite V] {H G : SimpleGraph V}
    (hle : H ≤ G) :
    Nat.card G.ConnectedComponent < Nat.card H.ConnectedComponent ↔
      ∃ a b : V, G.Reachable a b ∧ ¬ H.Reachable a b := by
  let f := SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hle)
  have hs : Function.Surjective f := SimpleGraph.ConnectedComponent.surjective_map_ofLE hle
  have hi : Function.Injective f ↔ ∀ a b : V, G.Reachable a b → H.Reachable a b := by
    constructor
    · intro hf a b hab
      exact SimpleGraph.ConnectedComponent.exact
        (hf (show f (H.connectedComponentMk a) = f (H.connectedComponentMk b) from
          SimpleGraph.ConnectedComponent.sound hab))
    · intro h c d
      induction c using SimpleGraph.ConnectedComponent.ind with | h a =>
        induction d using SimpleGraph.ConnectedComponent.ind with | h b =>
          intro hab
          exact SimpleGraph.ConnectedComponent.sound
            (h a b (SimpleGraph.ConnectedComponent.exact hab))
  have hcard := Nat.card_le_card_of_surjective f hs
  constructor
  · intro hlt
    by_contra! h
    have hinj : Function.Injective f := hi.mpr (by simpa using h)
    have := Nat.card_le_card_of_injective f hinj
    omega
  · rintro ⟨a, b, hab, hn⟩
    by_contra hlt
    have heq : Nat.card H.ConnectedComponent = Nat.card G.ConnectedComponent := by omega
    have hinj := ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hs, heq⟩).injective
    exact hn (hi.mp hinj a b hab)

theorem bridge_iff_isBridge :
    Specs.FiniteCombinatorics.Graph.Trees.ForestsBridges.bridge_iff_isBridgeType := by
  intro V _ G e he
  change (Nat.card G.ConnectedComponent < Nat.card (G.deleteEdges {e}).ConnectedComponent) ↔ _
  rw [component_count_lt_iff (G.deleteEdges_le {e})]
  constructor
  · rintro ⟨a, b, hab, hn⟩
    by_contra hb
    exact hn (hab.reachable_deleteEdges_of_not_isBridge hb)
  · intro hb
    induction e using Sym2.ind with
    | _ a b => exact ⟨a, b, (show G.Adj a b from he).reachable, hb⟩

theorem bridge_iff_no_cycle :
    Specs.FiniteCombinatorics.Graph.Trees.ForestsBridges.bridge_iff_no_cycleType := by
  intro V _ G e he
  exact (bridge_iff_isBridge G e he).trans (SimpleGraph.isBridge_iff_forall_cycle_notMem he)

/-- Summation over components partitions the vertex set, with no nonemptiness
assumption on the graph. -/
lemma sum_over_components {V : Type u} [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent]
    (f : V → ℕ) :
    ∑ c : G.ConnectedComponent, ∑ v : c, f v = ∑ v : V, f v := by
  classical
  exact Fintype.sum_fiberwise G.connectedComponentMk f

/-- W38: sum the tree degree formulas over all connected components. Using
addition before natural subtraction also handles the empty forest. -/
theorem forest_edge_count :
    Specs.FiniteCombinatorics.Graph.Trees.ForestsBridges.forest_edge_countType := by
  intro V _ G hG
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hc (c : G.ConnectedComponent) :
      (∑ v : c, G.degree v) + 2 = 2 * Fintype.card c := by
    have ht := hG.isTree_connectedComponent c
    have he := ht.card_edgeFinset
    have hd := c.toSimpleGraph.sum_degrees_eq_twice_card_edges
    have hdeg (v : c) : c.toSimpleGraph.degree v = G.degree v := by
      apply SimpleGraph.degree_induce_of_neighborSet_subset
      intro w hw
      exact c.mem_supp_of_adj_mem_supp v.property hw
    simp_rw [hdeg] at hd
    omega
  have hv : ∑ c : G.ConnectedComponent, Fintype.card c = Fintype.card V := by
    simpa using sum_over_components G (fun _ => 1)
  have hs := Finset.sum_congr rfl (fun c (_ : c ∈ (Finset.univ : Finset G.ConnectedComponent)) => hc c)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Finset.mul_sum] at hs
  rw [sum_over_components G (fun v => G.degree v), hv,
    G.sum_degrees_eq_twice_card_edges] at hs
  have he : Nat.card G.edgeSet = G.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  change Nat.card G.edgeSet = Nat.card V - Nat.card G.ConnectedComponent
  rw [he, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  omega

end FiniteCombinatorics.Graph.Trees
