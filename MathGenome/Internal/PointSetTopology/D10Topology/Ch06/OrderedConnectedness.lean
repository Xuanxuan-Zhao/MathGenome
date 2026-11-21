import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.OrderedConnectedness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.Connectedness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.OrderTopologies
import Mathlib.Topology.Order.IntermediateValue

/-! Connected subsets of the real line and of a linear continuum.
The general theorem assumes only density and existence of least upper
bounds of nonempty bounded-above sets. The auxiliary chosen completeness
structure preserves the given linear order. -/

open Set
universe u

namespace D10Topology.Ch06

theorem real_connectedSubset_iff_orderConvex (A : Set ℝ) :
    ConnectedSubset A ↔
      ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℝ, a < t → t < b → t ∈ A := by
  rw [connectedSubset_iff_isPreconnected, isPreconnected_iff_ordConnected]
  constructor
  · intro h a ha b hb t hat htb
    exact h.out ha hb ⟨hat.le, htb.le⟩
  · intro h
    exact ordConnected_of_Ioo (fun a ha b hb _ t ht => h a ha b hb t ht.1 ht.2)

theorem real_intermediate_value {X : Type u} [TopologicalSpace X] (f : X → ℝ)
    (hX : Connected X) (hf : Continuous f) (a b : X) (t : ℝ)
    (ha : f a ≤ t) (hb : t ≤ f b) : ∃ x : X, f x = t := by
  have hr := (real_connectedSubset_iff_orderConvex (range f)).mp
    (connected_range f hX hf)
  rcases ha.eq_or_lt with h | h
  · exact ⟨a, h⟩
  rcases hb.eq_or_lt with h' | h'
  · exact ⟨b, h'.symm⟩
  exact hr (f a) ⟨a, rfl⟩ (f b) ⟨b, rfl⟩ t h h'

/-- Choosing suprema and infima from the LUB property adds operations,
without imposing any new order-theoretic hypothesis. -/
private noncomputable abbrev completeOrderOfLUB (L : Type u) [hL : LinearOrder L]
    [Nonempty L]
    (h : ∀ S : Set L, S.Nonempty → BddAbove S → ∃ c : L, IsLUB S c) :
    ConditionallyCompleteLinearOrder L := by
  classical
  have hi : ∀ S : Set L, S.Nonempty → BddBelow S → ∃ c : L, IsGLB S c := by
    intro S hn hb
    obtain ⟨c, hc⟩ := h (lowerBounds S) hb hn.bddAbove_lowerBounds
    exact ⟨c, isLUB_lowerBounds.mp hc⟩
  let sup : Set L → L := fun S =>
    if hS : S.Nonempty ∧ BddAbove S then (h S hS.1 hS.2).choose
    else Classical.choice ‹Nonempty L›
  let inf : Set L → L := fun S =>
    if hS : S.Nonempty ∧ BddBelow S then (hi S hS.1 hS.2).choose
    else Classical.choice ‹Nonempty L›
  exact
    { hL, LinearOrder.toLattice with
      sSup := sup
      sInf := inf
      isLUB_csSup := fun S hn hb => by
        change IsLUB S (sup S)
        simpa only [sup, dite_eq_left (show S.Nonempty ∧ BddAbove S from ⟨hn, hb⟩)] using (h S hn hb).choose_spec
      isGLB_csInf := fun S hn hb => by
        change IsGLB S (inf S)
        simpa only [inf, dite_eq_left (show S.Nonempty ∧ BddBelow S from ⟨hn, hb⟩)] using (hi S hn hb).choose_spec
      csSup_of_not_bddAbove := fun S hb => by
        simp only [sup, Set.not_nonempty_empty, false_and, ↓reduceDIte,
          show ¬ (S.Nonempty ∧ BddAbove S) from fun hS => hb hS.2]
      csInf_of_not_bddBelow := fun S hb => by
        simp only [inf, Set.not_nonempty_empty, false_and, ↓reduceDIte,
          show ¬ (S.Nonempty ∧ BddBelow S) from fun hS => hb hS.2] }

theorem linear_continuum_convex_connected (L : Type u) [LinearOrder L]
    [Nontrivial L] [DenselyOrdered L]
    (hLUB : ∀ S : Set L, S.Nonempty → BddAbove S → ∃ c : L, IsLUB S c)
    (A : Set L)
    (hA : ∀ a ∈ A, ∀ b ∈ A, ∀ t : L, a < t → t < b → t ∈ A) :
    @ConnectedSubset L (Ch01.orderTopology L) A ∧
      Ch01.orderTopology A = TopologicalSpace.induced (Subtype.val : A → L)
        (Ch01.orderTopology L) ∧
      @Connected A (Ch01.orderTopology A) := by
  let : ConditionallyCompleteLinearOrder L := completeOrderOfLUB L hLUB
  let : TopologicalSpace L := Ch01.orderTopology L
  let : OrderTopology L := ⟨rfl⟩
  have hc : OrdConnected A :=
    ordConnected_of_Ioo (fun a ha b hb _ t ht => hA a ha b hb t ht.1 ht.2)
  have hconn : ConnectedSubset A :=
    (connectedSubset_iff_isPreconnected A).mpr hc.isPreconnected
  have heq := Ch01.orderTopology_convex_subspace L A
    (fun a ha b hb t hat htb => hc.out ha hb ⟨hat, htb⟩)
  refine ⟨hconn, heq, ?_⟩
  rw [heq]
  exact hconn

end D10Topology.Ch06
