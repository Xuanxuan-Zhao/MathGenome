import MathGenome.Internal.D07.Ch02.CycleDecomposition
import MathGenome.Internal.D07.Ch02.OrderDivisibility
import MathGenome.Internal.Specs.D07.Ch02.PermutationOrder

/-!
# Order from disjoint cycle lengths

The library's cycle type records support cardinalities. We identify those
cardinalities with the lengths of the written cycles of the accepted
decomposition, then apply the order formula for cycle types.
-/

namespace D07.Ch02.PermutationOrder

open Equiv
open Specs.D07.Ch02.CycleDecomposition

universe u

/-- A written nontrivial cycle moves exactly its distinct entries. -/
theorem support_card_formPerm {X : Type u} [Fintype X] [DecidableEq X]
    (l : List X) (hl : l.Nodup) (hlen : 2 ≤ l.length) :
    l.formPerm.support.card = l.length := by
  rw [List.support_formPerm_of_nodup l hl]
  · exact List.toFinset_card_of_nodup hl
  · intro x hx
    have := congrArg List.length hx
    simp only [List.length_singleton] at this
    omega

/-- Cycle type is exactly the multiset of lengths in any accepted
written decomposition; in particular, no fixed points are counted as
nontrivial cycles. -/
theorem cycleType_eq_lengths {X : Type u} [Fintype X]
    (σ : Perm X) (L : List (List X)) (hL : Decomposition σ L) : by
    classical
    exact σ.cycleType = (L.map List.length : Multiset ℕ) := by
  classical
  have hc : ∀ g ∈ L.map List.formPerm, g.IsCycle := by
    intro g hg
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
    exact List.isCycle_formPerm (hL.1 l hl).1 (hL.1 l hl).2
  have hd : (L.map List.formPerm).Pairwise Perm.Disjoint := by
    apply List.pairwise_map.mpr
    apply hL.2.1.imp_of_mem
    intro l m hl hm hdisj
    exact (List.formPerm_disjoint_iff (hL.1 l hl).1 (hL.1 m hm).1
      (hL.1 l hl).2 (hL.1 m hm).2).mpr hdisj
  rw [Perm.cycleType_eq (L.map List.formPerm) hL.2.2 hc hd]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro l hl
  exact support_card_formPerm l (hL.1 l hl).1 (hL.1 l hl).2

private theorem multiset_lcm_eq_foldr (ns : List ℕ) :
    (ns : Multiset ℕ).lcm = ns.foldr Nat.lcm 1 := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    simp only [← Multiset.cons_coe, Multiset.lcm_cons, List.foldr_cons,
      ih, lcm_eq_nat_lcm]

theorem order_from_cycle_lengths :
    Specs.D07.Ch02.PermutationOrder.OrderFromCycleLengths.{u} := by
  classical
  intro X _ σ L hL
  let := Fintype.ofFinite X
  rw [← Perm.lcm_cycleType σ, cycleType_eq_lengths σ L hL,
    multiset_lcm_eq_foldr]

theorem exists_decomposition_with_order :
    Specs.D07.Ch02.PermutationOrder.ExistsDecompositionWithOrder.{u} := by
  intro X _ σ
  obtain ⟨L, hL⟩ := D07.Ch02.CycleDecomposition.cycle_decomposition X σ
  exact ⟨L, hL, order_from_cycle_lengths X σ L hL⟩

theorem empty_cycle_lengths :
    Specs.D07.Ch02.PermutationOrder.EmptyCycleLengths.{u} := by
  intro X _
  constructor
  · classical
    simp [Decomposition]
  · simp

end D07.Ch02.PermutationOrder
