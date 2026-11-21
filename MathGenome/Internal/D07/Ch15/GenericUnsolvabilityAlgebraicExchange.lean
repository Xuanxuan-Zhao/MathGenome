import MathGenome.Internal.Specs.D07.Ch15.GenericUnsolvabilityAlgebraicExchange
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! Algebraic exchange and the finite generator bound, in arbitrary characteristic. -/

universe u v

namespace D07.Ch15.GenericUnsolvabilityAlgebraicExchange

open Specs.D07.Ch15.GenericUnsolvabilityAlgebraicExchange
open scoped IntermediateField.algebraAdjoinAdjoin

/-- The algebraic closure operator on a field is a matroid closure. Its exchange
law applies to algebraicity over generated fields because the generated field
is algebraic over the generated subalgebra (indeed its fraction field). -/
theorem algebraic_exchange : AlgebraicExchange.{u, v} := by
  intro B M _ _ _ x y hx hxy
  have hx0 : x ∉ (AlgebraicIndependent.matroid B M).closure ∅ := by
    rw [AlgebraicIndependent.matroid_closure_eq]
    change ¬ IsAlgebraic (Algebra.adjoin B ∅) x
    rw [Algebra.adjoin_empty]
    exact fun h => hx ((Subalgebra.isAlgebraic_bot_iff (algebraMap B M).injective).mp h)
  have hxy' : x ∈ (AlgebraicIndependent.matroid B M).closure (insert y ∅) := by
    rw [insert_empty_eq, AlgebraicIndependent.matroid_closure_eq,
      SetLike.mem_coe, Subalgebra.mem_algebraicClosure]
    change IsAlgebraic (Algebra.adjoin B {y}) x
    exact hxy.restrictScalars _
  have hy := Matroid.mem_closure_insert hx0 hxy'
  rw [insert_empty_eq, AlgebraicIndependent.matroid_closure_eq,
      SetLike.mem_coe, Subalgebra.mem_algebraicClosure] at hy
  change IsAlgebraic (Algebra.adjoin B {x}) y at hy
  exact hy.extendScalars
    (FaithfulSMul.algebraMap_injective (Algebra.adjoin B {x})
      (IntermediateField.adjoin B {x}))

/-- A spanning generating set bounds transcendence degree even if it is
 dependent; independence supplies the reverse bound for the tested tuple. -/
theorem independent_cardinality_bound : IndependentCardinalityBound.{u, v} := by
  intro K M _ _ _ s t c a hM ha
  let := hM
  let : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range c)) M :=
    ⟨fun z => (hM.isAlgebraic z).restrictScalars _⟩
  have hupper := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range c)
  have hlower := ha.lift_cardinalMk_le_trdeg
  have hrange := Cardinal.mk_range_le_lift (f := c)
  have hbound : (t : Cardinal.{v}) ≤ s := by
    calc
      (t : Cardinal.{v}) ≤ Algebra.trdeg K M := by simpa using hlower
      _ ≤ Cardinal.mk (Set.range c) := hupper
      _ ≤ (s : Cardinal.{v}) := by simpa using hrange
  exact_mod_cast hbound

theorem no_independent_successor : NoIndependentSuccessor.{u, v} := by
  intro K M _ _ _ s c hM a ha
  exact Nat.not_succ_le_self s (independent_cardinality_bound K M s (s + 1) c a hM ha)

end D07.Ch15.GenericUnsolvabilityAlgebraicExchange
