import MathGenome.Internal.Specs.D07.Ch04.NormalityNotTransitive

/-! The explicit failure of transitivity of normality in `S₄`. -/

namespace D07.Ch04.NormalityNotTransitive

open Specs.D07.Ch04.NormalityNotTransitive

private theorem v_mul_closed :
    ∀ x ∈ vCarrier, ∀ y ∈ vCarrier, x * y ∈ vCarrier := by
  intro x hx y hy
  simp only [vCarrier, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;> decide

private theorem v_inv_closed : ∀ x ∈ vCarrier, x⁻¹ ∈ vCarrier := by
  intro x hx
  simp only [vCarrier, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl <;> decide

private def V : Subgroup S4 where
  carrier := vCarrier
  one_mem' := by simp [vCarrier]
  mul_mem' := fun hx hy => v_mul_closed _ hx _ hy
  inv_mem' := fun hx => v_inv_closed _ hx

private def H : Subgroup S4 where
  carrier := hCarrier
  one_mem' := by simp [hCarrier]
  mul_mem' := by
    intro x y hx hy
    simp only [hCarrier, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide
  inv_mem' := by
    intro x hx
    simp only [hCarrier, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl <;> decide

private theorem h_le_v : H ≤ V := by
  intro x hx
  change x ∈ hCarrier at hx
  change x ∈ vCarrier
  simp only [hCarrier, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> simp [vCarrier]

private theorem v_commutative : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  intro x hx y hy
  change x ∈ vCarrier at hx
  change y ∈ vCarrier at hy
  simp only [vCarrier, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;> decide

private theorem h_normal_in_v : (H.subgroupOf V).Normal := by
  constructor
  intro n hn g
  change (g : S4) * (n : S4) * (g : S4)⁻¹ ∈ H
  rw [v_commutative g g.property n n.property, mul_inv_cancel_right]
  exact hn

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem v_conjugation_closed :
    ∀ g x : S4, x ∈ vCarrier → g * x * g⁻¹ ∈ vCarrier := by
  unfold vCarrier
  decide

private theorem v_normal : V.Normal := by
  constructor
  intro n hn g
  exact v_conjugation_closed g n hn

theorem conjugation_witness : ConjugationWitness := by
  unfold ConjugationWitness hCarrier
  decide

private theorem h_not_normal : ¬ H.Normal := by
  intro h
  have hn : double12_34 ∈ H := conjugation_witness.1
  have hc := h.conj_mem double12_34 hn cycle123
  rw [conjugation_witness.2.1] at hc
  exact conjugation_witness.2.2 hc

theorem normality_not_transitive : Counterexample := by
  exact ⟨V, H, rfl, rfl, h_le_v, v_commutative, h_normal_in_v, v_normal, h_not_normal⟩

end D07.Ch04.NormalityNotTransitive
