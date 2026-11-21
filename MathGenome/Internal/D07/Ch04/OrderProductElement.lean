import MathGenome.Internal.Specs.D07.Ch04.OrderProductElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Element orders and cyclicity in binary direct products (`paper.tex:753–763`).

`Prod.orderOf_mk` is the componentwise period formula and applies even to
infinite-order components. The finite cyclic product criterion is specialized
to the source's canonical residue-addition models after checking their
cardinalities. There is no nontriviality assumption on either factor.
-/

namespace D07.Ch04.OrderProductElement

universe u v

theorem finite_pair_order :
    Specs.D07.Ch04.OrderProductElement.FinitePairOrder.{u, v} := by
  intro G H _ _ x y _hx _hy
  exact Prod.orderOf_mk

theorem infinite_pair_order :
    Specs.D07.Ch04.OrderProductElement.InfinitePairOrder.{u, v} := by
  intro G H _ _ x y h
  rw [Prod.orderOf_mk]
  rcases h with hx | hy
  · simp only [hx, Nat.lcm_zero_left]
  · simp only [hy, Nat.lcm_zero_right]

theorem finite_cyclic_product_iff :
    Specs.D07.Ch04.OrderProductElement.FiniteCyclicProductIff.{u, v} := by
  intro G H _ _ _ _ _ _
  constructor
  · intro h
    exact (Group.isCyclic_prod_iff.mp h).2.2
  · intro h
    exact Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance, h⟩

theorem cyclic_models_product_iff :
    Specs.D07.Ch04.OrderProductElement.CyclicModelsProductIff := by
  intro m n hm hn
  let : NeZero m := ⟨hm.ne'⟩
  let : NeZero n := ⟨hn.ne'⟩
  have hcard_m : Nat.card (Multiplicative (ZMod m)) = m := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hcard_n : Nat.card (Multiplicative (ZMod n)) = n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  simpa only [hcard_m, hcard_n] using
    (finite_cyclic_product_iff (Multiplicative (ZMod m)) (Multiplicative (ZMod n)))

end D07.Ch04.OrderProductElement
