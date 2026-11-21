import MathGenome.Internal.D07.Ch03.CosetsPartition
import MathGenome.Internal.Specs.D07.Ch03.IndexTower

/-!
Multiplication of indices, K07.03.index_tower (paper.tex:599–609).

The Mathlib quotient relation is exactly the upstream left-coset relation.
The representative-based equivalence sends `(C,hK)` to `t C * h K`.
Its construction and inverse laws do not require either subgroup normal.
Counting the product under the two finite-index hypotheses gives the formula
even for an infinite ambient group.
-/

namespace D07.Ch03.IndexTower

universe u

theorem left_coset_model (G : Type u) [Group G] (H : Subgroup G) (x y : G) :
    (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk y ↔
      Specs.D07.Ch03.CosetsPartition.leftCoset H x =
        Specs.D07.Ch03.CosetsPartition.leftCoset H y := by
  rw [← CosetsPartition.left_class_eq_coset G H x,
    ← CosetsPartition.left_class_eq_coset G H y]
  constructor
  · intro h
    ext z
    change (x⁻¹ * z ∈ H ↔ y⁻¹ * z ∈ H)
    rw [← QuotientGroup.eq, ← QuotientGroup.eq, h]
  · intro h
    apply QuotientGroup.eq.mpr
    have hy : y ∈ ({z : G | y⁻¹ * z ∈ H} : Set G) := by
      simpa only [Set.mem_ofPred_eq, inv_mul_cancel] using H.one_mem
    rw [← h] at hy
    exact hy

theorem tower_bijection (G : Type u) [Group G] (H K : Subgroup G) (hKH : K ≤ H) :
    Nonempty ((G ⧸ K) ≃ ((G ⧸ H) × (H ⧸ K.subgroupOf H))) :=
  ⟨Subgroup.quotientEquivProdOfLE hKH⟩

theorem tower_bijection_with_representatives (G : Type u) [Group G]
    (H K : Subgroup G) (hKH : K ≤ H) (t : G ⧸ H → G)
    (ht : ∀ C : G ⧸ H, (QuotientGroup.mk (t C) : G ⧸ H) = C) :
    ∃ e : (G ⧸ K) ≃ ((G ⧸ H) × (H ⧸ K.subgroupOf H)),
      ∀ (C : G ⧸ H) (h : H),
        e.symm (C, (QuotientGroup.mk h : H ⧸ K.subgroupOf H)) =
          (QuotientGroup.mk (t C * (h : G)) : G ⧸ K) := by
  exact ⟨Subgroup.quotientEquivProdOfLE' hKH t ht, fun _ _ => rfl⟩

theorem finite_index_tower (G : Type u) [Group G] (H K : Subgroup G) (hKH : K ≤ H)
    [Finite (G ⧸ H)] [Finite (H ⧸ K.subgroupOf H)] :
    Finite (G ⧸ K) ∧ K.index = H.index * (K.subgroupOf H).index := by
  let e := Subgroup.quotientEquivProdOfLE hKH
  have : Finite (G ⧸ K) :=
    Finite.of_equiv ((G ⧸ H) × (H ⧸ K.subgroupOf H)) e.symm
  refine ⟨inferInstance, ?_⟩
  change Nat.card (G ⧸ K) = Nat.card (G ⧸ H) * Nat.card (H ⧸ K.subgroupOf H)
  exact (Nat.card_congr e).trans (Nat.card_prod _ _)

theorem index_tower_divisibility (G : Type u) [Group G] (H K : Subgroup G)
    (hKH : K ≤ H) [Finite (G ⧸ H)] [Finite (H ⧸ K.subgroupOf H)] :
    H.index ∣ K.index := by
  exact ⟨(K.subgroupOf H).index, (finite_index_tower G H K hKH).2⟩

end D07.Ch03.IndexTower
