import MathGenome.Internal.D07.Ch03.SubgroupProductCounting
import MathGenome.Internal.D07.Ch04.FirstIsomorphism
import MathGenome.Internal.Specs.D07.Ch04.SecondIsomorphism
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
The second group isomorphism theorem (`K07.04.second_isomorphism`).
The normal product is the join, and restricting `N` to either subgroup
preserves normality. Mathlib's second-isomorphism equivalence is induced
by the inclusion of `H` followed by projection modulo `N`; the final
representative formula checks this forward map explicitly.
-/

namespace D07.Ch04.SecondIsomorphism

open scoped Pointwise
universe u

theorem product_subgroup (G : Type u) [Group G] (H N : Subgroup G) [N.Normal] :
    ((H ⊔ N : Subgroup G) : Set G) = (H : Set G) * (N : Set G) :=
  Subgroup.mul_normal H N

theorem normal_in_product (G : Type u) [Group G] (H N : Subgroup G) [N.Normal] :
    (N.subgroupOf (H ⊔ N)).Normal ∧
      (N.subgroupOf (H ⊔ N)).map (H ⊔ N).subtype = N := by
  exact ⟨inferInstance, Subgroup.map_subgroupOf_eq_of_le le_sup_right⟩

theorem intersection_normal (G : Type u) [Group G] (H N : Subgroup G) [N.Normal] :
    (N.subgroupOf H).Normal ∧ (N.subgroupOf H).map H.subtype = H ⊓ N := by
  exact ⟨inferInstance, (Subgroup.subgroupOf_map_subtype N H).trans (inf_comm N H)⟩

theorem second_isomorphism (G : Type u) [Group G] (H N : Subgroup G) [N.Normal] :
    ∃ e : H ⧸ N.subgroupOf H ≃*
        (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N),
      ∀ h : H, e (QuotientGroup.mk' (N.subgroupOf H) h) =
        QuotientGroup.mk' (N.subgroupOf (H ⊔ N))
          (Subgroup.inclusion (show H ≤ H ⊔ N from le_sup_left) h) := by
  exact ⟨QuotientGroup.quotientInfEquivProdNormalQuotient H N, fun _ => rfl⟩

end D07.Ch04.SecondIsomorphism
