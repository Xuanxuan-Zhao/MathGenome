import MathGenome.Internal.Specs.D07.Ch03.SubgroupProductCounting
import MathGenome.Internal.Specs.D07.Ch04.FirstIsomorphism

/-!
Independent specification of `K07.04.second_isomorphism`, paper.tex:699–708.

The join `H ⊔ N` is used for the product subgroup; `ProductSubgroup` identifies
its carrier with the pointwise product `HN`, rather than assuming that a set
product is a subgroup. By definition, `N.subgroupOf H = N.comap H.subtype`:
its elements are precisely the elements of `H` whose values belong to `N`.
The image equalities below explicitly identify the two restricted subgroups
with `N` and `H ⊓ N` in the original ambient group.

All quotients use the canonical normal-subgroup instances induced by the
stated hypothesis `N.Normal`. There are no finiteness, commutativity, or
nontriviality assumptions. The representative formula specifies the forward
isomorphism as `h(H ∩ N) ↦ hN` in the product subgroup.
-/

namespace Specs.D07.Ch04.SecondIsomorphism

open scoped Pointwise
universe u

/-- In the presence of normality, the subgroup join has exactly carrier `HN`. -/
def ProductSubgroup : Prop :=
  ∀ (G : Type u) [Group G] (H N : Subgroup G) [N.Normal],
    ((H ⊔ N : Subgroup G) : Set G) = (H : Set G) * (N : Set G)

/-- `N`, viewed inside `HN`, is normal and embeds as the original `N`. -/
def NormalInProduct : Prop :=
  ∀ (G : Type u) [Group G] (H N : Subgroup G) [N.Normal],
    (N.subgroupOf (H ⊔ N)).Normal ∧
      (N.subgroupOf (H ⊔ N)).map (H ⊔ N).subtype = N

/-- The intersection is normal in `H`, and its ambient image is `H ∩ N`. -/
def IntersectionNormal : Prop :=
  ∀ (G : Type u) [Group G] (H N : Subgroup G) [N.Normal],
    (N.subgroupOf H).Normal ∧
      (N.subgroupOf H).map H.subtype = H ⊓ N

/-- The second isomorphism theorem with its value on every representative. -/
def SecondIsomorphism : Prop :=
  ∀ (G : Type u) [Group G] (H N : Subgroup G) [N.Normal],
    ∃ e : H ⧸ N.subgroupOf H ≃*
        (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N),
      ∀ h : H, e (QuotientGroup.mk' (N.subgroupOf H) h) =
        QuotientGroup.mk' (N.subgroupOf (H ⊔ N))
          (Subgroup.inclusion (show H ≤ H ⊔ N from le_sup_left) h)

end Specs.D07.Ch04.SecondIsomorphism
