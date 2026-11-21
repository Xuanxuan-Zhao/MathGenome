import MathGenome.Internal.Specs.D07.Ch03.CosetsPartition
import Mathlib.GroupTheory.Index

/-!
Independent specification of K07.03.index_tower (paper.tex:599–609).

`G ⧸ H` is the set quotient by `x⁻¹ * y ∈ H`, not a quotient group.
`K.subgroupOf H` has carrier `{h : H | (h : G) ∈ K}`; when `K ≤ H`
this is precisely K viewed as a subgroup of H. Thus `H ⧸ K.subgroupOf H`
is the source's H/K. The first proposition identifies the quotient model
with the upstream set-valued left cosets.

The bijection exists without finiteness or normality. Its dependence on a
choice of representatives is recorded by the construction for every section
of G → G/H, with the source's formula for the inverse bijection. The natural
number index statements explicitly require both factor coset spaces finite;
the ambient group is allowed to be infinite. No infinite cardinality is
interpreted as an ordinary finite number.
-/

namespace Specs.D07.Ch03.IndexTower

universe u

def LeftCosetModel : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (x y : G),
    (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk y ↔
      CosetsPartition.leftCoset H x = CosetsPartition.leftCoset H y

def TowerBijection : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G), K ≤ H →
    Nonempty ((G ⧸ K) ≃ ((G ⧸ H) × (H ⧸ K.subgroupOf H)))

def TowerBijectionWithRepresentatives : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G), K ≤ H →
    ∀ (t : G ⧸ H → G),
      (∀ C : G ⧸ H, (QuotientGroup.mk (t C) : G ⧸ H) = C) →
      ∃ e : (G ⧸ K) ≃ ((G ⧸ H) × (H ⧸ K.subgroupOf H)),
        ∀ (C : G ⧸ H) (h : H),
          e.symm (C, (QuotientGroup.mk h : H ⧸ K.subgroupOf H)) =
            (QuotientGroup.mk (t C * (h : G)) : G ⧸ K)

def FiniteIndexTower : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G), K ≤ H →
    ∀ [Finite (G ⧸ H)] [Finite (H ⧸ K.subgroupOf H)],
      Finite (G ⧸ K) ∧ K.index = H.index * (K.subgroupOf H).index

def IndexTowerDivisibility : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G), K ≤ H →
    ∀ [Finite (G ⧸ H)] [Finite (H ⧸ K.subgroupOf H)],
      H.index ∣ K.index

end Specs.D07.Ch03.IndexTower
