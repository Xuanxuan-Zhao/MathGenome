import MathGenome.Internal.Specs.D07.Ch03.CosetBijections
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Perm.Basic

/-!
Independent specification of K07.03.subgroup_product_counting,
paper.tex:627–641. Products are pointwise products of subgroup carriers;
they carry no assumed group structure. Only the counting assertions require
finite factors, and the ambient group is arbitrary throughout.
-/
namespace Specs.D07.Ch03.SubgroupProductCounting

open scoped Pointwise
universe u

/-- The product is finite and its size is the exact natural-number quotient.
The intersection contains the identity, so the denominator is positive. -/
def ProductCardinality : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G) [Finite H] [Finite K],
    ((H : Set G) * (K : Set G)).Finite ∧
      Nat.card ↥((H : Set G) * (K : Set G)) =
        Nat.card H * Nat.card K / Nat.card ↥(H ⊓ K)

/-- Representations are ordered pairs of elements of the two factors. -/
def RepresentationCount : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G) [Finite H] [Finite K]
    (x : G), x ∈ (H : Set G) * (K : Set G) →
      Nat.card {p : H × K // (p.1 : G) * (p.2 : G) = x} = Nat.card ↥(H ⊓ K)

/-- Being a subgroup means being the carrier of a subgroup with ambient operations. -/
def ProductSubgroupIff : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G),
    (∃ L : Subgroup G, (L : Set G) = (H : Set G) * (K : Set G)) ↔
      (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)

def NormalLeftProductComm : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G) [H.Normal],
    (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)

def NormalRightProductComm : Prop :=
  ∀ (G : Type u) [Group G] (H K : Subgroup G) [K.Normal],
    (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)

/-- The source's boundary: a product of subgroups need not be a subgroup. -/
def ProductNotAlwaysSubgroup : Prop :=
  ∃ H K : Subgroup (Equiv.Perm (Fin 3)),
    ¬ ∃ L : Subgroup (Equiv.Perm (Fin 3)),
      (L : Set (Equiv.Perm (Fin 3))) = (H : Set _) * (K : Set _)

end Specs.D07.Ch03.SubgroupProductCounting
