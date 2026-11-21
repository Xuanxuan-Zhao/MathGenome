import Mathlib.GroupTheory.Commutator.Basic

/-!
Independent specification of `K07.18.mixed_commutators`,
paper.tex:4946–4968 (chapters/M07.18.tex:8–30).

The canonical bracket of subgroups is identified below with ordinary subgroup
generation of exactly `a * b * a⁻¹ * b⁻¹`. It is not a normal closure or the
set of individual commutators. `Subgroup.map` denotes the ordinary image,
including for homomorphisms that are neither injective nor surjective.

For normal `N`, the subgroup `AN/N` of `G/N` is represented by
`(A ⊔ N).map (QuotientGroup.mk' N)`. The image and membership bridges below
identify it with the cosets of products `a * n`, and also with the image of
`A` alone. Thus no normality of `A` or containment `N ≤ A` is required in
the final criterion. All groups may be infinite or trivial; in particular
`A = ⊥` and `N = ⊤` are included. Source and target universes are independent.
-/

namespace Specs.D07.Ch18.MixedCommutators

open scoped commutatorElement

universe u v

def CommutatorGenerated : Prop :=
  ∀ (G : Type u) [Group G] (A B : Subgroup G),
    ⁅A, B⁆ = Subgroup.closure
      {z : G | ∃ a ∈ A, ∃ b ∈ B, a * b * a⁻¹ * b⁻¹ = z}

def ElementCommutatorInverse : Prop :=
  ∀ (G : Type u) [Group G] (a b : G),
    (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹

def ElementCommutatorMap : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H) (a b : G),
    f (a * b * a⁻¹ * b⁻¹) = f a * f b * (f a)⁻¹ * (f b)⁻¹

def CommutatorSymmetry : Prop :=
  ∀ (G : Type u) [Group G] (A B : Subgroup G), ⁅A, B⁆ = ⁅B, A⁆

def CommutatorMonotone : Prop :=
  ∀ (G : Type u) [Group G] (A B A' B' : Subgroup G),
    A ≤ A' → B ≤ B' → ⁅A, B⁆ ≤ ⁅A', B'⁆

def CommutatorImage : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) (A B : Subgroup G),
    (⁅A, B⁆).map f = ⁅A.map f, B.map f⁆

/-- Ordinary set-image equality records surjectivity onto the displayed subgroup. -/
def CommutatorImageSet : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) (A B : Subgroup G),
    f '' ((⁅A, B⁆ : Subgroup G) : Set G) = ((⁅A.map f, B.map f⁆ : Subgroup H) : Set H)

def AutomorphismImage : Prop :=
  ∀ (G : Type u) [Group G] (α : MulAut G) (A B : Subgroup G),
    (⁅A, B⁆).map α.toMonoidHom = ⁅A.map α.toMonoidHom, B.map α.toMonoidHom⁆

def CommutatorCharacteristic : Prop :=
  ∀ (G : Type u) [Group G] (A B : Subgroup G),
    A.Characteristic → B.Characteristic → (⁅A, B⁆).Characteristic

def CommutatorNormal : Prop :=
  ∀ (G : Type u) [Group G] (A B : Subgroup G),
    A.Normal → B.Normal → (⁅A, B⁆).Normal

def NormalElementCommutator : Prop :=
  ∀ (G : Type u) [Group G] (A : Subgroup G),
    A.Normal → ∀ a ∈ A, ∀ g : G, a * g * a⁻¹ * g⁻¹ ∈ A

def NormalCommutatorLe : Prop :=
  ∀ (G : Type u) [Group G] (A : Subgroup G),
    A.Normal → ⁅A, (⊤ : Subgroup G)⁆ ≤ A

def QuotientProductImage : Prop :=
  ∀ (G : Type u) [Group G] (A N : Subgroup G) [N.Normal],
    (A ⊔ N).map (QuotientGroup.mk' N) = A.map (QuotientGroup.mk' N)

def QuotientProductMembership : Prop :=
  ∀ (G : Type u) [Group G] (A N : Subgroup G) [N.Normal] (z : G ⧸ N),
    z ∈ (A ⊔ N).map (QuotientGroup.mk' N) ↔
      ∃ a ∈ A, ∃ n ∈ N, QuotientGroup.mk' N (a * n) = z

def QuotientCenterCriterion : Prop :=
  ∀ (G : Type u) [Group G] (A N : Subgroup G) [N.Normal],
    ⁅(⊤ : Subgroup G), A⁆ ≤ N ↔
      (A ⊔ N).map (QuotientGroup.mk' N) ≤ Subgroup.center (G ⧸ N)

end Specs.D07.Ch18.MixedCommutators
