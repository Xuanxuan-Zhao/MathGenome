import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InductionModels

/-! Induction in stages in the left-tensor convention. The subgroup of `K`
corresponding to `H ≤ K` is `H.subgroupOf K`; its representation is transported
along the canonical group isomorphism to `H`. No finiteness assumptions occur. -/
noncomputable section
set_option maxHeartbeats 2000000
universe u v w x
namespace P103.Ch09
open scoped MonoidAlgebra

variable {k : Type u} {G : Type v} [Field k] [Group G]
variable {H K : Subgroup G} (hHK : H ≤ K)
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- The given H-action, with H viewed as a subgroup of K. -/
def stageRestriction (ρ : Representation k H V) :
    Representation k (H.subgroupOf K) V :=
  ρ.comp (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom

/-- Data and the actual multiplication comparison, including the inverse
formula and equivariance on every vector. -/
structure StageData (ρ : Representation k H V) where
  inner : InductionData (H.subgroupOf K) (stageRestriction hHK ρ)
  outer : letI := inner.module; InductionData K inner.representation
  direct : InductionData H ρ
  equivalence : letI := inner.module; letI := outer.module; letI := direct.module
    Induced K inner.representation ≃ₗ[k] Induced H ρ
  forward_tensor : letI := inner.module; ∀ (g : G) (s : K) (z : V),
    equivalence (tensor K inner.representation (MonoidAlgebra.single g 1)
      (tensor (H.subgroupOf K) (stageRestriction hHK ρ) (MonoidAlgebra.single s 1) z)) =
    tensor H ρ (MonoidAlgebra.single (g * (s : G)) 1) z
  inverse_tensor : letI := inner.module; ∀ (g : G) (z : V),
    equivalence.symm (tensor H ρ (MonoidAlgebra.single g 1) z) =
    tensor K inner.representation (MonoidAlgebra.single g 1)
      (tensor (H.subgroupOf K) (stageRestriction hHK ρ) 1 z)
  equivariant : letI := inner.module; ∀ (g : G) (z : Induced K inner.representation),
    equivalence (outer.representation g z) = direct.representation g (equivalence z)

namespace Specs

def inductionStagesType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G]
    {H K : Subgroup G} (hHK : H ≤ K)
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k H V),
    Nonempty (StageData hHK ρ)

/-- Naturality for all choices of construction data and induced maps with the
specified tensor formulas. This includes every H-intertwiner, without a choice
of coset representatives. -/
def stageNaturalityCondition : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G]
    {H K : Subgroup G} (hHK : H ≤ K)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    (ρ : Representation k H V) (σ : Representation k H W)
    (D : StageData hHK ρ) (E : StageData hHK σ),
    letI := D.inner.module; letI := D.outer.module; letI := D.direct.module
    letI := E.inner.module; letI := E.outer.module; letI := E.direct.module
    ∀ (f : ρ.IntertwiningMap σ)
      (I : Induced (H.subgroupOf K) (stageRestriction hHK ρ) →ₗ[k]
        Induced (H.subgroupOf K) (stageRestriction hHK σ))
      (O : Induced K D.inner.representation →ₗ[k] Induced K E.inner.representation)
      (F : Induced H ρ →ₗ[k] Induced H σ),
      (∀ a z, I (tensor (H.subgroupOf K) (stageRestriction hHK ρ) a z) =
        tensor (H.subgroupOf K) (stageRestriction hHK σ) a (f z)) →
      (∀ a z, O (tensor K D.inner.representation a z) =
        tensor K E.inner.representation a (I z)) →
      (∀ a z, F (tensor H ρ a z) = tensor H σ a (f z)) →
      ∀ z, E.equivalence (O z) = F (D.equivalence z)

/-- For every H-intertwiner all three induced intertwiners exist, have their
actual tensor formulas, and commute with the stages comparison. -/
def inductionStagesNaturalityType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G]
    {H K : Subgroup G} (hHK : H ≤ K)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    (ρ : Representation k H V) (σ : Representation k H W)
    (D : StageData hHK ρ) (E : StageData hHK σ),
    letI := D.inner.module; letI := D.outer.module; letI := D.direct.module
    letI := E.inner.module; letI := E.outer.module; letI := E.direct.module
    ∀ f : ρ.IntertwiningMap σ,
      ∃ (I : D.inner.representation.IntertwiningMap E.inner.representation)
        (O : D.outer.representation.IntertwiningMap E.outer.representation)
        (F : D.direct.representation.IntertwiningMap E.direct.representation),
        (∀ a z, I (tensor (H.subgroupOf K) (stageRestriction hHK ρ) a z) =
          tensor (H.subgroupOf K) (stageRestriction hHK σ) a (f z)) ∧
        (∀ a z, O (tensor K D.inner.representation a z) =
          tensor K E.inner.representation a (I z)) ∧
        (∀ a z, F (tensor H ρ a z) = tensor H σ a (f z)) ∧
        ∀ z, E.equivalence (O z) = F (D.equivalence z)

end Specs
end P103.Ch09
