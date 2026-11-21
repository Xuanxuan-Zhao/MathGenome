import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.BaseChange.GaloisExtensions
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.InverseLimit.Profiniteness
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.InfiniteGalois
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.BaseChange.RestrictionIsomorphism

universe u v
noncomputable section
namespace AdvancedFieldTheory
open IntermediateField

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
variable (E M : IntermediateField K Ω) [IsGalois K E]

local notation "C" => (E ⊔ M : IntermediateField K Ω)
local notation "I" => (E ⊓ M : IntermediateField K Ω)
local instance compositumRightAlgebra : Algebra M C := (inclusion le_sup_right).toAlgebra
local instance compositumLeftAlgebra : Algebra E C := (inclusion le_sup_left).toAlgebra
local instance intersectionLeftAlgebra : Algebra I E := (inclusion inf_le_left).toAlgebra
local instance : IsScalarTower K E C := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower K M C := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower K I E := IsScalarTower.of_algebraMap_eq' rfl
local instance : IsGalois M C := galois_compositum_over_right E M
local instance : IsGalois I E := galois_over_intersection E M

/-- Restriction to the actual field E, with the larger fixed base E ∩ M. -/
def baseChangeRestriction : (C ≃ₐ[M] C) →* (E ≃ₐ[I] E) where
  toFun g :=
    { (g.restrictScalars K).restrictNormal E with
      commutes' := by
        intro x
        apply Subtype.ext
        have h := (g.restrictScalars K).restrictNormal_commutes E
          (algebraMap I E x)
        have hg := g.commutes (⟨(x : Ω), x.property.2⟩ : M)
        exact congrArg (fun y : C => (y : Ω)) (h.trans hg) }
  map_one' := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E C).injective
    exact (AlgEquiv.restrictNormal_commutes (1 : C ≃ₐ[K] C) E x)
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E C).injective
    change algebraMap E C (((g * h).restrictScalars K).restrictNormal E x) =
      algebraMap E C ((g.restrictScalars K).restrictNormal E
        ((h.restrictScalars K).restrictNormal E x))
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes,
      AlgEquiv.restrictNormal_commutes]
    rfl

@[simp] theorem baseChangeRestriction_apply (g : C ≃ₐ[M] C) (x : E) :
    ((baseChangeRestriction E M g x : E) : Ω) =
      (g ⟨(x : Ω), (le_sup_left : E ≤ E ⊔ M) x.property⟩ : Ω) := by
  exact congrArg (fun y : C => (y : Ω))
    ((g.restrictScalars K).restrictNormal_commutes E x)

/-- The same restriction formula expressed in the compositum. -/
theorem baseChangeRestriction_apply_inclusion (g : C ≃ₐ[M] C) (x : E) :
    algebraMap E C (baseChangeRestriction E M g x) = g (algebraMap E C x) :=
  (g.restrictScalars K).restrictNormal_commutes E x

/-- E and M generate their compositum, so restriction is injective. -/
theorem baseChangeRestriction_injective : Function.Injective (baseChangeRestriction E M) := by
  intro g h he
  have hh : g.toAlgHom.restrictScalars K = h.toAlgHom.restrictScalars K := by
    apply adjoin_algHom_ext K (s := (E : Set Ω) ∪ (M : Set Ω))
    intro x hx
    rcases hx with hx | hx
    · have he' := congrArg (fun f : E ≃ₐ[I] E => algebraMap E C (f ⟨x, hx⟩)) he
      rw [baseChangeRestriction_apply_inclusion, baseChangeRestriction_apply_inclusion] at he'
      exact he'
    · exact (g.commutes (⟨x, hx⟩ : M)).trans (h.commutes (⟨x, hx⟩ : M)).symm
  exact AlgEquiv.ext fun x => DFunLike.congr_fun hh x

/-- Restriction is continuous for the two intrinsic Krull topologies. -/
theorem baseChangeRestriction_continuous : Continuous (baseChangeRestriction E M) := by
  apply (KrullTopology.continuous_iff_evaluations I E _).mpr
  intro x
  let : TopologicalSpace E := ⊥
  let : DiscreteTopology E := ⟨rfl⟩
  let : TopologicalSpace C := ⊥
  let : DiscreteTopology C := ⟨rfl⟩
  have hc : Continuous (fun g : C ≃ₐ[M] C => g (algebraMap E C x)) :=
    (KrullTopology.continuous_iff_evaluations M C id).mp continuous_id _
  apply continuous_discrete_rng.mpr
  intro y
  have heq : (fun g : C ≃ₐ[M] C => baseChangeRestriction E M g x) ⁻¹' {y} =
      (fun g : C ≃ₐ[M] C => g (algebraMap E C x)) ⁻¹' {algebraMap E C y} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      ← baseChangeRestriction_apply_inclusion,
      (algebraMap E C).injective.eq_iff]
  rw [heq]
  exact (isOpen_discrete _).preimage hc

/-- The restriction image fixes exactly the intersection, expressed as the
bottom field for the intrinsic extension E/(E ∩ M). -/
theorem baseChangeRestriction_fixedField :
    fixedField (baseChangeRestriction E M).range = (⊥ : IntermediateField I E) := by
  apply le_antisymm _ bot_le
  intro x hx
  have hfix : algebraMap E C x ∈ fixedField (⊤ : Subgroup (C ≃ₐ[M] C)) := by
    apply (mem_fixedField _ _).mpr
    intro g _
    rw [← baseChangeRestriction_apply_inclusion]
    congr 1
    exact (mem_fixedField _ _).mp hx _ ⟨g, rfl⟩
  rw [full_fixedField_eq_bot M C] at hfix
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hfix
  have hyΩ : (y : Ω) = (x : Ω) := congrArg (fun z : C => (z : Ω)) hy
  apply IntermediateField.mem_bot.mpr
  refine ⟨⟨(x : Ω), x.property, ?_⟩, ?_⟩
  · exact hyΩ ▸ y.property
  · rfl

/-- Compactness closes the restriction image; the infinite Galois
correspondence then makes this image the whole target group. -/
theorem baseChangeRestriction_surjective : Function.Surjective (baseChangeRestriction E M) := by
  let : T2Space (E ≃ₐ[I] E) := galoisGroup_t2Space I E
  have hclosed : IsClosed ((baseChangeRestriction E M).range : Set (E ≃ₐ[I] E)) :=
    (isCompact_range (baseChangeRestriction_continuous E M)).isClosed
  apply MonoidHom.range_eq_top.mp
  have hrec := fixingSubgroup_fixedField_eq_topologicalClosure (baseChangeRestriction E M).range
  rw [baseChangeRestriction_fixedField, fixingSubgroup, IntermediateField.fixingSubgroup_bot] at hrec
  have hcl : (baseChangeRestriction E M).range.topologicalClosure =
      (baseChangeRestriction E M).range := by
    apply SetLike.ext'
    exact hclosed.closure_eq
  rw [hcl] at hrec
  exact hrec.symm

/-- C10: both Galoisness assertions and the unique topological group
isomorphism whose underlying action is restriction to E. -/
theorem baseChange_restriction_topologicalIsomorphism :
    IsGalois M C ∧ IsGalois I E ∧
    ∃! e : (C ≃ₐ[M] C) ≃ₜ* (E ≃ₐ[I] E),
      ∀ g x, ((e g x : E) : Ω) =
        (g ⟨(x : Ω), (le_sup_left : E ≤ E ⊔ M) x.property⟩ : Ω) := by
  let : T2Space (E ≃ₐ[I] E) := galoisGroup_t2Space I E
  let e := MulEquiv.ofBijective (baseChangeRestriction E M)
    ⟨baseChangeRestriction_injective E M, baseChangeRestriction_surjective E M⟩
  have hc : Continuous e := baseChangeRestriction_continuous E M
  let t : (C ≃ₐ[M] C) ≃ₜ* (E ≃ₐ[I] E) :=
    { e with
      continuous_toFun := hc
      continuous_invFun :=
        (e.toEquiv.toHomeomorphOfContinuousClosed hc hc.isClosedMap).continuous_invFun }
  refine ⟨inferInstance, inferInstance, t, baseChangeRestriction_apply E M, ?_⟩
  intro t' ht'
  apply ContinuousMulEquiv.ext
  intro g
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact (ht' g x).trans (baseChangeRestriction_apply E M g x).symm

end AdvancedFieldTheory
