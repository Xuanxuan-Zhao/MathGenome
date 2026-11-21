import MathGenome.Internal.D07.Ch17.Definition
import MathGenome.Internal.D07.Ch17.Characters
import MathGenome.Internal.D07.Ch17.IrreducibleDefinition
import MathGenome.Internal.Specs.D07.Ch21.DualTensor

namespace D07.Ch21.DualTensor
universe u v w x t z
noncomputable section
open scoped TensorProduct
open Specs.D07.Ch21.DualTensor

abbrev dualRepresentation : DualRepresentationType.{u,v,w} := dualRepresentationValue
abbrev tensorRepresentation : TensorRepresentationType.{u,v,w,x} := tensorRepresentationValue

theorem dual_laws : DualLaws.{u,v,w} := by
  intro K G V _ _ _ _ ρ
  refine ⟨fun _ _ _ => rfl, ρ.dual.map_one, ρ.dual.map_mul, ?_⟩
  intro g
  constructor
  · rw [← ρ.dual.map_mul, mul_inv_cancel, ρ.dual.map_one]
  · rw [← ρ.dual.map_mul, inv_mul_cancel, ρ.dual.map_one]

theorem dual_matrix : DualMatrix.{u,v,w,t} := by
  intro K G V ι _ _ _ _ _ _ b ρ g
  exact LinearMap.toMatrix_transpose (ρ g⁻¹)

theorem dual_character : DualCharacter.{u,v,w} := by
  intro K G V _ _ _ _ _ ρ g
  exact LinearMap.trace_transpose' (ρ g⁻¹)

theorem bidual_equivalence : BidualEquivalence.{u,v,w} := by
  intro K G V _ _ _ _ _ ρ
  refine ⟨{ toLinearEquiv := Module.evalEquiv K V, isIntertwining' := ?_ }, ?_⟩
  · intro g
    ext v φ
    simp [Representation.dual, Module.Dual.eval_apply]
  · intro v φ
    rfl

section Annihilators
variable {K : Type u} {G : Type v} {V : Type w}
  [Field K] [Group G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V)

/-- The annihilator of an invariant subspace, with the contragredient action. -/
def annihilator (U : Subrepresentation ρ) : Subrepresentation ρ.dual where
  toSubmodule := U.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g φ hφ := by
    rw [Submodule.mem_dualAnnihilator] at hφ ⊢
    intro v hv
    exact hφ (ρ g⁻¹ v) (U.apply_mem_toSubmodule g⁻¹ hv)

/-- The annihilator in V of an invariant subspace of V*. -/
def coannihilator (U : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := U.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro φ hφ
    have h := hv (ρ.dual g⁻¹ φ) (U.apply_mem_toSubmodule g⁻¹ hφ)
    simpa [Representation.dual] using h

end Annihilators

theorem annihilator_laws : AnnihilatorLaws.{u,v,w} := by
  intro K G V _ _ _ _ _ ρ U
  refine ⟨fun g _ hv => (coannihilator ρ U).apply_mem_toSubmodule g hv,
    Subspace.finrank_add_finrank_dualCoannihilator_eq U.toSubmodule, ?_⟩
  intro hU0 hUt
  have hd : U.toSubmodule.dualCoannihilator.dualAnnihilator = U.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  constructor
  · intro h0
    apply hUt
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊤
    simpa only [h0, Submodule.dualAnnihilator_bot] using hd.symm
  · intro ht
    apply hU0
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊥
    simpa only [ht, Submodule.dualAnnihilator_top] using hd.symm

theorem dual_irreducible : DualIrreducible.{u,v,w} := by
  intro K G V _ _ _ _ _ ρ
  constructor
  · intro h
    obtain ⟨hne, hU⟩ :=
      (Ch17.IrreducibleDefinition.irreducible_iff_subrepresentations ρ.dual).mp h
    have : Nontrivial V := (Module.nontrivial_dual_iff K).mp hne
    apply (Ch17.IrreducibleDefinition.irreducible_iff_subrepresentations ρ).mpr
    refine ⟨inferInstance, fun U => ?_⟩
    rcases hU (annihilator ρ U) with h0 | ht
    · right
      apply Subrepresentation.toSubmodule_injective
      exact Submodule.dualAnnihilator_eq_bot_iff.mp
        (congrArg Subrepresentation.toSubmodule h0)
    · left
      apply Subrepresentation.toSubmodule_injective
      exact Submodule.dualAnnihilator_eq_top_iff.mp
        (congrArg Subrepresentation.toSubmodule ht)
  · intro h
    obtain ⟨hne, hU⟩ :=
      (Ch17.IrreducibleDefinition.irreducible_iff_subrepresentations ρ).mp h
    have : Nontrivial V := hne
    apply (Ch17.IrreducibleDefinition.irreducible_iff_subrepresentations ρ.dual).mpr
    refine ⟨inferInstance, fun U => ?_⟩
    have hd : U.toSubmodule.dualCoannihilator.dualAnnihilator = U.toSubmodule :=
      Subspace.dualCoannihilator_dualAnnihilator_eq
    rcases hU (coannihilator ρ U) with h0 | ht
    · right
      apply Subrepresentation.toSubmodule_injective
      change U.toSubmodule = ⊤
      have h0' := congrArg Subrepresentation.toSubmodule h0
      change U.toSubmodule.dualCoannihilator = ⊥ at h0'
      simpa only [h0', Submodule.dualAnnihilator_bot] using hd.symm
    · left
      apply Subrepresentation.toSubmodule_injective
      change U.toSubmodule = ⊥
      have ht' := congrArg Subrepresentation.toSubmodule ht
      change U.toSubmodule.dualCoannihilator = ⊤ at ht'
      simpa only [ht', Submodule.dualAnnihilator_top] using hd.symm

theorem dual_zero : DualZero.{u,v,w} := by
  intro K G V _ _ _ _ _ ρ
  have : Subsingleton (Module.Dual K V) := (Module.subsingleton_dual_iff K).mpr inferInstance
  refine ⟨this, ?_, ?_⟩
  · exact (Ch17.IrreducibleDefinition.zero_space K G V ρ).2
  · exact (Ch17.IrreducibleDefinition.zero_space K G (Module.Dual K V) ρ.dual).2

theorem tensor_laws : TensorLaws.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ
  refine ⟨?_, (ρ.tprod σ).map_one, (ρ.tprod σ).map_mul, ?_⟩
  · intro g v w
    exact TensorProduct.map_tmul _ _ _ _
  · intro g
    constructor <;> rw [← map_mul] <;> simp

theorem tensor_matrix : TensorMatrix.{u,v,w,x,t,z} := by
  intro K G V W ι κ _ _ _ _ _ _ _ _ _ _ b c ρ σ g i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp [LinearMap.toMatrix_apply, Representation.tprod, mul_comm]

theorem tensor_character : TensorCharacter.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ _ _ ρ σ g
  exact LinearMap.trace_tensorProduct' (ρ g) (σ g)

theorem tensor_zero : TensorZero.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ _ _ ρ σ h
  have hz : Subsingleton (V ⊗[K] W) := by
    rcases h with h | h
    · have := h
      infer_instance
    · have := h
      infer_instance
  have := hz
  refine ⟨hz, fun g => ?_⟩
  have ht : Ch17.Characters.character K G (V ⊗[K] W) (ρ.tprod σ) g = 0 := by
    change LinearMap.trace K (V ⊗[K] W) ((ρ.tprod σ) g) = 0
    rw [Subsingleton.elim ((ρ.tprod σ) g) 0, map_zero]
  exact ⟨ht, (tensor_character K G V W ρ σ g).symm.trans ht⟩

end
end D07.Ch21.DualTensor
