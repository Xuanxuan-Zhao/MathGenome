import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeightSubmodules
import Mathlib.LinearAlgebra.Isomorphisms

namespace LieAlgebrasAndRepresentations.WeightSubmodules

universe u v

open scoped DirectSum BigOperators

variable {H : Type u} [LieRing H] [LieAlgebra ℂ H]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule H V] [LieModule ℂ H V]

local notation "weight[" M ", " μ "]" => LieSubmodule.toSubmodule (LieModule.weightSpace M (μ : _ → ℂ))

private theorem weight_independent [IsLieAbelian H] :
    iSupIndep (fun μ : Module.Dual ℂ H => weight[V, μ]) := by
  let : LieRing.IsNilpotent H := LieModule.trivialIsNilpotent H H
  have h := LieModule.iSupIndep_genWeightSpace ℂ H V
  rw [← LieSubmodule.iSupIndep_toSubmodule] at h
  exact (h.comp (fun a b h => LinearMap.ext fun x => congrFun h x)).mono
    (fun μ => LieModule.weightSpace_le_genWeightSpace V μ)

private theorem weight_map_le
    {V' : Type*} [AddCommGroup V'] [Module ℂ V'] [LieRingModule H V'] [LieModule ℂ H V']
    (f : V →ₗ⁅ℂ,H⁆ V') (μ : Module.Dual ℂ H) :
    (weight[V, μ]).map (f : V →ₗ[ℂ] V') ≤ weight[V', μ] := by
  rintro _ ⟨x, hx, rfl⟩
  change f x ∈ LieModule.weightSpace V' (μ : H → ℂ)
  change x ∈ LieModule.weightSpace V (μ : H → ℂ) at hx
  rw [LieModule.mem_weightSpace] at hx ⊢
  intro h
  rw [← f.map_lie, hx h, map_smul]

/-- A stable subspace and its quotient inherit the algebraic weight decomposition. -/
theorem weight_submodules :
    Specs.LieAlgebrasAndRepresentations.WeightSubmodules.weight_submodules_type := by
  classical
  intro H _ _ _ V _ _ _ _ W hV
  let q := LieSubmodule.Quotient.mk' W
  let A : Module.Dual ℂ H → Submodule ℂ V := fun μ => weight[V, μ]
  let B : Module.Dual ℂ H → Submodule ℂ (V ⧸ W) := fun μ => weight[(V ⧸ W), μ]
  let C : Module.Dual ℂ H → Submodule ℂ W := fun μ => (A μ).comap W.toSubmodule.subtype
  -- The images span the quotient, so independence identifies them with its weight spaces.
  have hBIndependent : iSupIndep B := weight_independent
  have hSpan : (⨆ μ, (A μ).map (q : V →ₗ[ℂ] V ⧸ W)) = ⊤ := by
    rw [← Submodule.map_iSup, hV.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (LieSubmodule.Quotient.surjective_mk' W)
  have hMaps : (fun μ => (A μ).map (q : V →ₗ[ℂ] V ⧸ W)) = B :=
    (hBIndependent.le_iff_eq_of_iSup_eq_top hSpan).mp (weight_map_le q)
  have hB : DirectSum.IsInternal B :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hBIndependent
      (hMaps ▸ hSpan)
  let components (μ : Module.Dual ℂ H) : A μ →ₗ[ℂ] B μ :=
    ((q : V →ₗ[ℂ] V ⧸ W).comp (A μ).subtype).codRestrict (B μ)
      (fun x => weight_map_le q μ (Submodule.mem_map_of_mem x.property))
  have hSum :
      (DirectSum.coeLinearMap B).comp (DirectSum.lmap components) =
        (q : V →ₗ[ℂ] V ⧸ W).comp (DirectSum.coeLinearMap A) := by
    apply DirectSum.linearMap_ext
    intro μ
    ext x
    simp [components]
  refine ⟨?_, hB, ?_⟩
  · change DirectSum.IsInternal C
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
    · have hC : C = fun (μ : Module.Dual ℂ H) => weight[W, μ] := by
        funext μ
        ext x
        change ((x : W) : V) ∈ LieModule.weightSpace V (μ : H → ℂ) ↔
          x ∈ LieModule.weightSpace W (μ : H → ℂ)
        simp only [LieModule.mem_weightSpace]
        refine forall_congr' fun h => ?_
        change ((⁅h, x⁆ : W) : V) = ((μ h • x : W) : V) ↔ ⁅h, x⁆ = μ h • x
        exact Subtype.ext_iff.symm
      rw [hC]
      exact weight_independent
    · apply top_unique
      intro w _
      obtain ⟨parts, hparts⟩ := hV.surjective (w : V)
      change DirectSum.coeLinearMap A parts = (w : V) at hparts
      -- A vector of W maps to zero, and the quotient sum has unique components.
      have hZero : DirectSum.lmap components parts = 0 := by
        apply hB.injective
        have h := DFunLike.congr_fun hSum parts
        change DirectSum.coeLinearMap B (DirectSum.lmap components parts) =
          q (DirectSum.coeLinearMap A parts) at h
        change DirectSum.coeLinearMap B (DirectSum.lmap components parts) =
          DirectSum.coeLinearMap B 0
        rw [h, hparts, map_zero]
        exact (LieSubmodule.Quotient.mk_eq_zero W).mpr w.property
      have hPart (μ : Module.Dual ℂ H) : ((parts μ : A μ) : V) ∈ W := by
        apply (LieSubmodule.Quotient.mk_eq_zero W).mp
        have h := congrArg (fun p : ⨁ μ, B μ => p μ) hZero
        exact congrArg Subtype.val (show components μ (parts μ) = 0 from h)
      have hv (μ : Module.Dual ℂ H) :
          (⟨(parts μ : V), hPart μ⟩ : W) ∈ C μ := (parts μ).property
      have hw : w = ∑ μ ∈ parts.support, (⟨(parts μ : V), hPart μ⟩ : W) := by
        apply Subtype.ext
        change (w : V) = W.toSubmodule.subtype (∑ μ ∈ parts.support, (⟨(parts μ : V), hPart μ⟩ : W))
        rw [map_sum, ← hparts, DirectSum.coeLinearMap_eq_dfinsuppSum]
        rfl
      rw [hw]
      exact Submodule.sum_mem _ fun μ _ => (le_iSup C μ) (hv μ)
  · intro μ
    have hSurj : Function.Surjective (components μ) := by
      intro y
      have hy : (y : V ⧸ W) ∈ (A μ).map (q : V →ₗ[ℂ] V ⧸ W) := by
        rw [congrFun hMaps μ]
        exact y.property
      obtain ⟨x, hx, he⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩
    have hKer : W.toSubmodule.comap (A μ).subtype = (components μ).ker := by
      ext x
      change (x : V) ∈ W ↔ components μ x = 0
      rw [← LieSubmodule.Quotient.mk_eq_zero W]
      change ((components μ x : B μ) : V ⧸ W) = ((0 : B μ) : V ⧸ W) ↔
        components μ x = 0
      exact Subtype.ext_iff.symm
    refine ⟨(Submodule.quotEquivOfEq _ _ hKer).trans
      ((components μ).quotKerEquivOfSurjective hSurj), ?_⟩
    intro x
    simp only [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
    rfl

end LieAlgebrasAndRepresentations.WeightSubmodules
