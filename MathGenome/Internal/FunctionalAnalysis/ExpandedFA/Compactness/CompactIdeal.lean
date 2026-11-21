import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.CompactIdeal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.Definitions

/-!
The compact-ideal part of `fa2:p2:schauder-adjoint` (paper.tex:9458–9474).
The upstream equivalence identifies compact closure of the unit-ball image
with Mathlib's neighborhood definition. Mathlib proves the operations by
compact images and the norm closure by total boundedness and completeness
of the target. No finite-rank approximation is used.
-/

namespace ExpandedFA.Compactness

universe u v w vD vG

variable {𝕂 : Type u} [RCLike 𝕂]
  {E : Type v} {F : Type w} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕂 E] [NormedSpace 𝕂 F]

theorem compact_zero : IsCompactLinearMap (0 : E →ₗ[𝕂] F) := by
  exact (compact_iff_isCompactOperator _).mpr isCompactOperator_zero

theorem compact_add (S T : E →ₗ[𝕂] F)
    (hS : IsCompactLinearMap S) (hT : IsCompactLinearMap T) :
    IsCompactLinearMap (S + T) := by
  exact (compact_iff_isCompactOperator _).mpr
    (((compact_iff_isCompactOperator S).mp hS).add
      ((compact_iff_isCompactOperator T).mp hT))

/-- All scalars are allowed, including zero. -/
theorem compact_smul (a : 𝕂) (T : E →ₗ[𝕂] F) (hT : IsCompactLinearMap T) :
    IsCompactLinearMap (a • T) := by
  exact (compact_iff_isCompactOperator _).mpr
    (((compact_iff_isCompactOperator T).mp hT).smul a)

/-- The carrier of this subspace is exactly the set of bounded linear maps
whose unit-ball images have compact closure. -/
theorem compact_maps_form_subspace :
    ∃ M : Submodule 𝕂 (E →L[𝕂] F),
      ∀ T : E →L[𝕂] F, T ∈ M ↔ IsCompactLinearMap T.toLinearMap := by
  refine ⟨{
    carrier := {T | IsCompactLinearMap T.toLinearMap}
    zero_mem' := compact_zero
    add_mem' := fun hS hT => compact_add _ _ hS hT
    smul_mem' := fun a T hT => compact_smul a T.toLinearMap hT
  }, fun T => Iff.rfl⟩

theorem compact_precomp {D : Type vD} [NormedAddCommGroup D] [NormedSpace 𝕂 D]
    (T : E →ₗ[𝕂] F) (A : D →L[𝕂] E) (hT : IsCompactLinearMap T) :
    IsCompactLinearMap (T.comp A.toLinearMap) := by
  exact (compact_iff_isCompactOperator _).mpr
    (((compact_iff_isCompactOperator T).mp hT).comp_clm A)

theorem compact_postcomp {G : Type vG} [NormedAddCommGroup G] [NormedSpace 𝕂 G]
    (T : E →ₗ[𝕂] F) (B : F →L[𝕂] G) (hT : IsCompactLinearMap T) :
    IsCompactLinearMap (B.toLinearMap.comp T) := by
  exact (compact_iff_isCompactOperator _).mpr
    (((compact_iff_isCompactOperator T).mp hT).clm_comp B)

open Filter
open scoped Topology

/-- The topology on bounded linear maps here is their operator-norm topology. -/
theorem compact_operators_isClosed [CompleteSpace F] :
    IsClosed {T : E →L[𝕂] F | IsCompactLinearMap T.toLinearMap} := by
  have hset : {T : E →L[𝕂] F | IsCompactLinearMap T.toLinearMap} =
      {T : E →L[𝕂] F | IsCompactOperator T} := by
    ext T
    exact compact_iff_isCompactOperator T.toLinearMap
  rw [hset]
  exact isClosed_setOfPred_isCompactOperator

/-- No completeness of the domain, or nonzero assumption on the maps, is needed. -/
theorem compact_of_operatorNorm_tendsto [CompleteSpace F]
    (Tn : ℕ → E →L[𝕂] F) (T : E →L[𝕂] F)
    (hcompact : ∀ n, IsCompactLinearMap (Tn n).toLinearMap)
    (hlim : Tendsto (fun n => ‖Tn n - T‖) atTop (𝓝 0)) :
    IsCompactLinearMap T.toLinearMap := by
  have ht : Tendsto Tn atTop (𝓝 T) := tendsto_iff_norm_sub_tendsto_zero.mpr hlim
  exact compact_operators_isClosed.mem_of_tendsto ht (Eventually.of_forall hcompact)

theorem compact_maps_form_closed_subspace [CompleteSpace F] :
    ∃ M : Submodule 𝕂 (E →L[𝕂] F), IsClosed (M : Set (E →L[𝕂] F)) ∧
      ∀ T : E →L[𝕂] F, T ∈ M ↔ IsCompactLinearMap T.toLinearMap := by
  obtain ⟨M, hM⟩ := compact_maps_form_subspace (𝕂 := 𝕂) (E := E) (F := F)
  refine ⟨M, ?_, hM⟩
  have hset : (M : Set (E →L[𝕂] F)) =
      {T : E →L[𝕂] F | IsCompactLinearMap T.toLinearMap} := Set.ext hM
  rw [hset]
  exact compact_operators_isClosed

end ExpandedFA.Compactness
