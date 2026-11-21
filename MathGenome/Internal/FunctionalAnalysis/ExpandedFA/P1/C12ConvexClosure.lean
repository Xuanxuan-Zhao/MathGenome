import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12ConvexClosure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-! Weak and norm closures of real-convex sets agree. The library separation
argument applies to real convexity over either scalar field. We transport its
conclusion from the native weak-space carrier to the canonical topology on E.
-/

namespace ExpandedFA.P1.C12ConvexClosure

universe u v
noncomputable section

/-- Equality of closures, including the empty set and incomplete spaces. -/
theorem weak_closure_eq_norm_closure : Spec.ConvexClosure.{u,v} := by
  intro 𝕜 E _ _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  let : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  intro C hC
  change @closure E (TopologicalSpace.induced (toWeakSpace 𝕜 E)
    (instTopologicalSpaceWeakSpace 𝕜 E)) C = closure C
  ext x
  rw [closure_induced, ← hC.toWeakSpace_closure 𝕜]
  exact ⟨fun ⟨y, hy, hyx⟩ => (toWeakSpace 𝕜 E).injective hyx ▸ hy,
    fun hx => ⟨x, hx, rfl⟩⟩

/-- Norm-closed real-convex sets are weakly closed. -/
theorem isWeaklyClosed_of_isClosed_convex : Spec.ClosedConvex.{u,v} := by
  intro 𝕜 E _ _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro C hC hclosed
  exact (@closure_eq_iff_isClosed E
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) C).mp
      ((weak_closure_eq_norm_closure 𝕜 E C hC).trans hclosed.closure_eq)

/-- A norm-closed linear subspace is weakly closed. -/
theorem isWeaklyClosed_of_isClosed_submodule : Spec.ClosedSubspace.{u,v} := by
  intro 𝕜 E _ _ _ M hM
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  exact isWeaklyClosed_of_isClosed_convex 𝕜 E M (M.restrictScalars ℝ).convex hM

theorem subspace_weak_scalar_tests : Spec.ScalarTests.{u,v} := by
  intro 𝕜 E _ _ _ M
  constructor
  · intro F
    refine ⟨F.comp M.subtypeL, (fun _ => rfl), ?_⟩
    exact (ContinuousLinearMap.opNorm_comp_le F M.subtypeL).trans
      (mul_le_of_le_one_right (norm_nonneg F) M.norm_subtypeL_le)
  · exact C05NormExtension.norm_preserving_extension 𝕜 E M

theorem subspace_weak_test_families_eq :
    Spec.TestFamilyEquality.{u,v} := by
  intro 𝕜 E _ _ _ M
  apply Set.Subset.antisymm
  · rintro g ⟨F, rfl⟩
    obtain ⟨f, hf, _⟩ := (subspace_weak_scalar_tests 𝕜 E M).1 F
    exact ⟨f, funext hf⟩
  · rintro g ⟨f, rfl⟩
    obtain ⟨F, hF, _⟩ := (subspace_weak_scalar_tests 𝕜 E M).2 f
    exact ⟨F, funext hF⟩

theorem subspace_induced_weak_topology :
    Spec.InducedTopology.{u,v} := by
  intro 𝕜 E _ _ _ M
  rw [dualPairTopology_evaluation 𝕜 E, induced_iInf,
    dualPairTopology_evaluation 𝕜 M]
  simp_rw [induced_compose]
  apply le_antisymm
  · refine le_iInf fun f => ?_
    obtain ⟨F, hF, _⟩ := (subspace_weak_scalar_tests 𝕜 E M).2 f
    refine iInf_le_of_le F ?_
    have heq : (F : E → 𝕜) ∘ (fun m : M => (m : E)) = (f : M → 𝕜) :=
      funext hF
    rw [heq]
  · refine le_iInf fun F => ?_
    exact iInf_le_of_le (F.comp M.subtypeL) le_rfl

end
end ExpandedFA.P1.C12ConvexClosure
