import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OperatorTopology.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair

/-! Canonical strong and weak operator topologies on the existing bounded
linear maps, with their generating seminorms and arbitrary-filter convergence
tests. The Hilbert coefficient description is an equality of these topologies.
No separability, nonzero-space, or Banach-space assumptions enter the definitions.
-/

namespace ExpandedFA.OperatorTopology

open scoped Topology InnerProductSpace
noncomputable section

abbrev strongSeminorm : Spec.StrongSeminormType := Spec.StrongSeminormValue
abbrev weakSeminorm : Spec.WeakSeminormType := Spec.WeakSeminormValue
abbrev strongTopology : Spec.StrongTopologyType := Spec.StrongTopologyValue
abbrev weakTopology : Spec.WeakTopologyType := Spec.WeakTopologyValue
abbrev hilbertCoefficientTopology : Spec.HilbertCoefficientTopologyType :=
  Spec.HilbertCoefficientTopologyValue

theorem strongSeminorm_apply : Spec.StrongSeminormFormula := by
  intro 𝕜 E F _ _ _ _ _ x T
  rfl

theorem weakSeminorm_apply : Spec.WeakSeminormFormula := by
  intro 𝕜 E F _ _ _ _ _ x g T
  rfl

private def evaluationMap (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] : (E →L[𝕜] F) →ₗ[𝕜] (E → F) where
  toFun T x := T x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def coefficientMap (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] :
    (E →L[𝕜] F) →ₗ[𝕜] (E × (F →L[𝕜] 𝕜) → 𝕜) where
  toFun T p := p.2 (T p.1)
  map_add' T S := by ext p; simp
  map_smul' a T := by ext p; simp

theorem strong_withSeminorms : Spec.StrongWithSeminorms := by
  intro 𝕜 E F _ _ _ _ _
  let e : E ≃ (Σ _ : E, Unit) := .symm <| .sigmaUnique _ _
  have h := (evaluationMap 𝕜 E F).withSeminorms_induced
    ((withSeminorms_pi (fun _ : E => norm_withSeminorms 𝕜 F)).congr_equiv e)
  convert h using 1
  · ext x T
    rfl
  · rfl

theorem weak_withSeminorms : Spec.WeakWithSeminorms := by
  intro 𝕜 E F _ _ _ _ _
  let e : (E × (F →L[𝕜] 𝕜)) ≃ (Σ _ : E × (F →L[𝕜] 𝕜), Unit) :=
    .symm <| .sigmaUnique _ _
  have h := (coefficientMap 𝕜 E F).withSeminorms_induced
    ((withSeminorms_pi (fun _ : E × (F →L[𝕜] 𝕜) => norm_withSeminorms 𝕜 𝕜)).congr_equiv e)
  convert h using 1
  · ext x T
    rfl
  · rfl

theorem strong_initial : Spec.StrongInitial := by
  intro 𝕜 E F _ _ _ _ _
  exact induced_to_pi _

theorem weak_initial : Spec.WeakInitial := by
  intro 𝕜 E F _ _ _ _ _
  change TopologicalSpace.induced _ Pi.topologicalSpace = _
  rw [induced_to_pi, iInf_prod]

theorem strong_tendsto_iff : Spec.StrongTendsto := by
  intro 𝕜 E F _ _ _ _ _ α l f T
  change Filter.Tendsto f l (@nhds _ (TopologicalSpace.induced _ _) T) ↔ _
  rw [nhds_induced, Filter.tendsto_comap_iff, tendsto_pi_nhds]
  rfl

theorem weak_tendsto_iff : Spec.WeakTendsto := by
  intro 𝕜 E F _ _ _ _ _ α l f T
  change Filter.Tendsto f l (@nhds _ (TopologicalSpace.induced _ _) T) ↔ _
  rw [nhds_induced, Filter.tendsto_comap_iff, tendsto_pi_nhds]
  exact Prod.forall

theorem hilbert_weak_eq_coefficients : Spec.HilbertIdentification := by
  intro 𝕜 E F _ _ _ _ _ _
  rw [weak_initial 𝕜 E F]
  change _ = TopologicalSpace.induced _ Pi.topologicalSpace
  rw [induced_to_pi, iInf_prod]
  apply iInf_congr
  intro x
  exact ((InnerProductSpace.toDual 𝕜 F).surjective.iInf_comp
    (fun g : F →L[𝕜] 𝕜 => TopologicalSpace.induced
      (fun T : E →L[𝕜] F => g (T x)) inferInstance)).symm

theorem hilbert_tendsto_iff : Spec.HilbertTendsto := by
  intro 𝕜 E F _ _ _ _ _ _ α l f T
  rw [weak_tendsto_iff 𝕜 E F α l f T]
  exact forall_congr' fun x =>
    .symm <| Equiv.forall_congr (InnerProductSpace.toDual 𝕜 F) fun _ => Iff.rfl

theorem weak_native : Spec.WeakNative := by
  intro 𝕜 E F _ _ _ _ _
  change TopologicalSpace.induced _ _ = TopologicalSpace.induced _
    (TopologicalSpace.induced _ _)
  rw [induced_compose]
  rfl

theorem strong_coarsest : Spec.StrongCoarsest := by
  intro 𝕜 E F _ _ _ _ _ t
  rw [strong_initial 𝕜 E F, le_iInf_iff]
  simp only [continuous_iff_le_induced]

theorem weak_coarsest : Spec.WeakCoarsest := by
  intro 𝕜 E F _ _ _ _ _ t
  rw [weak_initial 𝕜 E F, le_iInf_iff]
  simp only [le_iInf_iff, continuous_iff_le_induced]

end
end ExpandedFA.OperatorTopology
