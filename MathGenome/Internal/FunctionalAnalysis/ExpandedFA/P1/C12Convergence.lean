import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12Convergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Annihilators

/-!
Evaluation criteria for arbitrary nets, norm-to-weak convergence, and the
weak continuity of bounded linear maps and weak-star continuity of their
Banach transposes (Proposition `fa2:p1:c12:convergence`).
-/

namespace ExpandedFA.P1.C12Convergence

universe u v w z
open Filter
open scoped Topology
noncomputable section

/-- The initial topology tests convergence coordinate by coordinate.
An arbitrary filter includes all directed nets, without a sequence restriction. -/
theorem weak_tendsto_iff : Spec.WeakConvergence := by
  intro 𝕜 E A _ _ _ l xₐ x
  rw [dualPairTopology_evaluation 𝕜 E, nhds_iInf]
  simp only [tendsto_iInf, nhds_induced, tendsto_comap_iff, Function.comp_def]

theorem weakStar_tendsto_iff : Spec.WeakStarConvergence := by
  intro 𝕜 E A _ _ _ l fₐ f
  rw [C12WeakStar.weakStarTopology_evaluations 𝕜 E, nhds_iInf]
  simp only [tendsto_iInf, nhds_induced, tendsto_comap_iff, Function.comp_def]

/-- Each norm-continuous linear functional preserves a norm limit. -/
theorem norm_tendsto_weak : Spec.NormImpliesWeak := by
  intro 𝕜 E A _ _ _ l xₐ x h
  apply (weak_tendsto_iff 𝕜 E A l xₐ x).mpr
  intro f
  exact (f.continuous.tendsto x).comp h

/-- Evaluation at a fixed vector is continuous for the operator norm. -/
theorem norm_tendsto_weakStar : Spec.NormImpliesWeakStar := by
  intro 𝕜 E A _ _ _ l fₐ f h
  apply (weakStar_tendsto_iff 𝕜 E A l fₐ f).mpr
  intro x
  exact ((ContinuousLinearMap.apply 𝕜 𝕜 x).continuous.tendsto f).comp h

/-- Testing T against g ∈ F′ is testing the input against g∘T ∈ E′. -/
theorem operator_weak_continuous : Spec.WeakContinuity := by
  intro 𝕜 E F _ _ _ _ _ T
  rw [dualPairTopology_evaluation 𝕜 F]
  apply continuous_iInf_rng.mpr
  intro g
  apply continuous_induced_rng.mpr
  change @Continuous E 𝕜
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
    inferInstance (fun x => (g.comp T) x)
  rw [continuous_iff_le_induced, dualPairTopology_evaluation 𝕜 E]
  exact iInf_le _ (g.comp T)

/-- Evaluating T′f at x is precisely evaluating f at Tx. -/
theorem transpose_weakStar_continuous : Spec.TransposeWeakStarContinuity := by
  intro 𝕜 E F _ _ _ _ _ T
  rw [C12WeakStar.weakStarTopology_evaluations 𝕜 E]
  apply continuous_iInf_rng.mpr
  intro x
  apply continuous_induced_rng.mpr
  change @Continuous (F →L[𝕜] 𝕜) 𝕜
    (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 F)
    inferInstance (fun f => f (T x))
  rw [continuous_iff_le_induced, C12WeakStar.weakStarTopology_evaluations 𝕜 F]
  exact iInf_le _ (T x)

end
end ExpandedFA.P1.C12Convergence
