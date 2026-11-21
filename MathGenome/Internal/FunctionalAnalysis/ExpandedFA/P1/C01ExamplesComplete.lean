import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01ExamplesComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Banach

/-!
Completeness of the canonical examples (paper.tex 259–265).

Mathlib's `lp.completeSpace` uses coordinate limits and finite power-sum
bounds (or uniform bounds for infinity) with exactly our canonical `lp` norm.
The epsilon/2 argument below proves that `c₀` is closed in `ℓ∞`, so it is
complete in its inherited norm. The continuous-map completeness instance uses
uniform limits of continuous functions; compactness identifies its norm with
the supremum norm. The accepted Banach bridge translates completeness to the
manuscript's every-norm-Cauchy-sequence definition.
-/

open Filter
open scoped Topology ENNReal

universe u v
namespace ExpandedFA.P1.C01ExamplesComplete
open C01SequenceSpaces C01Banach

theorem sequence_lp_banach : Spec.LpBanach.{u} := by
  intro 𝕜 _ p _
  exact (isBanachSpace_iff_completeSpace (SequenceLp 𝕜 p)).mpr inferInstance

theorem sequence_c0_closed : Spec.C0Closed.{u} := by
  intro 𝕜 _
  apply isClosed_of_closure_subset
  intro x hx
  change Tendsto (fun j => x j) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  change Tendsto (fun j => y j) atTop (𝓝 0) at hy
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy (ε / 2) (half_pos hε)
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_zero_right]
  calc
    ‖x j‖ ≤ ‖x j - y j‖ + ‖y j‖ := norm_le_norm_sub_add (x j) (y j)
    _ ≤ ‖x - y‖ + ‖y j‖ :=
      add_le_add (lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) j) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa [dist_eq_norm] using hxy)
      (by simpa only [dist_zero_right] using hN j hj)
    _ = ε := add_halves ε

theorem sequence_c0_banach : Spec.C0Banach.{u} := by
  intro 𝕜 _
  let : CompleteSpace (SequenceC0 𝕜) :=
    (sequence_c0_closed 𝕜).isComplete.completeSpace_coe
  exact (isBanachSpace_iff_completeSpace (SequenceC0 𝕜)).mpr inferInstance

theorem continuous_functions_bounded : Spec.ContinuousFunctionsBounded.{u, v} := by
  intro 𝕜 K _ _ _ _ f
  exact ⟨(isCompact_range f.continuous).isBounded,
    ‖f‖, norm_nonneg f, f.norm_coe_le_norm⟩

theorem continuous_functions_supremum_norm : Spec.SupremumNorm.{u, v} := by
  intro 𝕜 K _ _ _ _ f
  exact ⟨f.norm_eq_iSup_norm, fun _ hM => f.norm_le hM⟩

theorem continuous_functions_banach : Spec.ContinuousFunctionsBanach.{u, v} := by
  intro 𝕜 K _ _ _ _
  exact (isBanachSpace_iff_completeSpace C(K, 𝕜)).mpr inferInstance

theorem continuous_functions_empty_domain : Spec.EmptyDomain.{u, v} := by
  intro 𝕜 K _ _ _ _ _ f
  have hf : f = 0 := by
    ext t
    exact isEmptyElim t
  exact ⟨hf, hf ▸ norm_zero⟩

end ExpandedFA.P1.C01ExamplesComplete
