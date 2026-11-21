import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.WeakVariants.NormTotalTests
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace ExpandedFA.WeakVariants.NormTotalTests
universe u v
open Filter
open scoped Topology ENNReal
noncomputable section

/-- Scalar convergence on all of the dual is precisely the shared weak topology. -/
theorem weak_iff_tests (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (s : ℕ → X) (x : X) :
    Tendsto s atTop
      (@nhds X (P1.C12DualPairSpec.DualPairTopologyValue 𝕜 X (X →L[𝕜] 𝕜)
        (topDualPairing 𝕜 X)) x) ↔
    ∀ f : X →L[𝕜] 𝕜, Tendsto (fun n => f (s n)) atTop (𝓝 (f x)) := by
  rw [P1.dualPairTopology_evaluation 𝕜 X, nhds_iInf, tendsto_iInf]
  simp only [nhds_induced, tendsto_comap_iff, Function.comp_def]

/-- The convergent tests form a submodule. -/
def convergentTests (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (s : ℕ → X) (x : X) :
    Submodule 𝕜 (X →L[𝕜] 𝕜) where
  carrier := {f | Tendsto (fun n => f (s n)) atTop (𝓝 (f x))}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg; exact hf.add hg
  smul_mem' := by
    intro a f hf
    exact (tendsto_const_nhds (x := a)).smul hf

/-- A uniform bound on the vectors makes the family of dual evaluations
 equicontinuous, so convergence of tests is closed in the operator norm. -/
theorem convergentTests_closed (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (s : ℕ → X) (x : X)
    (hb : ∃ C : ℝ, ∀ n, ‖s n‖ ≤ C) :
    IsClosed (convergentTests 𝕜 X s x : Set (X →L[𝕜] 𝕜)) := by
  obtain ⟨C, hC⟩ := hb
  have he : Equicontinuous (fun n (f : X →L[𝕜] 𝕜) => f (s n)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun t => C * t)
      (by simpa using (tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))))
    intro f g n
    rw [dist_eq_norm, ← sub_apply]
    exact ((f - g).le_opNorm (s n)).trans (by
      rw [dist_eq_norm, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))
  exact he.isClosed_setOfPred_tendsto (ContinuousLinearMap.apply 𝕜 𝕜 x).continuous

theorem norm_total_criterion : Spec.NormTotalCriterion := by
  intro 𝕜 X _ _ _ s x S hb hS
  rw [weak_iff_tests]
  constructor
  · intro h f _; exact h f
  · intro h f
    have hspan : Submodule.span 𝕜 S ≤ convergentTests 𝕜 X s x :=
      Submodule.span_le.mpr h
    have hclosure : closure (Submodule.span 𝕜 S : Set (X →L[𝕜] 𝕜)) ⊆
        (convergentTests 𝕜 X s x : Set (X →L[𝕜] 𝕜)) :=
      closure_minimal hspan (convergentTests_closed 𝕜 X s x hb)
    apply hclosure
    change f ∈ (Submodule.span 𝕜 S).topologicalClosure
    rw [hS]
    trivial

theorem coordinate_counterexample : Spec.CoordinateCounterexample := by
  intro 𝕜 _
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y h
    ext j
    exact h j
  · intro n
    simp [lp.norm_single (p := (1 : ℝ≥0∞)) zero_lt_one]
  · intro j
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop j] with n hn
    change (0 : 𝕜) = lp.single (E := fun _ : ℕ => 𝕜) 1 n (1 : 𝕜) j
    simp [lp.single_apply, (ne_of_gt hn).symm]
  · intro n
    simp [lp.tsumCLM]
  · intro h
    have ht := (weak_iff_tests 𝕜 (lp (fun _ : ℕ => 𝕜) 1) _ 0).mp h
      (lp.tsumCLM 𝕜 ℕ 𝕜)
    have hone : ∀ n : ℕ, lp.tsumCLM 𝕜 ℕ 𝕜 (lp.single 1 n (1 : 𝕜)) = 1 := by
      intro n; simp [lp.tsumCLM]
    simp only [hone, map_zero] at ht
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

end
end ExpandedFA.WeakVariants.NormTotalTests
