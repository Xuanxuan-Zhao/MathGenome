import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14WeakSubsequence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Stability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14DualSeparability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Embedding
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
Weak subsequences without separability of the ambient space.
The sequence's closed span M is separable, complete and reflexive, so M′
is norm separable. Sequential Banach–Alaoglu on M″ supplies an extraction
whose limit is represented in M by surjectivity of J_M. Restricting each
ambient functional to M gives weak convergence in E.

The library sequential Alaoglu theorem uses metrizability of a compact
dual ball with separable predual; no general weak compactness to sequential
compactness implication is used.
-/

namespace ExpandedFA.P1.C14WeakSubsequence

universe u v
open Filter TopologicalSpace
open scoped Topology

/-- Theorem `fa2:p1:c14:weak-subsequence` for either scalar field,
including nonseparable ambient spaces. -/
theorem reflexive_weak_subsequence : Spec.WeakSubsequence.{u, v} := by
  intro 𝕜 E _ _ _ _ href a ha
  let M := (Submodule.span 𝕜 (Set.range a)).topologicalClosure
  have hclosed : IsClosed (M : Set E) := Submodule.isClosed_topologicalClosure _
  let : CompleteSpace M := hclosed.isComplete.completeSpace_coe
  have hsep : IsSeparable (M : Set E) :=
    ((Set.countable_range a).isSeparable.span (R := 𝕜)).closure
  let : SeparableSpace M := hsep.separableSpace
  have hMref := ((C14Stability.reflexivity_stability 𝕜 E M hclosed).1 href).1
  let : SeparableSpace (M →L[𝕜] 𝕜) :=
    C14DualSeparability.dual_separable_of_separable_reflexive 𝕜 M inferInstance hMref
  let b : ℕ → M := fun n =>
    ⟨a n, Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_range_self n))⟩
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp ha
  let J := C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 M
  let c : ℕ → WeakDual 𝕜 (M →L[𝕜] 𝕜) :=
    fun n => StrongDual.toWeakDual (J (b n))
  have hc : ∀ n, c n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : (M →L[𝕜] 𝕜) →L[𝕜] 𝕜) R := by
    intro n
    have hn : ‖J (b n)‖ ≤ R := by
      rw [show ‖J (b n)‖ = ‖b n‖ from
        C05BidualIsometry.canonicalEvaluation_norm 𝕜 M (b n)]
      exact hR (a n) (Set.mem_range_self n)
    change dist (J (b n)) 0 ≤ R
    exact (dist_zero_right (J (b n))).le.trans hn
  obtain ⟨ξ, _hξ, k, hk, hconv⟩ :=
    (WeakDual.isSeqCompact_closedBall (𝕜 := 𝕜) (E := M →L[𝕜] 𝕜)
      (0 : (M →L[𝕜] 𝕜) →L[𝕜] 𝕜) R) hc
  obtain ⟨z, hz⟩ := hMref ξ.toStrongDual
  refine ⟨k, hk, (z : E), ?_⟩
  rw [dualPairTopology_evaluation 𝕜 E, nhds_iInf]
  simp only [tendsto_iInf, nhds_induced, tendsto_comap_iff, Function.comp_def]
  intro f
  have ht := ((WeakDual.eval_continuous (𝕜 := 𝕜) (f.comp M.subtypeL)).tendsto ξ).comp
    hconv
  change Tendsto (fun n => (f.comp M.subtypeL) (b (k n))) atTop
    (𝓝 (ξ (f.comp M.subtypeL))) at ht
  have hval : ξ (f.comp M.subtypeL) = f (z : E) :=
    congrArg (fun ψ : (M →L[𝕜] 𝕜) →L[𝕜] 𝕜 => ψ (f.comp M.subtypeL)) hz.symm
  rw [hval] at ht
  exact ht

end ExpandedFA.P1.C14WeakSubsequence
