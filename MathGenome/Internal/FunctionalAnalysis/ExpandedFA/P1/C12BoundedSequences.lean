import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12BoundedSequences
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04DualComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.WeakstarSequenceBounds

/-!
The bounds in `fa2:p1:c12:bounded-sequences`. Uniform boundedness acts on the
complete dual, so the original space need not be complete. A norming functional
at the limit proves the liminf inequality. The weak-star clauses reuse the
accepted results on the Banach predual with precisely the same topology.
-/

namespace ExpandedFA.P1.C12BoundedSequences

universe u v w
open Filter
open scoped Topology
noncomputable section

/-- The scalar tests defining the weak topology are continuous. -/
theorem weak_evaluation_continuous (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : E →L[𝕜] 𝕜) :
    @Continuous E 𝕜
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      inferInstance f := by
  rw [continuous_iff_le_induced, dualPairTopology_evaluation 𝕜 E]
  exact iInf_le _ f

/-- Apply uniform boundedness to the canonical evaluations on the complete dual.
The arbitrary index type permits empty families as well as sequences. -/
theorem norm_bound_of_scalar_bounds
    (𝕜 : Type u) (E : Type v) (I : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (s : I → E)
    (h : ∀ f : E →L[𝕜] 𝕜, ∃ C : ℝ, ∀ i, ‖f (s i)‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖s i‖ ≤ C := by
  letI : CompleteSpace (E →L[𝕜] 𝕜) := C04DualComplete.dual_completeSpace 𝕜 E
  obtain ⟨C, hC, hb⟩ := C07UniformBoundedness.uniform_boundedness 𝕜 (E →L[𝕜] 𝕜) 𝕜 I
    (fun i => C04CanonicalMap.canonicalEvaluation 𝕜 E (s i)) h
  refine ⟨C, hC, fun i => ?_⟩
  calc
    ‖s i‖ = ‖C04CanonicalMap.canonicalEvaluation 𝕜 E (s i)‖ :=
      (C05BidualIsometry.canonicalEvaluation_norm 𝕜 E (s i)).symm
    _ ≤ C := hb i

/-- Weak convergence gives convergence of each original continuous linear test. -/
theorem weak_evaluation_tendsto (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (s : ℕ → E) (x : E)
    (hs : Tendsto s atTop
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) x)) (f : E →L[𝕜] 𝕜) :
    Tendsto (fun n => f (s n)) atTop (𝓝 (f x)) := by
  let : TopologicalSpace E :=
    C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
  exact ((weak_evaluation_continuous 𝕜 E f).tendsto x).comp hs

theorem weak_sequence_bounded : Spec.WeakSequenceBounded := by
  intro 𝕜 E _ _ _ s x hs
  apply norm_bound_of_scalar_bounds 𝕜 E ℕ s
  intro f
  obtain ⟨C, hC⟩ := (weak_evaluation_tendsto 𝕜 E s x hs f).norm.bddAbove_range
  exact ⟨C, fun n => hC (Set.mem_range_self n)⟩

theorem weak_sequence_norm_liminf : Spec.WeakSequenceNormLiminf := by
  intro 𝕜 E _ _ _ s x hs
  obtain ⟨C, _, hC⟩ := weak_sequence_bounded 𝕜 E s x hs
  obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional 𝕜 E x
  have hconv := (weak_evaluation_tendsto 𝕜 E s x hs f).norm
  have hnorm : ‖f x‖ = ‖x‖ := by
    rw [hfx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]
  rw [← hnorm, ← hconv.liminf_eq]
  apply Filter.liminf_le_liminf
  · exact Eventually.of_forall fun n =>
      (f.le_opNorm (s n)).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hf (norm_nonneg (s n)))
  · exact hconv.isBoundedUnder_ge
  · have hb : atTop.IsBoundedUnder (· ≤ ·) (fun n => ‖s n‖) :=
      ⟨C, show ∀ᶠ n : ℕ in atTop, ‖s n‖ ≤ C from Eventually.of_forall hC⟩
    exact hb.isCobounded_flip

theorem weakStar_sequence_bounded : Spec.WeakStarSequenceBounded :=
  WeakstarSequenceBounds.weakStar_sequence_bounded

theorem weakStar_sequence_norm_liminf : Spec.WeakStarSequenceNormLiminf :=
  WeakstarSequenceBounds.weakStar_sequence_norm_liminf

/-- Compact scalar images give pointwise bounds for the evaluations indexed by K. -/
theorem weak_compact_norm_bounded : Spec.WeakCompactNormBounded := by
  intro 𝕜 E _ _ _ K hK
  obtain ⟨C, hC, hb⟩ := norm_bound_of_scalar_bounds 𝕜 E K (fun x => x.val) (by
    intro f
    have hImage : IsCompact (f '' K) := @IsCompact.image E 𝕜
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      inferInstance K f hK (weak_evaluation_continuous 𝕜 E f)
    obtain ⟨B, hB⟩ := hImage.isBounded.exists_norm_le
    exact ⟨B, fun x => hB _ (Set.mem_image_of_mem f x.property)⟩)
  exact ⟨C, hC, fun x hx => hb ⟨x, hx⟩⟩

end
end ExpandedFA.P1.C12BoundedSequences
