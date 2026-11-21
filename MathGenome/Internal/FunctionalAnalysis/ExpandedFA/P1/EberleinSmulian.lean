import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.EberleinSmulian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SeparableWeakCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.WeakSequentialRelativeCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.WeakClusterToSubsequence

/-! Eberlein–Šmulian for arbitrary real or complex normed spaces. -/
namespace ExpandedFA.P1.EberleinSmulian

universe u v
open Filter Set TopologicalSpace
open scoped Topology
noncomputable section

/-- Restrict a sequence to its separable norm-closed linear span. Its
intersection with the compact weak closure is compact and metrizable. -/
theorem compact_implies_subsequences : Spec.CompactImpliesSubsequences.{u,v} := by
  intro 𝕜 E _ _ _ A hA s hs
  let Y : Submodule 𝕜 E := (Submodule.span 𝕜 (Set.range s)).topologicalClosure
  have hYs : ∀ n, s n ∈ Y := fun n =>
    (Submodule.span 𝕜 (Set.range s)).le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self n))
  have hYsep : IsSeparable (Y : Set E) := by
    rw [show (Y : Set E) = closure (Submodule.span 𝕜 (Set.range s) : Set E) from
      Submodule.topologicalClosure_coe _]
    exact (Set.countable_range s).isSeparable.span.closure
  letI : SeparableSpace Y := hYsep.separableSpace
  have hYclosed := C12ConvexClosure.isWeaklyClosed_of_isClosed_submodule 𝕜 E Y
    (Submodule.isClosed_topologicalClosure _)
  let K : Set E := @closure E (Spec.weakTopology 𝕜 E) A ∩ (Y : Set E)
  have hmetr := SeparableWeakCompact.weak_compact_metrizable 𝕜 E Y K
    (fun _ hx => hx.2)
  letI : TopologicalSpace E := Spec.weakTopology 𝕜 E
  have hK : IsCompact K := hA.inter_right hYclosed
  letI : MetrizableSpace K := hmetr hK
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let t : ℕ → K := fun n => ⟨s n, subset_closure (hs n), hYs n⟩
  obtain ⟨x, r, hr, hconv⟩ := SeqCompactSpace.tendsto_subseq t
  exact ⟨x.val, r, hr, continuous_subtype_val.tendsto x |>.comp hconv⟩

/-- The relative compactness, subsequence and cluster-point formulations. -/
theorem relative_equivalences : Spec.RelativeEquivalences.{u,v} := by
  intro 𝕜 E _ _ _ A
  refine ⟨⟨compact_implies_subsequences 𝕜 E A,
    WeakSequentialRelativeCompact.weak_closure_isCompact 𝕜 E A⟩, ⟨?_, ?_⟩⟩
  · intro hA s hs
    obtain ⟨x, r, hr, hconv⟩ := hA s hs
    letI : TopologicalSpace E := Spec.weakTopology 𝕜 E
    exact ⟨x, hconv.mapClusterPt.of_comp hr.tendsto_atTop⟩
  · exact WeakClusterToSubsequence.cluster_implies_subsequence 𝕜 E A

/-- Closedness places all subsequential limits inside the set. Countable
compactness supplies cluster points, so the relative equivalence applies. -/
theorem closed_equivalences : Spec.ClosedEquivalences.{u,v} := by
  intro 𝕜 E _ _ _ A
  have heq := relative_equivalences 𝕜 E A
  letI : TopologicalSpace E := Spec.weakTopology 𝕜 E
  intro hclosed
  have hseq : IsCompact A ↔ IsSeqCompact A := by
    constructor
    · intro hA s hs
      obtain ⟨x, r, hr, hconv⟩ := heq.1.mp (hclosed.closure_eq.symm ▸ hA) s hs
      exact ⟨x, hclosed.mem_of_tendsto hconv (.of_forall fun n => hs (r n)),
        r, hr, hconv⟩
    · intro hA
      rw [← hclosed.closure_eq]
      apply heq.1.mpr
      intro s hs
      obtain ⟨x, _, r, hr, hconv⟩ := hA hs
      exact ⟨x, r, hr, hconv⟩
  refine ⟨hseq, ⟨IsCompact.isCountablyCompact, ?_⟩⟩
  intro hA
  rw [← hclosed.closure_eq]
  apply heq.1.mpr
  apply heq.2.mpr
  intro s hs
  obtain ⟨x, _, hx⟩ := hA.seq_clusterPt s (.of_forall hs)
  exact ⟨x, hx⟩

/-- Applying the closed-set result to the weak closure gives exactly the
source's definition of relative countable compactness. -/
theorem relative_countable_equivalence : Spec.RelativeCountableEquivalence.{u,v} := by
  intro 𝕜 E _ _ _ A
  exact (closed_equivalences 𝕜 E
    (@closure E (Spec.weakTopology 𝕜 E) A)
    (@isClosed_closure E (Spec.weakTopology 𝕜 E) A)).2

end
end ExpandedFA.P1.EberleinSmulian
