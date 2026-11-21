import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.CompleteContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.CompactWeakSequences
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EberleinSmulian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Schur
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import Mathlib.Analysis.LocallyConvex.WeakSpace

namespace ExpandedFA.Compactness.CompleteContinuity

universe u v w
open Filter Set
open scoped Topology ENNReal
noncomputable section

private theorem weak_t2 (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    @T2Space X (P1.EberleinSmulian.Spec.weakTopology 𝕜 X) := by
  change @T2Space X (TopologicalSpace.induced (toWeakSpace 𝕜 X)
    (instTopologicalSpaceWeakSpace 𝕜 X))
  exact @Topology.IsEmbedding.t2Space X (WeakSpace 𝕜 X)
    (TopologicalSpace.induced (toWeakSpace 𝕜 X) (instTopologicalSpaceWeakSpace 𝕜 X))
    (instTopologicalSpaceWeakSpace 𝕜 X) inferInstance (toWeakSpace 𝕜 X)
    ((toWeakSpace 𝕜 X).injective.isEmbedding_induced)

/-- Eberlein–Šmulian supplies subsequences with limits inside a compact set. -/
private theorem weak_compact_seqCompact (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (K : Set X)
    (hK : @IsCompact X (P1.EberleinSmulian.Spec.weakTopology 𝕜 X) K) :
    @IsSeqCompact X (P1.EberleinSmulian.Spec.weakTopology 𝕜 X) K := by
  have hc : @IsClosed X (P1.EberleinSmulian.Spec.weakTopology 𝕜 X) K :=
    @IsCompact.isClosed X (P1.EberleinSmulian.Spec.weakTopology 𝕜 X)
      (weak_t2 𝕜 X) K hK
  exact (P1.EberleinSmulian.closed_equivalences 𝕜 X K hc).1.mp hK

/-- Sequential complete continuity in fact makes the image itself compact. -/
theorem image_isCompact_of_completelyContinuous
    {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y)
    (hT : IsCompletelyContinuous T) (K : Set X)
    (hK : @IsCompact X (P1.EberleinSmulian.Spec.weakTopology 𝕜 X) K) :
    IsCompact (T '' K) := by
  apply IsSeqCompact.isCompact
  intro s hs
  choose x hx hxs using hs
  obtain ⟨a, ha, r, hr, hlim⟩ := weak_compact_seqCompact 𝕜 X K hK hx
  refine ⟨T a, mem_image_of_mem T ha, r, hr, ?_⟩
  have ht := hT (x ∘ r) a ((weak_convergence_iff_tests (x ∘ r) a).mp hlim)
  simpa only [Function.comp_def, hxs] using ht

theorem set_sequence_equivalence : Spec.SetSequenceEquivalence.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ T
  constructor
  · intro hT s x hs
    have hweak := (weak_convergence_iff_tests s x).mpr hs
    have hK : @IsCompact X (P1.EberleinSmulian.Spec.weakTopology 𝕜 X)
        (insert x (range s)) := @Tendsto.isCompact_insert_range X
          (P1.EberleinSmulian.Spec.weakTopology 𝕜 X) s x hweak
    have hnorm := hT (insert x (range s)) hK
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨y, _, r, hr, hlim⟩ := hnorm.tendsto_subseq (fun n =>
      subset_closure (mem_image_of_mem T (mem_insert_of_mem x (mem_range_self (ns n)))))
    have hy : y = T x := by
      apply (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr
      intro f
      exact tendsto_nhds_unique ((f.continuous.tendsto y).comp hlim)
        ((hs (f.comp T)).comp (hns.comp hr.tendsto_atTop))
    exact ⟨r, hy ▸ hlim⟩
  · intro hT K hK
    exact (image_isCompact_of_completelyContinuous T hT K hK).closure

theorem compact_completelyContinuous : Spec.CompactCompletelyContinuous.{u,v,w} :=
  CompactWeakSequences.compact_completelyContinuous

/-- Surjectivity and isometry of J identify the unit ball with the bidual ball.
Pull back Alaoglu compactness through the accepted weak embedding. -/
theorem reflexive_closedBall_weaklyCompact
    (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (hX : P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 X) :
    @IsCompact X (P1.EberleinSmulian.Spec.weakTopology 𝕜 X)
      (Metric.closedBall (0 : X) 1) := by
  let J := P1.C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 X
  have he := P1.C13Embedding.canonicalEvaluation_weak_embedding 𝕜 X
  have hb := P1.C13Alaoglu.banach_alaoglu 𝕜 (X →L[𝕜] 𝕜)
  have hi := @Topology.IsEmbedding.isInducing X ((X →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    J (P1.EberleinSmulian.Spec.weakTopology 𝕜 X)
    (P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (X →L[𝕜] 𝕜)) he
  have hpre := @Topology.IsInducing.isCompact_preimage' X
    ((X →L[𝕜] 𝕜) →L[𝕜] 𝕜) (P1.EberleinSmulian.Spec.weakTopology 𝕜 X)
    (P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (X →L[𝕜] 𝕜)) J hi _ hb
    (fun y _ => hX y)
  have heq : J ⁻¹' {f : (X →L[𝕜] 𝕜) →L[𝕜] 𝕜 | ‖f‖ ≤ 1} =
      Metric.closedBall (0 : X) 1 := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    rw [show ‖J x‖ = ‖x‖ from P1.C05BidualIsometry.canonicalEvaluation_norm 𝕜 X x]
  exact heq ▸ hpre

theorem reflexive_equivalence : Spec.ReflexiveEquivalence.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ hX T
  constructor
  · intro hT
    exact (set_sequence_equivalence 𝕜 X Y T).mpr hT
      (Metric.closedBall 0 1) (reflexive_closedBall_weaklyCompact 𝕜 X hX)
  · exact compact_completelyContinuous 𝕜 X Y T

/-- Unit coordinate vectors stay at least unit distance apart, contradicting
any norm-convergent subsequence of the compact unit ball. -/
theorem l1_identity_not_compact (𝕜 : Type u) [RCLike 𝕜] :
    ¬ IsCompactLinearMap
      (ContinuousLinearMap.id 𝕜 (P1.C01SequenceSpaces.SequenceLp 𝕜 1)).toLinearMap := by
  intro h
  let e : ℕ → P1.C01SequenceSpaces.SequenceLp 𝕜 1 := fun n => lp.single 1 n 1
  have he (n : ℕ) : e n ∈ Metric.closedBall (0 : P1.C01SequenceSpaces.SequenceLp 𝕜 1) 1 := by
    simp [e, Metric.mem_closedBall, lp.norm_single]
  have hK : IsCompact (closure (Metric.closedBall
      (0 : P1.C01SequenceSpaces.SequenceLp 𝕜 1) 1)) := by
    change IsCompact (closure (id '' Metric.closedBall
      (0 : P1.C01SequenceSpaces.SequenceLp 𝕜 1) 1)) at h
    simpa only [image_id] using h
  obtain ⟨a, _, r, hr, ht⟩ := hK.tendsto_subseq (fun n => subset_closure (he n))
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ht.cauchySeq 1 zero_lt_one
  have hlt := hN N le_rfl (N+1) (Nat.le_succ N)
  have hne : r N ≠ r (N+1) := ne_of_lt (hr (Nat.lt_succ_self N))
  have hge := lp.norm_apply_le_norm (by simp : (1 : ℝ≥0∞) ≠ 0)
    (e (r N) - e (r (N+1))) (r N)
  have hsep : 1 ≤ dist (e (r N)) (e (r (N+1))) := by
    simpa [e, dist_eq_norm, lp.coeFn_sub, lp.single_apply, hne] using hge
  exact (not_lt_of_ge hsep) hlt

theorem l1_counterexample : Spec.L1Counterexample.{u} := by
  intro 𝕜 _
  have hc : IsCompletelyContinuous
      (ContinuousLinearMap.id 𝕜 (P1.C01SequenceSpaces.SequenceLp 𝕜 1)) := by
    intro s x hs
    exact P1.Schur.schur_property 𝕜 s x hs
  refine ⟨hc, l1_identity_not_compact 𝕜, ?_⟩
  intro hr
  exact l1_identity_not_compact 𝕜
    ((reflexive_equivalence 𝕜 _ _ hr _).mp hc)

end
end ExpandedFA.Compactness.CompleteContinuity
