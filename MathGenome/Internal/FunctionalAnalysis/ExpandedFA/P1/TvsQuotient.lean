import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsQuotient
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.TvsQuotientTopology
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.TvsMetrization

/-! Closed subspaces and quotients of TVSs, paper.tex:1896–1930. -/

open Set Filter TopologicalSpace
open scoped Topology

universe u v w

namespace ExpandedFA.P1

theorem quotient_topological_properties : TvsQuotientSpec.TopologicalQuotient.{u, v, w} :=
  ⟨quotient_tvs, quotient_hausdorff, quotient_projection_continuous_open,
    quotient_continuity_iff, quotient_locally_convex, quotient_countable_local_basis⟩

theorem quotient_metrizable : TvsQuotientSpec.QuotientMetrizable := by
  intro 𝕜 E _ _ _ _ _ _ _ M hM hm
  let := hm
  let : T2Space (E ⧸ M) := quotient_hausdorff 𝕜 E M hM
  apply (tvs_metrizable_iff_countable_local_base 𝕜 (E ⧸ M)
    (quotient_tvs 𝕜 E M hM)).mpr
  exact quotient_countable_local_basis 𝕜 E M hM inferInstance

/-- Mathlib's group-quotient completeness theorem uses precisely the right
translation uniformities on the ambient space and its quotient. Its proof
lifts successive differences of a Cauchy subsequence along a shrinking local
base; thus it does not need a norm or local convexity. -/
theorem quotient_complete : TvsQuotientSpec.QuotientComplete := by
  intro 𝕜 E _ _ _ _ _ _ _ M _ hm hc
  let := hm
  let : TranslationComplete E := hc
  exact QuotientAddGroup.completeSpace_right' E M.toAddSubgroup

theorem complete_subspace_closed : TvsQuotientSpec.CompleteSubspaceClosed := by
  intro 𝕜 E _ _ _ _ _ _ _ M hc
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : IsUniformAddGroup M := .comap M.subtype
  have hcomp : CompleteSpace M := by
    unfold TranslationComplete at hc
    rwa [IsUniformAddGroup.rightUniformSpace_eq] at hc
  exact (completeSpace_coe_iff_isComplete.mp hcomp).isClosed

theorem closed_subspace_complete : TvsQuotientSpec.ClosedSubspaceComplete := by
  intro 𝕜 E _ _ _ _ _ _ _ M hM hc
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : IsUniformAddGroup M := .comap M.subtype
  let : CompleteSpace E := hc
  have hcomp : CompleteSpace M := hM.isComplete.completeSpace_coe
  unfold TranslationComplete
  rwa [IsUniformAddGroup.rightUniformSpace_eq]

theorem closed_subspace_fSpace : TvsQuotientSpec.ClosedSubspaceFSpace := by
  intro 𝕜 E _ _ _ _ hE M hM
  rcases hE with ⟨hadd, hsmul, hmet, hcomp⟩
  let := hadd
  let := hsmul
  let := hmet
  exact ⟨inferInstance, inferInstance, Topology.IsEmbedding.subtypeVal.metrizableSpace,
    closed_subspace_complete 𝕜 E M hM hcomp⟩

theorem closed_quotient_fSpace : TvsQuotientSpec.ClosedQuotientFSpace := by
  intro 𝕜 E _ _ _ _ hE M hM
  rcases hE with ⟨hadd, hsmul, hmet, hcomp⟩
  let := hadd
  let := hsmul
  let := hmet
  exact ⟨inferInstance, inferInstance, quotient_metrizable 𝕜 E M hM hmet,
    quotient_complete 𝕜 E M hM hmet hcomp⟩

theorem closed_subspace_frechet : TvsQuotientSpec.ClosedSubspaceFrechet := by
  intro 𝕜 E _ _ _ _ _ _ hE M hM
  let : LocallyConvexSpace ℝ E := hE.2
  refine ⟨closed_subspace_fSpace 𝕜 E hE.1 M hM, ?_⟩
  exact Topology.IsInducing.locallyConvexSpace
    (f := M.subtype.restrictScalars ℝ) .subtypeVal

theorem closed_quotient_frechet : TvsQuotientSpec.ClosedQuotientFrechet := by
  intro 𝕜 E _ _ _ _ _ _ hE M hM
  rcases hE with ⟨hF, hconv⟩
  have hquot := closed_quotient_fSpace 𝕜 E hF M hM
  obtain ⟨hadd, hsmul, hmet, hcomp⟩ := hF
  let := hadd
  let := hsmul
  let := hmet
  exact ⟨hquot,
    quotient_locally_convex 𝕜 E M hM hconv⟩

end ExpandedFA.P1
