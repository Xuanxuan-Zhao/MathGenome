import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.TvsDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsQuotientTopology

/-! Topological vector-space quotients, paper.tex:1896–1914. -/

open Set Filter
open scoped Topology

namespace ExpandedFA.P1

theorem quotient_tvs : TvsQuotientTopologySpec.QuotientTVS := by
  intro 𝕜 E _ _ _ _ _ _ _ M _
  exact ⟨inferInstance, inferInstance⟩

theorem quotient_hausdorff : TvsQuotientTopologySpec.QuotientHausdorff := by
  intro 𝕜 E _ _ _ _ _ _ _ M hM
  let : IsClosed (M : Set E) := hM
  infer_instance

theorem quotient_projection_continuous_open :
    TvsQuotientTopologySpec.ProjectionContinuousOpen := by
  intro 𝕜 E _ _ _ _ _ _ _ M _
  exact ⟨M.continuous_mkQ, M.isOpenMap_mkQ⟩

theorem quotient_continuity_iff : TvsQuotientTopologySpec.UniversalContinuity := by
  intro 𝕜 E Y _ _ _ _ _ _ _ _ M _ f
  exact M.isQuotientMap_mkQ.continuous_iff

/-- Images of zero neighborhoods describe exactly the quotient neighborhood
filter. This does not require the submodule to be closed. -/
theorem quotient_map_nhds_zero {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (M : Submodule 𝕜 E) :
    Filter.map M.mkQ (𝓝 (0 : E)) = 𝓝 (0 : E ⧸ M) := by
  simpa only [map_zero] using M.isOpenQuotientMap_mkQ.map_nhds_eq (0 : E)

theorem quotient_locally_convex : TvsQuotientTopologySpec.QuotientLocallyConvex := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ M _ hconv
  let : LocallyConvexSpace ℝ E := hconv
  apply LocallyConvexSpace.ofBasisZero ℝ (E ⧸ M)
    (fun U : Set E => M.mkQ '' U)
    (fun U : Set E => U ∈ 𝓝 (0 : E) ∧ Convex ℝ U)
  · rw [← quotient_map_nhds_zero M]
    exact (LocallyConvexSpace.convex_basis_zero ℝ E).map M.mkQ
  · intro U hU
    exact hU.2.linear_image (M.mkQ.restrictScalars ℝ)

theorem quotient_countable_local_basis :
    TvsQuotientTopologySpec.QuotientCountableLocalBasis := by
  intro 𝕜 E _ _ _ _ _ _ _ M _ hcount
  let : (𝓝 (0 : E)).IsCountablyGenerated := hcount
  rw [← quotient_map_nhds_zero M]
  infer_instance

end ExpandedFA.P1
