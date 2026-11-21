import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.UniversalContinuousEmbedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming

/-!
The universal evaluation embedding, `fa2:p1:banach-stone`.
Evaluation is continuous for the weak-star topology. Its supremum norm
is at most ‖x‖ by the operator norm bound, and a norming functional
gives the reverse inequality, also for x = 0. No completeness is used.
-/

namespace ExpandedFA.Supplements.UniversalContinuousEmbedding

universe u v
noncomputable section

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The native weak-star subspace topology agrees with the shared one. -/
theorem dualUnitBall_topology : Spec.DomainTopology.{u, v} := by
  intro 𝕜 E _ _ _
  rw [P1.C12WeakStar.weakStarTopology_native 𝕜 E, induced_compose]
  rfl

/-- The dual unit ball is compact, without requiring E to be complete. -/
theorem dualUnitBall_compact : CompactSpace (DualUnitBall 𝕜 E) := by
  have hset : {f : WeakDual 𝕜 E | ‖WeakDual.toStrongDual f‖ ≤ 1} =
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : E →L[𝕜] 𝕜) 1 := by
    ext f
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      Set.mem_ofPred_eq]
  apply isCompact_iff_compactSpace.mp
  change IsCompact {f : WeakDual 𝕜 E | ‖WeakDual.toStrongDual f‖ ≤ 1}
  rw [hset]
  exact WeakDual.isCompact_closedBall (0 : E →L[𝕜] 𝕜) 1

/-- Evaluation at a vector, as a continuous function on the weak-star ball. -/
def evaluation (x : E) : C(DualUnitBall 𝕜 E, 𝕜) where
  toFun f := WeakDual.toStrongDual f.val x
  continuous_toFun := (WeakDual.eval_continuous x).comp continuous_subtype_val

@[simp]
theorem evaluation_apply (x : E) (f : DualUnitBall 𝕜 E) :
    evaluation x f = WeakDual.toStrongDual f.val x := rfl

/-- Evaluation is linear over the original scalar field, including ℂ. -/
def evaluationLinearMap : E →ₗ[𝕜] C(DualUnitBall 𝕜 E, 𝕜) where
  toFun := evaluation
  map_add' x y := by
    ext f
    exact map_add (WeakDual.toStrongDual f.val) x y
  map_smul' a x := by
    ext f
    exact map_smul (WeakDual.toStrongDual f.val) a x

variable [CompactSpace (DualUnitBall 𝕜 E)]

/-- The supremum norm of evaluation is exactly the original vector norm. -/
theorem norm_evaluation (x : E) : ‖evaluation (𝕜 := 𝕜) x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
    intro f
    exact ((WeakDual.toStrongDual f.val).le_opNorm x).trans
      ((mul_le_mul_of_nonneg_right f.property (norm_nonneg x)).trans_eq (one_mul _))
  · obtain ⟨f, hf, hfx⟩ := P1.C05Norming.norming_functional 𝕜 E x
    let b : DualUnitBall 𝕜 E := ⟨StrongDual.toWeakDual f, hf⟩
    have hbound := (evaluation (𝕜 := 𝕜) x).norm_coe_le_norm b
    change ‖f x‖ ≤ ‖evaluation (𝕜 := 𝕜) x‖ at hbound
    simpa only [hfx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)] using hbound

/-- The canonical scalar-linear isometry into continuous functions. -/
def evaluationEmbedding : E →ₗᵢ[𝕜] C(DualUnitBall 𝕜 E, 𝕜) where
  toLinearMap := evaluationLinearMap
  norm_map' := norm_evaluation

/-- Every normed space has the stated evaluation embedding on its
compact Hausdorff weak-star dual unit ball. -/
theorem universal_evaluation_embedding : Spec.UniversalEmbedding.{u, v} := by
  intro 𝕜 E _ _ _
  let := dualUnitBall_compact (𝕜 := 𝕜) (E := E)
  exact ⟨inferInstance, inferInstance, evaluationEmbedding, fun _ _ => rfl⟩

end
end ExpandedFA.Supplements.UniversalContinuousEmbedding
