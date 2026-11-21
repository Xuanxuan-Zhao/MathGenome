import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakstarSequenceBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness

/-!
Weak-star sequence bounds and weak-star closedness of dual norm balls.
Scalar convergence gives pointwise bounds; uniform boundedness applies on
precisely the Banach predual. For the liminf, compare each unit-vector
evaluation with the operator norm. Closedness follows independently from
intersections of closed scalar evaluation conditions.
-/

namespace ExpandedFA.P1.WeakstarSequenceBounds

universe u v
open Filter
open scoped Topology
noncomputable section

/-- Evaluation is continuous for σ(E′, E), with the original dual fixed. -/
theorem evaluation_continuous (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) :
    @Continuous (E →L[𝕜] 𝕜) 𝕜 (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      inferInstance (fun f => f x) := by
  rw [continuous_iff_le_induced, C12WeakStar.weakStarTopology_evaluations 𝕜 E]
  exact iInf_le _ x

/-- Convergence in the specified weak-star topology implies scalar convergence. -/
theorem evaluation_tendsto (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (s : ℕ → (E →L[𝕜] 𝕜)) (f : E →L[𝕜] 𝕜)
    (hs : Tendsto s atTop
      (@nhds (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) f))
    (x : E) : Tendsto (fun n => s n x) atTop (𝓝 (f x)) := by
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  exact ((evaluation_continuous 𝕜 E x).tendsto f).comp hs

theorem weakStar_sequence_bounded : Spec.SequenceBounded := by
  intro 𝕜 E _ _ _ _ s f hs
  apply C07UniformBoundedness.uniform_boundedness 𝕜 E 𝕜 ℕ s
  intro x
  obtain ⟨C, hC⟩ := (evaluation_tendsto 𝕜 E s f hs x).norm.bddAbove_range
  exact ⟨C, fun n => hC (Set.mem_range_self n)⟩

theorem weakStar_sequence_norm_liminf : Spec.SequenceNormLiminf := by
  intro 𝕜 E _ _ _ _ s f hs
  obtain ⟨C, _, hC⟩ := weakStar_sequence_bounded 𝕜 E s f hs
  have hb : atTop.IsBoundedUnder (· ≤ ·) (fun n => ‖s n‖) :=
    ⟨C, show ∀ᶠ n : ℕ in atTop, ‖s n‖ ≤ C from Eventually.of_forall hC⟩
  have hnonneg : 0 ≤ liminf (fun n => ‖s n‖) atTop :=
    le_liminf_of_le hb.isCobounded_flip (Eventually.of_forall fun n => norm_nonneg (s n))
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hnonneg
  intro x hx
  have hconv := (evaluation_tendsto 𝕜 E s f hs x).norm
  rw [← hconv.liminf_eq]
  apply Filter.liminf_le_liminf
  · exact Eventually.of_forall fun n => (s n).unit_le_opNorm x hx.le
  · exact hconv.isBoundedUnder_ge
  · exact hb.isCobounded_flip

theorem closed_dual_balls_weakStar_closed : Spec.ClosedDualBalls := by
  intro 𝕜 E _ _ _ f₀ r
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  change IsClosed (Metric.closedBall f₀ r)
  by_cases hr : 0 ≤ r
  · have hset : Metric.closedBall f₀ r =
        ⋂ x : E, {g : E →L[𝕜] 𝕜 | ‖g x - f₀ x‖ ≤ r * ‖x‖} := by
      ext g
      simp only [Metric.mem_closedBall, dist_eq_norm, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro hg x
        exact (g - f₀).le_of_opNorm_le hg x
      · intro hg
        exact ContinuousLinearMap.opNorm_le_bound (g - f₀) hr hg
    rw [hset]
    exact isClosed_iInter fun x =>
      isClosed_le (((evaluation_continuous 𝕜 E x).sub continuous_const).norm) continuous_const
  · rw [Metric.closedBall_eq_empty.mpr (lt_of_not_ge hr)]
    exact isClosed_empty

end
end ExpandedFA.P1.WeakstarSequenceBounds
