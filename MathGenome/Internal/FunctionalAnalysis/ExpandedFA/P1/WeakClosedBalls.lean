import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakClosedBalls
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry

/-!
Closed norm balls are intersections of closed scalar-test constraints.
For vectors, the converse uses the isometry of canonical evaluation;
for dual vectors it is the operator norm bound. Negative-radius balls
are empty. This covers all centers without any completeness assumption.
-/

namespace ExpandedFA.P1.WeakClosedBalls

universe u v
noncomputable section

/-- Arbitrary closed norm constraints on continuous scalar tests. -/
private theorem isClosed_norm_constraints {X K I : Type*} [NormedAddCommGroup K]
    (t : TopologicalSpace X) (g : I → X → K)
    (hg : ∀ i, @Continuous X K t inferInstance (g i)) (a : I → K) (b : I → ℝ) :
    @IsClosed X t {x : X | ∀ i, ‖g i x - a i‖ ≤ b i} := by
  let : TopologicalSpace X := t
  have heq : {x : X | ∀ i, ‖g i x - a i‖ ≤ b i} =
      ⋂ i, {x : X | ‖g i x - a i‖ ≤ b i} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter fun i =>
    isClosed_le ((hg i).sub continuous_const).norm continuous_const

/-- A negative sublevel of a norm distance is empty, for any topology. -/
private theorem norm_sublevel_empty {X : Type*} [SeminormedAddCommGroup X]
    (c : X) {r : ℝ} (hr : ¬ 0 ≤ r) : {x : X | ‖x - c‖ ≤ r} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hr (le_trans (norm_nonneg (x - c)) hx)

theorem weak_closed_balls : Spec.WeakClosedBalls.{u, v} := by
  intro 𝕜 E _ _ _ c r
  by_cases hr : 0 ≤ r
  · have hc (f : E →L[𝕜] 𝕜) :
        @Continuous E 𝕜
          (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
            (topDualPairing 𝕜 E)) inferInstance f :=
      (dualPairTopology_coarsest 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
        (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
          (topDualPairing 𝕜 E))).mpr le_rfl f
    have heq : {x : E | ‖x - c‖ ≤ r} =
        {x : E | ∀ f : E →L[𝕜] 𝕜, ‖f x - f c‖ ≤ r * ‖f‖} := by
      ext x
      constructor
      · intro hx f
        calc
          ‖f x - f c‖ = ‖f (x - c)‖ := by rw [map_sub]
          _ ≤ ‖f‖ * ‖x - c‖ := f.le_opNorm _
          _ ≤ ‖f‖ * r := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
          _ = r * ‖f‖ := mul_comm _ _
      · intro hx
        change ‖x - c‖ ≤ r
        rw [← C05BidualIsometry.canonicalEvaluation_norm 𝕜 E (x - c)]
        apply ContinuousLinearMap.opNorm_le_bound _ hr
        intro f
        change ‖f (x - c)‖ ≤ r * ‖f‖
        simpa only [map_sub] using hx f
    rw [heq]
    exact isClosed_norm_constraints _ (fun (f : E →L[𝕜] 𝕜) (x : E) => f x)
      hc (fun f => f c) (fun f => r * ‖f‖)
  · rw [norm_sublevel_empty c hr]
    exact @isClosed_empty E
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))

theorem weakStar_closed_balls : Spec.WeakStarClosedBalls.{u, v} := by
  intro 𝕜 E _ _ _ c r
  by_cases hr : 0 ≤ r
  · have hc (x : E) :
        @Continuous (E →L[𝕜] 𝕜) 𝕜 (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
          inferInstance (fun f => f x) :=
      (C12WeakStar.weakStarTopology_evaluation_coarsest 𝕜 E
        (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)).mpr le_rfl x
    have heq : {f : E →L[𝕜] 𝕜 | ‖f - c‖ ≤ r} =
        {f : E →L[𝕜] 𝕜 | ∀ x : E, ‖f x - c x‖ ≤ r * ‖x‖} := by
      ext f
      exact ContinuousLinearMap.opNorm_le_iff hr
    rw [heq]
    exact isClosed_norm_constraints _ (fun (x : E) (f : E →L[𝕜] 𝕜) => f x) hc
      (fun x => c x) (fun x => r * ‖x‖)
  · rw [norm_sublevel_empty c hr]
    exact @isClosed_empty (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)

end
end ExpandedFA.P1.WeakClosedBalls
