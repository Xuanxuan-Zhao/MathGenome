import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24TopologyExample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24KreinMilman
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14BallCharacterization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01CompactBall
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
Example `fa2:p1:c24:topology-example`, paper.tex:5033–5046.
Riesz representation supplies reflexivity over either scalar field. The weak
ball characterization and Krein–Milman then apply to the original scalar-linear
dual, with real convex combinations. Norm compactness is ruled out separately
by the compact-ball criterion.
-/

set_option backward.isDefEq.respectTransparency false

universe u v
namespace ExpandedFA.P1.C24TopologyExample
noncomputable section

/-- Riesz representation identifies every scalar-linear bidual functional with
canonical evaluation, taking account of the conjugate linearity of `toDual`. -/
lemma hilbert_canonicalEvaluation_surjective (𝕜 : Type u) (H : Type v)
    [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] :
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 H := by
  intro ξ
  let R := InnerProductSpace.toDual 𝕜 H
  let g : H →L[𝕜] 𝕜 :=
    { toFun := fun x => star (ξ (R x))
      map_add' := by intro x y; simp
      map_smul' := by
        intro a x
        rw [R.map_smulₛₗ, map_smul]
        simp
      cont := continuous_star.comp (ξ.continuous.comp R.continuous) }
  obtain ⟨y, hy⟩ := R.surjective g
  refine ⟨y, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨x, rfl⟩ := R.surjective f
  have h := congrArg (fun k : H →L[𝕜] 𝕜 => k x) hy
  change inner 𝕜 y x = star (ξ (R x)) at h
  change inner 𝕜 x y = ξ (R x)
  rw [← inner_conj_symm x y, h]
  exact star_star _

/-- Weak compactness needs neither finite dimension nor separability. -/
theorem hilbert_unitBall_weakCompact : Spec.WeakCompactUnitBall.{u,v} := by
  intro 𝕜 H _ _ _ _ _hinf
  exact C14BallCharacterization.reflexive_weakCompact_norm_ball 𝕜 H
    (hilbert_canonicalEvaluation_surjective 𝕜 H) 1 zero_le_one

/-- The original Hilbert norm is strictly convex on the underlying real space. -/
theorem hilbert_unitBall_extremePoints : Spec.ExtremeUnitBall.{u,v} := by
  intro 𝕜 H _ _ _ _ hinf
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal 𝕜 H
  haveI : Nontrivial H := by
    by_contra h
    haveI : Subsingleton H := not_nontrivial_iff_subsingleton.mp h
    exact hinf inferInstance
  change extremePoints {x : H | ‖x‖ ≤ 1} = {x : H | ‖x‖ = 1}
  rw [extremePoints_eq_native]
  simpa only [Metric.closedBall, Metric.sphere, dist_zero_right] using
    (StrictConvexSpace.extremePoints_closedBall_eq_sphere (x := (0 : H)) (r := (1 : ℝ)))

/-- Krein–Milman in σ(H,H′), using the norm-continuous dual fixed before
introducing the weak topology on H. -/
theorem hilbert_unitBall_weakClosedConvexHull : Spec.WeakClosedConvexHull.{u,v} := by
  intro 𝕜 H _ _ _ _ hinf
  let V := H →L[𝕜] 𝕜
  let B : V →ₗ[𝕜] H →ₗ[𝕜] 𝕜 := topDualPairing 𝕜 H
  let t := C12DualPairSpec.DualPairTopologyValue 𝕜 H V B
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  letI : IsScalarTower ℝ 𝕜 H := IsScalarTower.restrictScalars ℝ 𝕜 H
  have hconv : Convex ℝ {x : H | ‖x‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      convex_closedBall (0 : H) (1 : ℝ)
  have hext := hilbert_unitBall_extremePoints 𝕜 H hinf
  have hc := hilbert_unitBall_weakCompact 𝕜 H hinf
  have ht : t = WeakBilin.instTopologicalSpace B.flip := by
    change TopologicalSpace.induced (id : H → H) (WeakBilin.instTopologicalSpace B.flip) = _
    exact @induced_id H (WeakBilin.instTopologicalSpace B.flip)
  have hgroup : @IsTopologicalAddGroup H t _ := by
    rw [ht]
    change @IsTopologicalAddGroup (WeakBilin B.flip)
      (WeakBilin.instTopologicalSpace B.flip) _
    infer_instance
  have hT2 : @T2Space H t := by
    rw [ht]
    change T2Space (WeakBilin B.flip)
    apply (WeakBilin.isEmbedding (B := B.flip) ?_).t2Space
    intro x y hxy
    by_contra hne
    obtain ⟨f, hf⟩ := C05BidualIsometry.dual_separates_points 𝕜 H x y hne
    exact hf (congrArg (fun l : V →ₗ[𝕜] 𝕜 => l f) hxy)
  have hsmul : @ContinuousSMul 𝕜 H _ _ t := by
    rw [ht]
    change @ContinuousSMul 𝕜 (WeakBilin B.flip) _ _
      (WeakBilin.instTopologicalSpace B.flip)
    infer_instance
  have hlc : @LocallyConvexSpace ℝ H _ _ _ _ t := by
    rw [ht]
    change LocallyConvexSpace ℝ (WeakBilin B.flip)
    infer_instance
  letI : TopologicalSpace H := t
  letI : IsTopologicalAddGroup H := hgroup
  letI : T2Space H := hT2
  letI : ContinuousSMul 𝕜 H := hsmul
  letI : ContinuousSMul ℝ H := IsScalarTower.continuousSMul 𝕜
  letI : LocallyConvexSpace ℝ H := hlc
  have hkm := real_krein_milman {x : H | ‖x‖ ≤ 1} ⟨0, by simp⟩ hc hconv
  change C24FacesSpec.extremePoints {x : H | ‖x‖ ≤ 1} = {x : H | ‖x‖ = 1} at hext
  rw [hext] at hkm
  exact hkm

/-- Norm compactness would force finite dimension. -/
theorem hilbert_unitBall_not_normCompact : Spec.NormNotCompact.{u,v} := by
  intro 𝕜 H _ _ _ _ hinf hc
  apply hinf
  apply (C01CompactBall.compact_closed_unit_ball_iff_finite_dimensional 𝕜 H).mp
  simpa only [Metric.closedBall, dist_zero_right] using hc

end
end ExpandedFA.P1.C24TopologyExample
