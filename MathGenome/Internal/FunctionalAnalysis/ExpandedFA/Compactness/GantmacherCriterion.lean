import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.GantmacherCriterion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.BanachAdjoints
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Goldstine
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import Mathlib.Analysis.Normed.Module.DoubleDual

namespace ExpandedFA.Compactness.GantmacherCriterion
universe u v w
open Set Topology
noncomputable section
variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

private abbrev transpose (T : X →L[𝕜] Y) :=
  P1.C04Annihilators.banachTranspose 𝕜 X Y T

/-- The second transpose with the weak-star topologies on both biduals. -/
def secondTransposeWeak (T : X →L[𝕜] Y) :
    WeakDual 𝕜 (X →L[𝕜] 𝕜) →L[𝕜] WeakDual 𝕜 (Y →L[𝕜] 𝕜) where
  toLinearMap := StrongDual.toWeakDual.toLinearMap.comp
    (((transpose (transpose T))).toLinearMap.comp WeakDual.toStrongDual.toLinearMap)
  cont := WeakDual.continuous_of_continuous_eval fun f =>
    WeakDual.eval_continuous ((transpose T) f)

lemma secondTransposeWeak_naturality (T : X →L[𝕜] Y) :
    secondTransposeWeak T ∘ (NormedSpace.inclusionInDoubleDualWeak 𝕜 X) =
      (NormedSpace.inclusionInDoubleDualWeak 𝕜 Y) ∘ WeakSpace.map T := by
  rfl

/-- Goldstine transported from the shared topology to the native weak-star bidual. -/
lemma goldstine_native (ξ : (X →L[𝕜] 𝕜) →L[𝕜] 𝕜) (hξ : ‖ξ‖ ≤ 1) :
    StrongDual.toWeakDual ξ ∈ closure
      ((fun x : X => NormedSpace.inclusionInDoubleDualWeak 𝕜 X (toWeakSpace 𝕜 X x)) ''
        Metric.closedBall (0 : X) 1) := by
  letI : TopologicalSpace ((X →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (X →L[𝕜] 𝕜)
  have hi : IsInducing (StrongDual.toWeakDual (𝕜 := 𝕜) (E := X →L[𝕜] 𝕜)) :=
    ⟨P1.C12WeakStar.weakStarTopology_native 𝕜 (X →L[𝕜] 𝕜)⟩
  have hd := P1.C14Goldstine.goldstine_density 𝕜 X
  have hm : ξ ∈ closure
      (P1.C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 X '' {x : X | ‖x‖ ≤ 1}) := by
    exact hd.symm ▸ hξ
  rw [hi.closure_eq_preimage_closure_image] at hm
  have heq : StrongDual.toWeakDual ''
      (P1.C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 X '' {x : X | ‖x‖ ≤ 1}) =
      (fun x : X => NormedSpace.inclusionInDoubleDualWeak 𝕜 X (toWeakSpace 𝕜 X x)) ''
        Metric.closedBall (0 : X) 1 := by
    rw [image_image]
    congr 1
    ext x
    exact mem_closedBall_zero_iff.symm
  rw [heq] at hm
  exact hm

/-- Weak compactness puts the second transpose of the entire bidual unit ball
in the canonical image of the target. -/
lemma bidual_unitBall_range (T : X →L[𝕜] Y)
    (hT : IsCompact (closure ((fun x : X => toWeakSpace 𝕜 Y (T x)) ''
      Metric.closedBall (0 : X) 1)))
    (ξ : (X →L[𝕜] 𝕜) →L[𝕜] 𝕜) (hξ : ‖ξ‖ ≤ 1) :
    ∃ y : Y, (transpose (transpose T)) ξ = NormedSpace.inclusionInDoubleDual 𝕜 Y y := by
  let J := NormedSpace.inclusionInDoubleDualWeak 𝕜 Y
  let S := (fun x : X => toWeakSpace 𝕜 Y (T x)) '' Metric.closedBall (0 : X) 1
  have hc : IsClosed (J '' closure S) := (hT.image J.continuous).isClosed
  have hm := mem_closure_image (secondTransposeWeak T).continuous.continuousAt
    (goldstine_native ξ hξ)
  have hs : (secondTransposeWeak T) ''
      ((fun x : X => NormedSpace.inclusionInDoubleDualWeak 𝕜 X (toWeakSpace 𝕜 X x)) ''
        Metric.closedBall (0 : X) 1) ⊆ J '' closure S := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨toWeakSpace 𝕜 Y (T x), subset_closure ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨y, _, hy⟩ := closure_minimal hs hc hm
  refine ⟨(toWeakSpace 𝕜 Y).symm y, ?_⟩
  exact congrArg WeakDual.toStrongDual hy.symm

/-- Gantmacher's bidual range criterion, with the full bidual as domain. -/
theorem weaklyCompact_iff_bidualRange : Spec.WeakCompactIffBidualRange.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T
  constructor
  · intro hT ξ
    have hnative := (weaklyCompact_iff_weakSpace T).mp hT
    let a : 𝕜 := ((‖ξ‖ + 1 : ℝ) : 𝕜)
    have hpos : 0 < ‖ξ‖ + 1 := by positivity
    have hnorm : ‖a‖ = ‖ξ‖ + 1 := by
      simp only [a, RCLike.norm_ofReal, abs_of_pos hpos]
    have ha : a ≠ 0 := norm_pos_iff.mp (hnorm.symm ▸ hpos)
    let η := a⁻¹ • ξ
    have hη : ‖η‖ ≤ 1 := by
      dsimp only [η]
      calc
        ‖a⁻¹ • ξ‖ ≤ ‖a⁻¹‖ * ‖ξ‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ 1 := by
          rw [norm_inv, hnorm]
          exact (inv_mul_le_one₀ hpos).mpr (by linarith)
    obtain ⟨y, hy⟩ := bidual_unitBall_range T hnative η hη
    refine ⟨a • y, ?_⟩
    change (transpose (transpose T)) ξ = NormedSpace.inclusionInDoubleDual 𝕜 Y (a • y)
    have heq : a • η = ξ := by simp [η, smul_smul, ha]
    calc
      (transpose (transpose T)) ξ = (transpose (transpose T)) (a • η) := congrArg _ heq.symm
      _ = a • (transpose (transpose T)) η := map_smul _ _ _
      _ = a • NormedSpace.inclusionInDoubleDual 𝕜 Y y := congrArg (a • ·) hy
      _ = NormedSpace.inclusionInDoubleDual 𝕜 Y (a • y) := (map_smul _ _ _).symm
  · intro hr
    apply (weaklyCompact_iff_weakSpace T).mpr
    let J := NormedSpace.inclusionInDoubleDualWeak 𝕜 Y
    let U := secondTransposeWeak T
    let B : Set (WeakDual 𝕜 (X →L[𝕜] 𝕜)) :=
      WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1
    let S := (fun x : X => toWeakSpace 𝕜 Y (T x)) '' Metric.closedBall (0 : X) 1
    have hcB : IsCompact B := WeakDual.isCompact_closedBall 0 1
    have hc : IsCompact (U '' B) := hcB.image U.continuous
    have hsub : U '' B ⊆ range J := by
      rintro _ ⟨ξ, _, rfl⟩
      obtain ⟨y, hy⟩ := hr (WeakDual.toStrongDual ξ)
      refine ⟨toWeakSpace 𝕜 Y y, ?_⟩
      apply WeakDual.toStrongDual.injective
      exact hy.symm
    haveI : T2Space (WeakSpace 𝕜 Y) :=
      (NormedSpace.isEmbedding_inclusionInDoubleDualWeak 𝕜 Y).t2Space
    have hK : IsCompact (J ⁻¹' (U '' B)) :=
      (NormedSpace.isEmbedding_inclusionInDoubleDualWeak 𝕜 Y).isInducing.isCompact_preimage' hc hsub
    have hS : S ⊆ J ⁻¹' (U '' B) := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨NormedSpace.inclusionInDoubleDualWeak 𝕜 X (toWeakSpace 𝕜 X x), ?_, rfl⟩
      change NormedSpace.inclusionInDoubleDual 𝕜 X x ∈ Metric.closedBall 0 1
      exact (@mem_closedBall_zero_iff ((X →L[𝕜] 𝕜) →L[𝕜] 𝕜)
        inferInstance (NormedSpace.inclusionInDoubleDual 𝕜 X x) 1).mpr
        ((NormedSpace.double_dual_bound 𝕜 X x).trans (mem_closedBall_zero_iff.mp hx))
    exact hK.of_isClosed_subset isClosed_closure (closure_minimal hS hK.isClosed)

theorem bidualRange_iff_adjoint_continuous :
    Spec.BidualRangeIffAdjointContinuity.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T
  constructor
  · intro h
    apply WeakBilin.continuous_of_continuous_eval
    intro ξ
    obtain ⟨y, hy⟩ := h ξ
    have heq : (fun f : WeakDual 𝕜 Y => ξ ((transpose T) (WeakDual.toStrongDual f))) =
        (fun f : WeakDual 𝕜 Y => f y) := by
      funext f
      exact congrArg (fun g : (Y →L[𝕜] 𝕜) →L[𝕜] 𝕜 => g (WeakDual.toStrongDual f)) hy
    change Continuous (fun f : WeakDual 𝕜 Y => ξ ((transpose T) (WeakDual.toStrongDual f)))
    rw [heq]
    exact WeakDual.eval_continuous y
  · intro h ξ
    let l : WeakDual 𝕜 Y →L[𝕜] 𝕜 :=
      { toLinearMap := ξ.toLinearMap.comp
          ((transpose T).toLinearMap.comp WeakDual.toStrongDual.toLinearMap)
        cont := (WeakBilin.eval_continuous (topDualPairing 𝕜 (X →L[𝕜] 𝕜)).flip ξ).comp h }
    obtain ⟨y, hy⟩ := LinearMap.dualEmbedding_surjective (topDualPairing 𝕜 Y) l
    refine ⟨y, ?_⟩
    ext f
    exact (congrArg (fun g : WeakDual 𝕜 Y →L[𝕜] 𝕜 => g (StrongDual.toWeakDual f)) hy).symm

end
end ExpandedFA.Compactness.GantmacherCriterion
