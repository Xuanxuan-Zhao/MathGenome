import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14BallCharacterization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Reflexive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Goldstine
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Embedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12NormLsc
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! Reflexivity and topological weak compactness of the closed unit ball.
Alaoglu and the canonical weak embedding prove compactness in the forward
direction. In the reverse direction compactness makes the image weak-star
closed, so Goldstine fills the bidual ball; scaling then fills the bidual.
-/
namespace ExpandedFA.P1.C14BallCharacterization
universe u v
open Set
noncomputable section

/-- An onto canonical isometry maps each centered closed ball onto the
corresponding bidual ball. -/
lemma canonicalEvaluation_image_norm_ball (𝕜 : Type u) (E : Type v)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (h : C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E) (r : ℝ) :
    C04CanonicalMap.canonicalEvaluation 𝕜 E '' {x : E | ‖x‖ ≤ r} =
      {ξ : ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) | ‖ξ‖ ≤ r} := by
  ext ξ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (C05BidualIsometry.canonicalEvaluation_norm 𝕜 E x).le.trans hx
  · intro hξ
    obtain ⟨x, rfl⟩ := h ξ
    exact ⟨x, (C05BidualIsometry.canonicalEvaluation_norm 𝕜 E x).ge.trans hξ, rfl⟩

/-- Every centered closed norm ball in a reflexive space is weakly compact.
This direction does not require a separate completeness assumption. -/
lemma reflexive_weakCompact_norm_ball (𝕜 : Type u) (E : Type v)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (h : C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E) (r : ℝ) (hr : 0 ≤ r) :
    @IsCompact E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      {x : E | ‖x‖ ≤ r} := by
  let V := E →L[𝕜] 𝕜
  let D := ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
  let J : E → D := C04CanonicalMap.canonicalEvaluation 𝕜 E
  let tD := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 V
  let tE := C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
  have he : @Topology.IsEmbedding E D tE tD J :=
    C13Embedding.canonicalEvaluation_weak_embedding 𝕜 E
  have hc : @IsCompact D tD {ξ : D | ‖ξ‖ ≤ r} := by
    simpa only [sub_zero] using
      C13Alaoglu.weakStar_closedBall_isCompact 𝕜 V 0 r hr
  let : TopologicalSpace E := tE
  let : TopologicalSpace D := tD
  apply he.isCompact_iff.mpr
  rw [show J '' {x : E | ‖x‖ ≤ r} = {ξ : D | ‖ξ‖ ≤ r} from
    canonicalEvaluation_image_norm_ball 𝕜 E h r]
  exact hc

/-- A weakly compact unit ball makes the canonical image closed in the
Hausdorff weak-star bidual. Goldstine and scalar normalization give surjectivity. -/
lemma weakCompact_norm_unitBall_reflexive (𝕜 : Type u) (E : Type v)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hc : @IsCompact E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      {x : E | ‖x‖ ≤ 1}) : C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E := by
  let V := E →L[𝕜] 𝕜
  let D := ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
  let J : E → D := C04CanonicalMap.canonicalEvaluation 𝕜 E
  let e : D ≃ₗ[𝕜] WeakDual 𝕜 V := StrongDual.toWeakDual
  let tD := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 V
  let tE := C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
  have he : @Topology.IsEmbedding E D tE tD J :=
    C13Embedding.canonicalEvaluation_weak_embedding 𝕜 E
  have heD : @Topology.IsEmbedding D (WeakDual 𝕜 V)
      tD inferInstance e := ⟨⟨C12WeakStar.weakStarTopology_native 𝕜 V⟩, e.injective⟩
  have hg : @closure D tD (J '' {x : E | ‖x‖ ≤ 1}) =
      {ξ : D | ‖ξ‖ ≤ 1} := C14Goldstine.goldstine_density 𝕜 E
  let : TopologicalSpace E := tE
  let : TopologicalSpace D := tD
  let : T2Space D := heD.t2Space
  have hclosed : IsClosed (J '' {x : E | ‖x‖ ≤ 1}) :=
    (he.isCompact_iff.mp hc).isClosed
  have hball : ∀ ξ : D, ‖ξ‖ ≤ 1 → ∃ x : E, ‖x‖ ≤ 1 ∧ J x = ξ := by
    intro ξ hξ
    have : ξ ∈ J '' {x : E | ‖x‖ ≤ 1} := by
      rw [← hclosed.closure_eq, hg]
      exact hξ
    exact this
  intro ξ
  by_cases hξ : ξ = 0
  · exact ⟨0, by simp [hξ]⟩
  · obtain ⟨x, _hx, hx⟩ := hball ((‖ξ‖⁻¹ : 𝕜) • ξ)
      (norm_smul_inv_norm (𝕜 := 𝕜) (x := ξ) hξ).le
    refine ⟨(‖ξ‖ : 𝕜) • x, ?_⟩
    rw [map_smul]
    change (‖ξ‖ : 𝕜) • J x = ξ
    rw [hx, smul_smul, mul_inv_cancel₀
      (RCLike.ofReal_ne_zero.mpr ((norm_ne_zero_iff (a := ξ)).mpr hξ)), one_smul]

/-- The first two assertions of the Banach-space ball characterization. -/
theorem reflexive_iff_weakCompact_unitBall :
    Spec.ReflexiveIffCompactBall.{u, v} := by
  intro 𝕜 E _ _ _ _
  constructor
  · intro h
    exact reflexive_weakCompact_norm_ball 𝕜 E h 1 zero_le_one
  · exact weakCompact_norm_unitBall_reflexive 𝕜 E

/-- The unit-ball formulation is equivalent to compactness of all bounded
weakly closed sets. No nonempty-set restriction is needed. -/
theorem weakCompact_unitBall_iff_closed_bounded :
    Spec.CompactBallIffClosedBounded.{u, v} := by
  intro 𝕜 E _ _ _ _
  constructor
  · intro hc A hA hclosed
    obtain ⟨r, hr, hAr⟩ := hA.exists_pos_norm_le
    have hb := reflexive_weakCompact_norm_ball 𝕜 E
      (weakCompact_norm_unitBall_reflexive 𝕜 E hc) r hr.le
    let : TopologicalSpace E := C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
    exact hb.of_isClosed_subset hclosed hAr
  · intro h
    apply h {x : E | ‖x‖ ≤ 1}
    · exact isBounded_iff_forall_norm_le.mpr ⟨1, fun _ hx => hx⟩
    · simpa only [sub_zero] using C12NormLsc.weak_closed_balls 𝕜 E 0 1

end
end ExpandedFA.P1.C14BallCharacterization
