import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.BanachAdjoints
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04DualMaps
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import Mathlib.Analysis.Normed.Module.DoubleDual

/-! Banach transposes and preadjoints. In the converse criterion, weak-star
representation recovers a vector T x in the original Y. Uniform boundedness
is then applied on the complete dual Y′, so X and Y need not be complete. -/

noncomputable section

namespace ExpandedFA.Compactness.BanachAdjoints

open ExpandedFA.P1

universe u v w

theorem transpose_apply : Spec.TransposeEvaluation.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ T f x
  rfl

theorem transpose_norm : Spec.TransposeNorm.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ T
  let U := C04Annihilators.banachTranspose 𝕜 X Y T
  apply le_antisymm (C04DualMaps.banachTranspose_norm_le 𝕜 X Y T)
  apply T.opNorm_le_bound (norm_nonneg U)
  intro x
  apply NormedSpace.norm_le_dual_bound 𝕜 (T x) (by positivity)
  intro f
  calc
    ‖f (T x)‖ = ‖U f x‖ := rfl
    _ ≤ ‖U f‖ * ‖x‖ := (U f).le_opNorm x
    _ ≤ (‖U‖ * ‖f‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (U.le_opNorm f) (norm_nonneg x)
    _ = (‖U‖ * ‖x‖) * ‖f‖ := by ring

theorem bidual_naturality : Spec.BidualNaturality.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ T
  ext x f
  rfl

section Preadjoint

variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

/-- Each scalar component of a weak-star continuous S is evaluation at an
actual vector of Y, by the weak representation theorem. -/
theorem exists_evaluation_vector
    (S : (Y →L[𝕜] 𝕜) →ₗ[𝕜] (X →L[𝕜] 𝕜))
    (hS : Continuous (fun f : WeakDual 𝕜 Y =>
      StrongDual.toWeakDual (S (WeakDual.toStrongDual f)))) (x : X) :
    ∃ y : Y, ∀ f : Y →L[𝕜] 𝕜, f y = S f x := by
  let l : WeakDual 𝕜 Y →L[𝕜] 𝕜 :=
    { toLinearMap := (ContinuousLinearMap.apply 𝕜 𝕜 x).toLinearMap.comp
        (S.comp WeakDual.toStrongDual.toLinearMap)
      cont := (WeakDual.eval_continuous x).comp hS }
  obtain ⟨y, hy⟩ := LinearMap.dualEmbedding_surjective (topDualPairing 𝕜 Y) l
  refine ⟨y, fun f => ?_⟩
  exact congrArg (fun g : WeakDual 𝕜 Y →L[𝕜] 𝕜 => g (StrongDual.toWeakDual f)) hy

/-- Uniform boundedness on Y′ turns the algebraic preadjoint into a
bounded map, even when both original spaces are incomplete. -/
theorem exists_bounded_preadjoint
    (S : (Y →L[𝕜] 𝕜) →ₗ[𝕜] (X →L[𝕜] 𝕜))
    (hS : Continuous (fun f : WeakDual 𝕜 Y =>
      StrongDual.toWeakDual (S (WeakDual.toStrongDual f)))) :
    ∃ T : X →L[𝕜] Y, ∀ (f : Y →L[𝕜] 𝕜) (x : X), f (T x) = S f x := by
  classical
  choose t ht using fun x : X => exists_evaluation_vector S hS x
  let T₀ : X →ₗ[𝕜] Y :=
    { toFun := t
      map_add' := by
        intro x z
        apply (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr
        intro f
        simp only [ht, map_add]
      map_smul' := by
        intro a x
        apply (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr
        intro f
        simp only [ht, map_smul, RingHom.id_apply] }
  have hT₀ (f : Y →L[𝕜] 𝕜) (x : X) : f (T₀ x) = S f x := ht x f
  let I := {x : X // ‖x‖ ≤ 1}
  let ev : I → (Y →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
    fun x => NormedSpace.inclusionInDoubleDual 𝕜 Y (T₀ x.val)
  have hpointwise (f : Y →L[𝕜] 𝕜) : ∃ C : ℝ, ∀ i, ‖ev i f‖ ≤ C := by
    refine ⟨‖S f‖, fun i => ?_⟩
    change ‖f (T₀ i.val)‖ ≤ ‖S f‖
    rw [hT₀]
    exact ((S f).le_opNorm i.val).trans
      (mul_le_of_le_one_right (norm_nonneg _) i.property)
  obtain ⟨C, _, hC⟩ := C07UniformBoundedness.uniform_boundedness
    𝕜 (Y →L[𝕜] 𝕜) 𝕜 I ev hpointwise
  have hball (x : X) (hx : x ∈ Metric.ball (0 : X) 1) : ‖T₀ x‖ ≤ C := by
    have heq : ‖ev ⟨x, (mem_ball_zero_iff.mp hx).le⟩‖ = ‖T₀ x‖ :=
      (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (T₀ x)
    exact heq ▸ hC ⟨x, (mem_ball_zero_iff.mp hx).le⟩
  let T : X →L[𝕜] Y :=
    T₀.mkContinuousOfExistsBound (T₀.bound_of_ball_bound zero_lt_one C hball)
  exact ⟨T, fun f x => hT₀ f x⟩

end Preadjoint

theorem preadjoint_iff_weakStar_continuous : Spec.PreadjointCriterion.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ S
  constructor
  · rintro ⟨T, rfl⟩
    apply WeakDual.continuous_of_continuous_eval
    intro x
    exact WeakDual.eval_continuous (T x)
  · intro hS
    obtain ⟨T, hT⟩ := exists_bounded_preadjoint S hS
    refine ⟨T, ?_⟩
    ext f x
    exact hT f x

end ExpandedFA.Compactness.BanachAdjoints
