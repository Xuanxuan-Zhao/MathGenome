import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.KreinSmulianIncomplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02Completion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12InitialProperties
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Extend

namespace ExpandedFA.P1.KreinSmulianIncomplete

universe u v
open UniformSpace Topology
noncomputable section

/-- Canonical evaluation after extension to the completion. -/
def completionEvaluation : Spec.EvaluationType := Spec.EvaluationValue

/-- The hyperplane attached to a missing completion point. -/
def completionHyperplane : Spec.HyperplaneType := Spec.HyperplaneValue

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

lemma fromCompletion_add (f g : E →L[𝕜] 𝕜) :
    (f + g).fromCompletion = f.fromCompletion + g.fromCompletion := by
  apply ContinuousLinearMap.fromCompletion_unique
  intro x
  simp

lemma fromCompletion_smul (a : 𝕜) (f : E →L[𝕜] 𝕜) :
    (a • f).fromCompletion = a • f.fromCompletion := by
  apply ContinuousLinearMap.fromCompletion_unique
  intro x
  simp

/-- Extension-evaluation is scalar-linear in the original continuous dual. -/
def completionEvaluationLinear (z : Completion E) : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜 where
  toFun f := f.fromCompletion z
  map_add' f g := by rw [fromCompletion_add]; rfl
  map_smul' a f := by rw [fromCompletion_smul]; rfl

lemma restriction_extension (g : Completion E →L[𝕜] 𝕜) :
    (g.comp Completion.toComplL).fromCompletion = g := by
  apply ContinuousLinearMap.fromCompletion_unique
  intro x
  rfl

lemma norm_fromCompletion_le (f : E →L[𝕜] 𝕜) : ‖f.fromCompletion‖ ≤ ‖f‖ := by
  rw [← ContinuousLinearMap.extend_completionToComplL]
  simpa using f.opNorm_extend_le (e := Completion.toComplL) (N := 1)
    Completion.denseRange_coe (fun x => by simp)

lemma evaluation_nonzero (z : Completion E)
    (hz : z ∉ Set.range (C02Completion.Spec.completionEmbeddingValue 𝕜 E)) :
    completionEvaluationLinear (𝕜 := 𝕜) z ≠ 0 := by
  intro hL
  have hz0 : z = 0 := by
    apply C12InitialProperties.norm_dual_pairing_separates 𝕜 (Completion E)
    intro g
    have h := LinearMap.congr_fun hL (g.comp Completion.toComplL)
    simpa [completionEvaluationLinear, restriction_extension] using h
  apply hz
  exact ⟨0, by simp [hz0, C02Completion.Spec.completionEmbeddingValue]⟩

theorem proper_hyperplane : Spec.ProperHyperplane := by
  intro 𝕜 E _ _ _ z hz
  refine ⟨completionEvaluationLinear z, fun _ => rfl,
    LinearMap.surjective (evaluation_nonzero z hz), rfl⟩

/-- A closed-inequality description of a bounded part of the hyperplane. -/
lemma bounded_hyperplane_description (z : Completion E) (r : ℝ) (hr : 0 ≤ r) :
    Spec.HyperplaneValue 𝕜 E z ∩ Metric.closedBall 0 r =
      {f : E →L[𝕜] 𝕜 | (∀ x : E, ‖f x‖ ≤ r * ‖x‖) ∧
        (∀ x : E, ‖f x‖ ≤ r * ‖(x : Completion E) - z‖)} := by
  ext f
  constructor
  · rintro ⟨hfz, hfr⟩
    change f.fromCompletion z = 0 at hfz
    have hfr' : ‖f‖ ≤ r := by simpa using hfr
    have hbound : ‖f.fromCompletion‖ ≤ r := (norm_fromCompletion_le f).trans hfr'
    constructor
    · intro x
      exact (f.le_opNorm x).trans (mul_le_mul_of_nonneg_right hfr' (norm_nonneg x))
    · intro x
      calc
        ‖f x‖ = ‖f.fromCompletion ((x : Completion E) - z)‖ := by simp [hfz]
        _ ≤ ‖f.fromCompletion‖ * ‖(x : Completion E) - z‖ :=
          f.fromCompletion.le_opNorm _
        _ ≤ r * ‖(x : Completion E) - z‖ :=
          mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  · rintro ⟨hfn, hfx⟩
    have hb : ∀ y : Completion E, ‖f.fromCompletion y‖ ≤ r * ‖y - z‖ := by
      intro y
      apply isClosed_property Completion.denseRange_coe (b := y)
      · exact isClosed_le (f.fromCompletion.continuous.norm)
          (continuous_const.mul (continuous_id.sub continuous_const).norm)
      · intro x
        simpa using hfx x
    have hfz : f.fromCompletion z = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa using hb z) (norm_nonneg _)
    refine ⟨hfz, ?_⟩
    simpa using f.opNorm_le_bound hr hfn

lemma weakStar_evaluation_continuous (x : E) :
    @Continuous (E →L[𝕜] 𝕜) 𝕜 (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      inferInstance (fun f => f x) := by
  rw [C12WeakStar.weakStarTopology_evaluations 𝕜 E]
  exact continuous_iInf_dom (i := x) continuous_induced_dom

theorem ball_intersections_closed : Spec.BallIntersectionsClosed := by
  intro 𝕜 E _ _ _ z r hr
  rw [bounded_hyperplane_description z r hr.le]
  letI := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  have hclosed (q : E → ℝ) : IsClosed {f : E →L[𝕜] 𝕜 | ∀ x, ‖f x‖ ≤ q x} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_le
      (weakStar_evaluation_continuous x).norm continuous_const
  exact (hclosed (fun x => r * ‖x‖)).inter
    (hclosed (fun x => r * ‖(x : Completion E) - z‖))

/-- Weak-star continuity would put completion-evaluation in the range of the
original evaluation pairing. Restriction of completion functionals then forces
the missing point to equal a point in the original space. -/
theorem not_weakStar_closed : Spec.NotWeakStarClosed := by
  intro 𝕜 E _ _ _ z hz hclosed
  let L := completionEvaluationLinear (𝕜 := 𝕜) z
  let B := (topDualPairing 𝕜 E).flip
  letI := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  haveI : IsTopologicalAddGroup (E →L[𝕜] 𝕜) := by
    change @IsTopologicalAddGroup (WeakDual 𝕜 E)
      (TopologicalSpace.induced id (instTopologicalSpaceWeakDual 𝕜 E)) _
    rw [induced_id]
    infer_instance
  haveI : ContinuousSMul 𝕜 (E →L[𝕜] 𝕜) := by
    change @ContinuousSMul 𝕜 (WeakDual 𝕜 E) _ _
      (TopologicalSpace.induced id (instTopologicalSpaceWeakDual 𝕜 E))
    rw [induced_id]
    infer_instance
  have hc : Continuous L := L.continuous_of_isClosed_ker hclosed
  have hspan := (C12InitialProperties.pairing_continuous_iff_mem_span
    𝕜 (E →L[𝕜] 𝕜) E B L).mp hc
  have hle : Submodule.span 𝕜 (Set.range B) ≤ B.range :=
    Submodule.span_le.mpr (fun _ h => h)
  obtain ⟨x, hx⟩ := hle hspan
  have hz_eq : z = (x : Completion E) := by
    apply sub_eq_zero.mp
    apply C12InitialProperties.norm_dual_pairing_separates 𝕜 (Completion E)
    intro g
    have heq := LinearMap.congr_fun hx (g.comp Completion.toComplL)
    have hv : g (x : Completion E) = g z := by
      simpa [B, L, completionEvaluationLinear, restriction_extension] using heq
    simp [map_sub, hv]
  exact hz ⟨x, hz_eq.symm⟩

theorem incomplete_counterexample : Spec.IncompleteCounterexample := by
  intro 𝕜 E _ _ _ hE
  have hns : ¬ Function.Surjective (fun x : E => (x : Completion E)) := by
    intro hs
    exact hE (((Completion.isUniformInducing_coe E).completeSpace_congr hs).mpr inferInstance)
  obtain ⟨z, hz⟩ := not_forall.mp hns
  have hz' : z ∉ Set.range (C02Completion.Spec.completionEmbeddingValue 𝕜 E) := hz
  exact ⟨z, hz', proper_hyperplane 𝕜 E z hz',
    ball_intersections_closed 𝕜 E z, not_weakStar_closed 𝕜 E z hz'⟩

end
end ExpandedFA.P1.KreinSmulianIncomplete
