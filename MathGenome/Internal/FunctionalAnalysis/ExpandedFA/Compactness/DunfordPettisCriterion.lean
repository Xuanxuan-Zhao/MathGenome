import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.DunfordPettisCriterion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EberleinSmulian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.GantmacherAdjointIdeal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01ExamplesComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences

namespace ExpandedFA.Compactness.DunfordPettisCriterion
universe u v w
open Filter Set
open scoped Topology ENNReal
noncomputable section

abbrev DunfordPettisProperty : Spec.DunfordPettisPropertyType.{u,v} :=
  Spec.DunfordPettisPropertyValue.{u,v,w}
abbrev C0TestingProperty : Spec.C0TestingPropertyType.{u,v} :=
  Spec.C0TestingPropertyValue
abbrev WeakNullTestingProperty : Spec.WeakNullTestingPropertyType.{u,v} :=
  Spec.WeakNullTestingPropertyValue

variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

private abbrev tr {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) := P1.C04Annihilators.Spec.BanachTransposeValue 𝕜 X Y T

/-- A sequential weak-to-norm assertion can be checked at zero. -/
theorem completelyContinuous_of_weakNull {Y : Type w}
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y)
    (h : ∀ x : ℕ → X,
      (∀ f : X →L[𝕜] 𝕜, Tendsto (fun n => f (x n)) atTop (𝓝 0)) →
      Tendsto (fun n => T (x n)) atTop (𝓝 0)) : IsCompletelyContinuous T := by
  intro s x hs
  have hh := h (fun n => s n - x) (fun f => by
    simpa only [map_sub, sub_self] using (hs f).sub_const (f x))
  have hh' := hh.add_const (T x)
  simpa only [map_sub, sub_add_cancel, zero_add] using hh'

/-- Gantmacher and Eberlein–Šmulian turn norming forms into a weakly
convergent subsequence in X′. Subtracting its limit permits the diagonal test. -/
theorem testing_implies_operator_property : Spec.TestingImpliesOperatorProperty.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ htest T hT
  apply completelyContinuous_of_weakNull T
  intro x hx
  apply tendsto_of_subseq_tendsto
  intro ns hns
  choose g hg hgnorm using (fun n => P1.C05Norming.norming_functional 𝕜 Y (T (x (ns n))))
  have htr : IsWeaklyCompactOperator (tr T) :=
    (GantmacherAdjointIdeal.adjoint_equivalence 𝕜 X Y T).mp hT
  obtain ⟨f, r, hr, hlim⟩ := P1.EberleinSmulian.compact_implies_subsequences
    𝕜 (X →L[𝕜] 𝕜) (tr T '' Metric.closedBall 0 1) htr
    (fun n => tr T (g n)) (fun n => mem_image_of_mem _ (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hg n))
  have hf := (weak_convergence_iff_tests (fun n => tr T (g (r n))) f).mp hlim
  have hxr (q : X →L[𝕜] 𝕜) :
      Tendsto (fun n => q (x (ns (r n)))) atTop (𝓝 0) :=
    (hx q).comp (hns.comp hr.tendsto_atTop)
  have hdiag := htest (fun n => x (ns (r n))) (fun n => tr T (g (r n)) - f)
    hxr (fun ξ => by simpa only [map_sub, sub_self] using (hf ξ).sub_const (ξ f))
  have heval : Tendsto (fun n => g (r n) (T (x (ns (r n))))) atTop (𝓝 0) := by
    change Tendsto (fun n => tr T (g (r n)) (x (ns (r n)))) atTop (𝓝 0)
    have hh := hdiag.add (hxr f)
    simpa only [sub_apply, sub_add_cancel, zero_add] using hh
  have hnorm : Tendsto (fun n => ‖T (x (ns (r n)))‖) atTop (𝓝 0) := by
    convert heval.norm using 1
    · funext n
      rw [hgnorm (r n), RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    · simp
  refine ⟨r, ?_⟩
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm


open P1.C01SequenceSpaces FunctionSpaces.SequenceDuals

local instance c0_complete : CompleteSpace (SequenceC0 𝕜) :=
  (P1.C01ExamplesComplete.sequence_c0_closed 𝕜).isComplete.completeSpace_coe

/-- A uniformly bounded pointwise-null family of functionals defines an
operator into the canonical subspace c₀ of ℓ∞. -/
def sequenceOperator (f : ℕ → (X →L[𝕜] 𝕜))
    (hpoint : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 0))
    (C : ℝ) (hbound : ∀ n, ‖f n‖ ≤ C) : X →L[𝕜] SequenceC0 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨⟨fun n => f n x, memℓp_infty ⟨C * ‖x‖, by
        rintro _ ⟨n, rfl⟩
        exact ((f n).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg x))⟩⟩, hpoint x⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        apply lp.ext
        funext n
        exact (f n).map_add x y
      map_smul' := by
        intro a x
        apply Subtype.ext
        apply lp.ext
        funext n
        exact (f n).map_smul a x }
    C (fun x => lp.norm_le_of_forall_le
      (mul_nonneg ((norm_nonneg (f 0)).trans (hbound 0)) (norm_nonneg x))
      (fun n => ((f n).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg x))))

@[simp] theorem sequenceOperator_apply (f : ℕ → (X →L[𝕜] 𝕜))
    (hpoint : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 0))
    (C : ℝ) (hbound : ∀ n, ‖f n‖ ≤ C) (x : X) (n : ℕ) :
    (sequenceOperator f hpoint C hbound x).val n = f n x := rfl

/-- Coordinate functionals are the images of the ℓ¹ unit vectors. -/
theorem c0SeriesFunctional_single_apply (n : ℕ) (a : 𝕜) (x : SequenceC0 𝕜) :
    c0SeriesFunctional (lp.single 1 n a) x = a * x.val n := by
  classical
  rw [c0SeriesFunctional_apply, tsum_eq_single n]
  · simp
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj, zero_mul]

/-- Direct bidual proof of weak compactness. Weak nullity is used at every
ξ ∈ X″; pointwise nullity alone would not put this bidual image in c₀. -/
theorem sequenceOperator_weaklyCompact [CompleteSpace X]
    (f : ℕ → (X →L[𝕜] 𝕜))
    (hf : ∀ ξ : (X →L[𝕜] 𝕜) →L[𝕜] 𝕜,
      Tendsto (fun n => ξ (f n)) atTop (𝓝 0))
    (C : ℝ) (hbound : ∀ n, ‖f n‖ ≤ C) :
    IsWeaklyCompactOperator (sequenceOperator f
      (fun x => hf (NormedSpace.inclusionInDoubleDual 𝕜 X x)) C hbound) := by
  let hpoint := fun x => hf (NormedSpace.inclusionInDoubleDual 𝕜 X x)
  let T := sequenceOperator f hpoint C hbound
  apply (GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 X (SequenceC0 𝕜) T).mpr
  intro ξ
  let y : SequenceC0 𝕜 := ⟨⟨fun n => ξ (f n), memℓp_infty ⟨‖ξ‖ * C, by
    rintro _ ⟨n, rfl⟩
    exact (ξ.le_opNorm (f n)).trans
      (mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg ξ))⟩⟩, hf ξ⟩
  refine ⟨y, ?_⟩
  let U := (c0DualityEquiv (𝕜 := 𝕜)).toContinuousLinearEquiv.toContinuousLinearMap
  have hsingle (n : ℕ) (a : 𝕜) :
      tr T (U (lp.single 1 n a)) = a • f n := by
    ext x
    change c0SeriesFunctional (lp.single 1 n a) (T x) = a * f n x
    rw [c0SeriesFunctional_single_apply]
    rfl
  have heq : (ξ.comp (tr T)).comp U =
      ((NormedSpace.inclusionInDoubleDual 𝕜 (SequenceC0 𝕜) y).comp U) := by
    apply lp.ext_continuousLinearMap (by simp)
    intro n
    apply ContinuousLinearMap.ext
    intro a
    change ξ (tr T (U (lp.single 1 n a))) =
      c0SeriesFunctional (lp.single 1 n a) y
    rw [hsingle, map_smul, c0SeriesFunctional_single_apply]
    rfl
  ext q
  obtain ⟨a, rfl⟩ := (c0DualityEquiv (𝕜 := 𝕜)).surjective q
  exact congrArg (fun H : SequenceLp 𝕜 1 →L[𝕜] 𝕜 => H a) heq

/-- Complete continuity of the sequence operator controls its diagonal
coordinates by the supremum norm. -/
theorem c0_testing_implies_weakNull_testing [CompleteSpace X]
    (h : C0TestingProperty 𝕜 X) : WeakNullTestingProperty 𝕜 X := by
  intro x f hx hf
  obtain ⟨C, _, hC⟩ := P1.C12BoundedSequences.norm_bound_of_scalar_bounds
    𝕜 (X →L[𝕜] 𝕜) ℕ f (fun ξ => by
      obtain ⟨B, hB⟩ := (hf ξ).norm.bddAbove_range
      exact ⟨B, fun n => hB (mem_range_self n)⟩)
  let hpoint := fun x => hf (NormedSpace.inclusionInDoubleDual 𝕜 X x)
  let T := sequenceOperator f hpoint C hC
  have hT : IsWeaklyCompactOperator T := sequenceOperator_weaklyCompact f hf C hC
  have hlim : Tendsto (fun n => T (x n)) atTop (𝓝 0) := by
    simpa only [map_zero] using h T hT x 0 (fun q => by
      simpa only [map_zero] using hx q)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n =>
    lp.norm_apply_le_norm ENNReal.top_ne_zero (T (x n)).val n)
    (by simpa using hlim.norm)

/-- The all-target property specializes to c₀. ULift merely accommodates
an arbitrary target universe; its linear isometry preserves all structures. -/
theorem operator_property_implies_c0_testing [CompleteSpace X]
    (h : DunfordPettisProperty.{u,v,w} 𝕜 X) : C0TestingProperty 𝕜 X := by
  intro T hT
  let e : ULift.{w} (SequenceC0 𝕜) ≃ₗᵢ[𝕜] SequenceC0 𝕜 := LinearIsometryEquiv.ulift 𝕜 _
  let S := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp T
  have hS : IsWeaklyCompactOperator S :=
    (GantmacherAdjointIdeal.two_sided_ideal 𝕜 X (SequenceC0 𝕜)
      (ULift.{w} (SequenceC0 𝕜)) T hT).1 e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  intro x a hx
  have hlim := h _ S hS x a hx
  simpa [S, Function.comp_def] using e.continuous.tendsto (S a) |>.comp hlim

/-- The three assertions of the manuscript, for real or complex Banach X. -/
theorem equivalences : Spec.Equivalences.{u,v,w} := by
  intro 𝕜 X _ _ _ _
  refine ⟨⟨operator_property_implies_c0_testing, ?_⟩, ⟨c0_testing_implies_weakNull_testing, ?_⟩⟩
  · intro h Y _ _ _ T hT
    exact testing_implies_operator_property 𝕜 X Y
      (c0_testing_implies_weakNull_testing h) T hT
  · intro h T hT
    exact testing_implies_operator_property 𝕜 X _ h T hT

end
end ExpandedFA.Compactness.DunfordPettisCriterion
