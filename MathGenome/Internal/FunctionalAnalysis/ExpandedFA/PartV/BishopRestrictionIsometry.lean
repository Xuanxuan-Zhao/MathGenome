import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.BishopRestrictionIsometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section
set_option maxHeartbeats 1000000
namespace ExpandedFA.PartV.BishopRestrictionIsometry
open Set MeasureTheory
open FunctionSpaces.ScalarRieszMarkovSpec
open FunctionSpaces.ScalarRieszMarkov
open BishopRestrictionIsometrySpec
open scoped ENNReal ZeroAtInfty
universe u

variable {𝕜 : Type} [RCLike 𝕜]

/-- Transfer the accepted C₀ representation to compact continuous functions. -/
lemma compact_representation (hrep : ScalarRepresentation.{u} 𝕜)
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (L : C(K, 𝕜) →L[𝕜] 𝕜) :
    ∃ μ : VectorMeasure K 𝕜, FiniteScalarRadon μ ∧
      (∀ f : C(K, 𝕜), L f = scalarIntegral μ f) ∧ ‖L‖ = μ.variation.real univ := by
  obtain ⟨e, he, _⟩ := compact_identification K 𝕜
  obtain ⟨μ, hμ, hf, hn, _⟩ := hrep K (L.comp (e.symm : C₀(K, 𝕜) →L[𝕜] C(K, 𝕜)))
  refine ⟨μ, hμ, ?_, ?_⟩
  · intro f
    have hh := (hf (e f)).2
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
      e.symm_apply_apply] using hh.trans (congrArg (scalarIntegral μ) (funext (he f)))
  · exact (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv L e.symm).symm.trans hn

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

omit [T2Space K] [MeasurableSpace K] [BorelSpace K] in
lemma restriction_norm_le (Y : Submodule 𝕜 C(K, 𝕜)) (F : TopologicalSpace.Compacts K)
    (y : Y) : ‖restriction Y F y‖ ≤ ‖y‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg y)).mpr
  intro x
  exact (y : C(K, 𝕜)).norm_coe_le_norm x

omit [CompactSpace K] in
/-- Extending a measure on the compact subset by zero is its pushforward
under the closed embedding. Total variation is pushed forward exactly. -/
lemma zero_extension_radon (F : TopologicalSpace.Compacts K)
    (ν : VectorMeasure F 𝕜) (hν : FiniteScalarRadon ν) :
    FiniteScalarRadon (ν.map (Subtype.val : F → K)) := by
  have hv : (ν.map (Subtype.val : F → K)).variation =
      ν.variation.map (Subtype.val : F → K) :=
    F.isCompact.isClosed.isClosedEmbedding_subtypeVal.measurableEmbedding.variation_map
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have : ν.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  have : (ν.variation.map (Subtype.val : F → K)).InnerRegularCompactLTTop :=
    Measure.InnerRegularCompactLTTop.map_of_continuous continuous_subtype_val
  have : (ν.variation.map (Subtype.val : F → K)).Regular := by infer_instance
  refine ⟨?_, ?_⟩
  · rw [hv]
    exact measure_lt_top _ _
  · rw [hv]
    exact (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr inferInstance

omit [CompactSpace K] in
/-- The measure difference vanishes on F, so its two restrictions agree. -/
lemma restrict_eq_of_variation_sub_zero (η μ : VectorMeasure K 𝕜)
    (F : TopologicalSpace.Compacts K) (h : (η - μ).variation (F : Set K) = 0) :
    η.restrict (F : Set K) = μ.restrict (F : Set K) := by
  apply sub_eq_zero.mp
  rw [← VectorMeasure.restrict_sub, ← VectorMeasure.variation_eq_zero,
    VectorMeasure.variation_restrict F.isCompact.isClosed.measurableSet]
  exact Measure.restrict_eq_zero.mpr h

/-- Core norm argument; the representation premise is discharged separately
by the accepted real and complex Riesz--Markov theorems. -/
lemma transpose_norm_eq (hrep : ScalarRepresentation.{u} 𝕜)
    (Y : Submodule 𝕜 C(K, 𝕜)) (F : TopologicalSpace.Compacts K)
    (hF : AnnihilatorsVanish Y F) (l : C(F, 𝕜) →L[𝕜] 𝕜) :
    ‖restrictionTranspose Y F l‖ = ‖l‖ := by
  obtain ⟨L, hLY, hLn⟩ := P1.C05NormExtension.norm_preserving_extension
    𝕜 C(K, 𝕜) Y (restrictionTranspose Y F l)
  obtain ⟨η, hη, hηrep, hηn⟩ := compact_representation hrep L
  obtain ⟨ν, hν, hνrep, hνn⟩ := compact_representation hrep l
  let μ : VectorMeasure K 𝕜 := ν.map (Subtype.val : F → K)
  have hμ : FiniteScalarRadon μ := zero_extension_radon F ν hν
  have : IsFiniteMeasure η.variation := ⟨hη.1⟩
  have : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  have : η.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hη.2
  have : μ.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hμ.2
  have hδle : (η - μ).variation ≤ η.variation + μ.variation :=
    VectorMeasure.variation_sub_le
  have : IsFiniteMeasure (η - μ).variation := isFiniteMeasure_of_le _ hδle
  have : (η.variation + μ.variation).Regular := regular_add _ _
  have : (η - μ).variation.Regular := regular_of_le hδle
  have hδ : FiniteScalarRadon (η - μ) := ⟨measure_lt_top _ _,
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr inferInstance⟩
  have hmap (f : C(K, 𝕜)) : scalarIntegral μ f = l (ambientRestriction F f) := by
    rw [hνrep]
    exact F.isCompact.isClosed.isClosedEmbedding_subtypeVal.integral_map_vectorMeasure
  have hzero : (η - μ).variation (F : Set K) = 0 := by
    apply hF _ hδ
    intro y
    change (η - μ).integral (y : C(K, 𝕜)) (ContinuousLinearMap.mul ℝ 𝕜) = 0
    rw [VectorMeasure.integral_sub_vectorMeasure]
    · change scalarIntegral η (y : C(K, 𝕜)) - scalarIntegral μ (y : C(K, 𝕜)) = 0
      rw [← hηrep, hmap, hLY]
      exact sub_self _
    · exact (ContinuousMap.equivBoundedOfCompact K 𝕜 (y : C(K, 𝕜))).integrable _
    · exact (ContinuousMap.equivBoundedOfCompact K 𝕜 (y : C(K, 𝕜))).integrable _
  have heq := restrict_eq_of_variation_sub_zero η μ F hzero
  have hvmap : μ.variation = ν.variation.map (Subtype.val : F → K) :=
    F.isCompact.isClosed.isClosedEmbedding_subtypeVal.measurableEmbedding.variation_map
  have hmass : μ.variation (F : Set K) = ν.variation univ := by
    rw [hvmap, Measure.map_apply (by fun_prop) F.isCompact.isClosed.measurableSet]
    congr 1
    ext x
    simp
  have hmassle : ν.variation univ ≤ η.variation univ := by
    rw [← hmass, ← Measure.restrict_apply_univ,
      ← VectorMeasure.variation_restrict F.isCompact.isClosed.measurableSet, ← heq,
      VectorMeasure.variation_restrict F.isCompact.isClosed.measurableSet,
      Measure.restrict_apply_univ]
    exact measure_mono (subset_univ _)
  apply le_antisymm
  · change ‖l.comp (restriction Y F)‖ ≤ ‖l‖
    apply (l.comp (restriction Y F)).opNorm_le_bound (norm_nonneg l)
    intro y
    change ‖l (restriction Y F y)‖ ≤ ‖l‖ * ‖y‖
    exact (l.le_opNorm _).trans (mul_le_mul_of_nonneg_left (restriction_norm_le Y F y)
      (norm_nonneg l))
  · rw [← hLn, hηn, hνn]
    exact ENNReal.toReal_mono (measure_ne_top η.variation univ) hmassle

/-- An isometric transpose forces density of ball images. Separation uses
real convexity and the scalar phase trick, so it works over both ℝ and ℂ. -/
lemma closedBall_subset_closure_image_ball
    {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]
    [NormedSpace ℝ E] [NormedSpace ℝ G]
    [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 G]
    (T : E →L[𝕜] G) (hnorm : ∀ l : G →L[𝕜] 𝕜, ‖l.comp T‖ = ‖l‖)
    {r : ℝ} (hr : 0 < r) :
    Metric.closedBall (0 : G) r ⊆ closure (T '' Metric.ball (0 : E) r) := by
  intro x hx
  by_contra hnot
  have hc : Convex ℝ (closure (T '' Metric.ball (0 : E) r)) :=
    ((convex_ball (0 : E) r).linear_image (T.restrictScalars ℝ).toLinearMap).closure
  obtain ⟨l, a, hsep, ha⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hc isClosed_closure hnot
  have himage : ∀ y ∈ Metric.closedBall (0 : E) r,
      T y ∈ closure (T '' Metric.ball (0 : E) r) := by
    intro y hy
    apply image_closure_subset_closure_image T.continuous
    refine ⟨y, ?_, rfl⟩
    rwa [closure_ball _ hr.ne']
  have hbound : ∀ y ∈ Metric.closedBall (0 : E) r, ‖(l.comp T) y‖ ≤ a := by
    intro y hy
    let c := normingPhase (l (T y))
    have hcy : c • y ∈ Metric.closedBall (0 : E) r := by
      rw [mem_closedBall_zero_iff] at hy ⊢
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg y) (norm_normingPhase_le_one _)).trans hy
    have hh := hsep (T (c • y)) (himage _ hcy)
    simpa only [map_smul, smul_eq_mul, c, normingPhase_mul, RCLike.ofReal_re,
      ContinuousLinearMap.comp_apply] using hh.le
  have hop := (l.comp T).opNorm_bound_of_ball_bound hr a hbound
  have hnr : ‖l‖ * r ≤ a := by
    rw [hnorm] at hop
    exact (le_div_iff₀ hr).mp hop
  have hle : RCLike.re (l x) ≤ a := calc
    RCLike.re (l x) ≤ ‖l x‖ := RCLike.re_le_norm _
    _ ≤ ‖l‖ * ‖x‖ := l.le_opNorm _
    _ ≤ ‖l‖ * r := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) (norm_nonneg _)
    _ ≤ a := hnr
  exact (not_lt_of_ge hle) ha

/-- The real scalar transpose is an isometry, including empty compact sets. -/
theorem real_transpose_isometry : TransposeIsometry.{u} ℝ := by
  intro K _ _ _ _ _ Y _ F hF
  apply isometry_iff_dist_eq.mpr
  intro l m
  have hh : restrictionTranspose Y F l - restrictionTranspose Y F m =
      restrictionTranspose Y F (l - m) := by ext y; rfl
  rw [dist_eq_norm, dist_eq_norm, hh]
  exact transpose_norm_eq real_representation Y F hF (l - m)

/-- The complex scalar transpose is an isometry on the linear dual. -/
theorem complex_transpose_isometry : TransposeIsometry.{u} ℂ := by
  intro K _ _ _ _ _ Y _ F hF
  apply isometry_iff_dist_eq.mpr
  intro l m
  have hh : restrictionTranspose Y F l - restrictionTranspose Y F m =
      restrictionTranspose Y F (l - m) := by ext y; rfl
  rw [dist_eq_norm, dist_eq_norm, hh]
  exact transpose_norm_eq complex_representation Y F hF (l - m)

/-- Real ball-image density at every positive radius. -/
theorem real_ball_image_density : BallImageDensity.{u} ℝ := by
  intro K _ _ _ _ _ Y _ F hF r hr
  exact closedBall_subset_closure_image_ball (restriction Y F)
    (transpose_norm_eq real_representation Y F hF) hr

/-- Complex ball-image density at every positive radius. -/
theorem complex_ball_image_density : BallImageDensity.{u} ℂ := by
  intro K _ _ _ _ _ Y _ F hF r hr
  exact closedBall_subset_closure_image_ball (restriction Y F)
    (transpose_norm_eq complex_representation Y F hF) hr

end ExpandedFA.PartV.BishopRestrictionIsometry


