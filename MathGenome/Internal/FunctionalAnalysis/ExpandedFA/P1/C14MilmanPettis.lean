import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14MilmanPettis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Goldstine
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import Mathlib.Analysis.Normed.Operator.NNNorm

/-! Milman–Pettis without a weak compactness or weak subsequence assumption.
Goldstine provides simultaneous finite-test approximants. Uniform convexity
makes the approximants in one sufficiently narrow slice have small diameter.
Testing against one further arbitrary functional gives an operator-norm bound
on the distance to evaluation. Completeness closes the evaluation range. -/
namespace ExpandedFA.P1.C14MilmanPettis
universe u v
open Set Metric
open C14UniformConvexity C14Goldstine
noncomputable section

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Approximants close to the same almost norming coordinate have small diameter. -/
lemma uniform_slice_diameter (huc : UniformlyConvex 𝕜 E)
    {ε : ℝ} (hε : 0 < ε) (hε₂ : ε ≤ 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ξ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      (f : E →L[𝕜] 𝕜), ‖f‖ ≤ 1 → 1 - δ / 2 < ‖ξ f‖ →
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        ‖f x - ξ f‖ < δ / 2 → ‖f y - ξ f‖ < δ / 2 → ‖x - y‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := huc ε hε hε₂
  refine ⟨δ, hδ, ?_⟩
  intro ξ f hf hξ x y hx hy hfx hfy
  by_contra hdist
  have hm := h x y hx hy (le_of_not_gt hdist)
  let m : E := (2 : 𝕜)⁻¹ • (x + y)
  have herr : ‖ξ f - f m‖ < δ / 2 := by
    have heq : ξ f - f m =
        (2 : 𝕜)⁻¹ • ((ξ f - f x) + (ξ f - f y)) := by
      dsimp [m]
      simp only [map_smul, map_add, smul_eq_mul]
      ring
    rw [heq, norm_midpoint_eq_half]
    have htri := norm_add_le (ξ f - f x) (ξ f - f y)
    rw [norm_sub_rev (ξ f), norm_sub_rev (ξ f)] at htri
    linarith
  have hfm : ‖f m‖ ≤ 1 - δ :=
    (f.le_opNorm m).trans ((mul_le_mul_of_nonneg_right hf (norm_nonneg m)).trans
      (by simpa only [one_mul] using hm))
  have hrev : ‖ξ f‖ ≤ ‖ξ f - f m‖ + ‖f m‖ := norm_le_norm_sub_add _ _
  linarith

/-- Every unit bidual vector is arbitrarily close in norm to an evaluation.
Only finite-test Goldstine approximation is used, with no completeness assumption. -/
lemma bidual_unit_approximation (huc : UniformlyConvex 𝕜 E)
    (ξ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) (hξ : ‖ξ‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε₂ : ε ≤ 2) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖ξ - C04CanonicalMap.canonicalEvaluation 𝕜 E x‖ ≤ ε := by
  classical
  obtain ⟨δ, hδ, hdiam⟩ := uniform_slice_diameter huc hε hε₂
  obtain ⟨f, hf, hfξ⟩ := ξ.exists_lt_apply_of_lt_opNorm
    (show 1 - δ / 2 < ‖ξ‖ by rw [hξ]; linarith)
  obtain ⟨x, hx, hfx⟩ := goldstine_finite_approximation 𝕜 E ξ hξ.le
    {f} (δ / 2) (by linarith)
  have hfx' : ‖f x - ξ f‖ < δ / 2 := hfx f (Finset.mem_singleton_self f)
  refine ⟨x, hx, ContinuousLinearMap.opNorm_le_bound _ hε.le ?_⟩
  intro g
  change ‖ξ g - g x‖ ≤ ε * ‖g‖
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨y, hy, hyfg⟩ := goldstine_finite_approximation 𝕜 E ξ hξ.le
    {f, g} (min (δ / 2) η) (lt_min (by linarith) hη)
  have hyf : ‖f y - ξ f‖ < δ / 2 :=
    (hyfg f (by simp)).trans_le (min_le_left _ _)
  have hyg : ‖g y - ξ g‖ < η :=
    (hyfg g (by simp)).trans_le (min_le_right _ _)
  have hxy : ‖y - x‖ < ε := hdiam ξ f hf.le hfξ y x hy hx hyf hfx'
  calc
    ‖ξ g - g x‖ ≤ ‖ξ g - g y‖ + ‖g y - g x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ η + ‖g‖ * ε := by
      apply add_le_add
      · simpa only [norm_sub_rev] using hyg.le
      · rw [← map_sub]
        exact (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left hxy.le (norm_nonneg _))
    _ = ε * ‖g‖ + η := by ring

/-- Completeness closes the canonical range, giving the unit-norm case. -/
lemma bidual_unit_mem_range [CompleteSpace E] (huc : UniformlyConvex 𝕜 E)
    (ξ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) (hξ : ‖ξ‖ = 1) :
    ξ ∈ range (C04CanonicalMap.canonicalEvaluation 𝕜 E) := by
  have hc : IsClosed (range (C04CanonicalMap.canonicalEvaluation 𝕜 E)) :=
    (C05BidualIsometry.canonicalEvaluation_closed_range_iff_banach 𝕜 E).mpr
      ((C01Banach.isBanachSpace_iff_completeSpace E).mpr inferInstance)
  rw [← hc.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hr : 0 < min (ε / 2) 1 := lt_min (by linarith) (by norm_num)
  obtain ⟨x, _, hx⟩ := bidual_unit_approximation huc ξ hξ hr
    ((min_le_right _ _).trans (by norm_num : (1 : ℝ) ≤ 2))
  refine ⟨C04CanonicalMap.canonicalEvaluation 𝕜 E x, mem_range_self x, ?_⟩
  rw [dist_eq_norm]
  exact hx.trans_lt ((min_le_left _ _).trans_lt (by linarith))

/-- **Milman–Pettis**: every real or complex uniformly convex Banach space
is reflexive for its canonical evaluation map, including the zero space. -/
theorem milman_pettis : Spec.MilmanPettis.{u, v} := by
  intro 𝕜 E _ _ _ _ huc
  change UniformlyConvex 𝕜 E at huc
  change Function.Surjective (C04CanonicalMap.canonicalEvaluation 𝕜 E)
  intro ξ
  by_cases hξ : ξ = 0
  · exact ⟨0, by simp [hξ]⟩
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  let a : 𝕜 := (‖ξ‖ : 𝕜)
  have ha : a ≠ 0 := RCLike.ofReal_ne_zero.mpr hn
  have hunit : ‖a⁻¹ • ξ‖ = 1 := by
    simp [a, norm_smul, norm_inv, inv_mul_cancel₀ hn]
  obtain ⟨x, hx⟩ := bidual_unit_mem_range huc (a⁻¹ • ξ) hunit
  refine ⟨a • x, ?_⟩
  rw [map_smul, hx, smul_smul, mul_inv_cancel₀ ha, one_smul]

end
end ExpandedFA.P1.C14MilmanPettis
