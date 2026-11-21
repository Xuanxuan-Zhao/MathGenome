import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05BidualIsometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BidualClosedImage
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.TransposeNorm

/-!
The full norm-formula and bidual-embedding theorem, `fa2:p1:c05:bidual-isometry`.
Norming functionals attain both dual suprema, including at zero. The absolute
value formula, isometry, closed-image criterion and transpose norm equality
reuse the accepted prerequisite results for the same shared objects.
-/

namespace ExpandedFA.P1.C05BidualIsometry

universe u v w

theorem dual_norm_formula : Spec.DualNormFormula.{u, v} := by
  intro 𝕜 E _ _ _ x
  refine ⟨TransposeNorm.norm_eq_dual_unitBall_sup 𝕜 E x, ?_⟩
  have hupper : ∀ b ∈
      (fun f : E →L[𝕜] 𝕜 => RCLike.re (f x)) '' {f | ‖f‖ ≤ 1}, b ≤ ‖x‖ := by
    rintro b ⟨f, hf, rfl⟩
    calc
      RCLike.re (f x) ≤ ‖f x‖ := RCLike.re_le_norm (f x)
      _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional 𝕜 E x
  have hmem : ‖x‖ ∈
      (fun f : E →L[𝕜] 𝕜 => RCLike.re (f x)) '' {f | ‖f‖ ≤ 1} := by
    refine ⟨f, hf, ?_⟩
    change RCLike.re (f x) = ‖x‖
    rw [hfx, RCLike.ofReal_re]
  exact le_antisymm (le_csSup ⟨‖x‖, hupper⟩ hmem)
    (csSup_le ⟨‖x‖, hmem⟩ hupper)

theorem canonicalEvaluation_norm : Spec.CanonicalEvaluationNorm.{u, v} :=
  BidualClosedImage.canonicalEvaluation_norm

theorem canonicalEvaluation_linear_isometry :
    Spec.CanonicalEvaluationLinearIsometry.{u, v} := by
  intro 𝕜 E _ _ _
  exact ⟨(C04CanonicalMap.canonicalEvaluation 𝕜 E).map_add,
    (C04CanonicalMap.canonicalEvaluation 𝕜 E).map_smul,
    BidualClosedImage.canonicalEvaluation_isometry 𝕜 E⟩

theorem canonicalEvaluation_injective : Spec.CanonicalEvaluationInjective.{u, v} := by
  intro 𝕜 E _ _ _
  exact (canonicalEvaluation_linear_isometry 𝕜 E).2.2.injective

theorem dual_separates_points : Spec.DualSeparatesPoints.{u, v} := by
  intro 𝕜 E _ _ _ x y hxy
  obtain ⟨f, _, hfx⟩ :=
    C05Norming.norming_functional_nonzero 𝕜 E (x - y) (sub_ne_zero.mpr hxy)
  refine ⟨f, fun h => ?_⟩
  have hnorm : (‖x - y‖ : 𝕜) = 0 := by
    rw [← hfx, map_sub, h, sub_self]
  have : ‖x - y‖ = 0 := RCLike.ofReal_eq_zero.mp hnorm
  exact hxy (sub_eq_zero.mp (norm_eq_zero.mp this))

theorem bidual_banach : Spec.BidualBanach.{u, v} := by
  intro 𝕜 E _ _ _
  exact C04DualComplete.dual_banach 𝕜 (C04Dual.ContinuousDual 𝕜 E)

theorem canonicalEvaluation_closed_range_iff_banach :
    Spec.CanonicalEvaluationClosedRangeIffBanach.{u, v} :=
  BidualClosedImage.canonicalEvaluation_closed_range_iff_banach

theorem reflexive_banach : Spec.ReflexiveBanach.{u, v} :=
  BidualClosedImage.reflexive_banach

theorem banachTranspose_norm : Spec.BanachTransposeNormEquality.{u, v, w} :=
  TransposeNorm.banachTranspose_norm

/-- Assemble every clause of the original theorem, without extra hypotheses. -/
theorem norm_formula_and_isometric_bidual_embedding :
    Spec.CompleteBidualTheorem.{u, v, w} := by
  intro 𝕜 E _ _ _
  exact ⟨dual_norm_formula 𝕜 E, canonicalEvaluation_linear_isometry 𝕜 E,
    dual_separates_points 𝕜 E, bidual_banach 𝕜 E,
    canonicalEvaluation_closed_range_iff_banach 𝕜 E, reflexive_banach 𝕜 E,
    fun F _ _ T => banachTranspose_norm 𝕜 E F T⟩

end ExpandedFA.P1.C05BidualIsometry
