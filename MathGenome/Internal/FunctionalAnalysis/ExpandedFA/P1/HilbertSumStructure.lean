import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.HilbertSumStructure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02HilbertSum

/-!
Hilbert structure of the arbitrary-index square-summable direct sum.
All objects are those of the accepted `C02HilbertSum` interface.
Mathlib's `lp` completeness theorem uses coordinate limits and finite
power-sum bounds, and therefore imposes no countability on the index set.
-/
noncomputable section
open scoped ComplexConjugate ENNReal
universe u v w
namespace ExpandedFA.P1.HilbertSumStructure

open Spec
open ExpandedFA.P1.C02HilbertSum

/-- Pointwise Cauchy–Schwarz and arbitrary-index Hölder give absolute
summability and its bound. The sum is the already fixed inner product. -/
theorem absolute_inner_summability : AbsoluteInnerSummability.{u, v, w} := by
  intro I H _ 𝕜 _ _ x y
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have habs : Summable (fun i => ‖inner 𝕜 (x i) (y i)‖) :=
    (lp.summable_mul hpq x y).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun _ => norm_inner_le_norm _ _)
  exact ⟨habs,
    (habs.tsum_le_tsum (fun _ => norm_inner_le_norm _ _) (lp.summable_mul hpq x y)).trans
      (lp.tsum_mul_le_mul_norm' hpq x y),
    ExpandedFA.P1.C02HilbertSum.hasSum_inner x y⟩

/-- These are laws of the canonical product, whose defining formula is
`ExpandedFA.P1.C02HilbertSum.inner_eq_tsum`; no new product is substituted. -/
theorem inner_product_laws : InnerProductLaws.{u, v, w} := by
  intro I H _ 𝕜 _ _
  exact ⟨inner_add_left, inner_add_right,
    fun _ _ _ => inner_smul_left _ _ _,
    fun _ _ _ => inner_smul_right _ _ _,
    fun x y => (inner_conj_symm y x).symm,
    fun _ => inner_self_nonneg,
    fun _ => inner_self_eq_zero⟩

theorem norm_squared_formula : NormSquaredFormula.{u, v, w} := by
  intro I H _ 𝕜 _ _ x
  exact ⟨(norm_sq_eq_re_inner (𝕜 := 𝕜) x).symm,
    ExpandedFA.P1.C02HilbertSum.norm_sq_eq_tsum x, ExpandedFA.P1.C02HilbertSum.norm_sq_eq_sup x⟩

/-- This theorem concerns the normed-group structure already fixed in the
interface. It even applies to complete normed summands without inner products. -/
theorem completeness : Completeness.{u, v} := by
  intro I H _ _
  infer_instance

theorem coordinate_contractive : CoordinateContractive.{u, v, w} := by
  intro I H _ 𝕜 _ _ i
  constructor
  · apply (coordinate (𝕜 := 𝕜) H i).opNorm_le_bound zero_le_one
    intro x
    simpa only [one_mul, ExpandedFA.P1.C02HilbertSum.coordinate_apply] using
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x i
  · exact lp.lipschitzWith_one_eval 2 i

theorem inclusion_isometric : InclusionIsometric.{u, v, w} := by
  intro I H _ 𝕜 _ _ i
  classical
  exact ⟨lp.isometry_single i, ExpandedFA.P1.C02HilbertSum.norm_inclusion i⟩

theorem inclusion_contractive : InclusionContractive.{u, v, w} := by
  intro I H _ 𝕜 _ _ i
  constructor
  · apply (inclusion (𝕜 := 𝕜) H i).opNorm_le_bound zero_le_one
    intro a
    simp only [ExpandedFA.P1.C02HilbertSum.norm_inclusion, one_mul, le_refl]
  · exact (inclusion_isometric (𝕜 := 𝕜) i).1.lipschitzWith

end ExpandedFA.P1.HilbertSumStructure
