import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.ScaledLimit
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.MoreauDecomposition
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.SmallParameter
import Mathlib.Topology.Algebra.Order.Field

/-! The scaled proximal limit follows from Moreau decomposition, the small
positive parameter limit for the conjugate, and nonexpansiveness. -/
noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.Proximal
open P1.ExtendedConvexFunctions
universe u

/-- The normalized proximal map converges to the negative minimum-norm point
in the norm closure of the conjugate domain, independently of the datum. -/
theorem proximalMap_scaledLimit : ScaledLimitSpec.ScaledLimit.{u} := by
  intro H _ _ _ φ hp hc hl f
  obtain ⟨hp', hc', hl'⟩ := conjugateFunction_regular H φ hp hc hl
  have hsmall : Tendsto (fun μ : ℝ =>
      proximalMap H (conjugateFunction H φ) μ⁻¹ 0) atTop
      (𝓝 (domainProjection H (conjugateFunction H φ) 0)) :=
    (proximalMap_smallParameter H (conjugateFunction H φ) hp' hc' hl' 0).comp
      (tendsto_inv_atTop_nhdsGT_zero : Tendsto (fun μ : ℝ => μ⁻¹) atTop (𝓝[>] 0))
  have hdatum : Tendsto (fun μ : ℝ => μ⁻¹ • f) atTop (𝓝 (0 : H)) := by
    simpa using (tendsto_inv_atTop_zero :
      Tendsto (fun μ : ℝ => μ⁻¹) atTop (𝓝 (0 : ℝ))).smul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => f) atTop (𝓝 f))
  have herror : Tendsto (fun μ : ℝ =>
      proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f) -
      proximalMap H (conjugateFunction H φ) μ⁻¹ 0) atTop (𝓝 (0 : H)) := by
    apply squeeze_zero_norm'
      (a := fun μ : ℝ => ‖μ⁻¹ • f‖) _ (by simpa using hdatum.norm)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
    simpa only [proximalMap, sub_zero] using
      proximalMap_nonexpansive H (conjugateFunction H φ) hp' hc' hl'
        μ⁻¹ (inv_pos.mpr hμ) (μ⁻¹ • f) 0
  have hdual : Tendsto (fun μ : ℝ =>
      proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f)) atTop
      (𝓝 (domainProjection H (conjugateFunction H φ) 0)) := by
    simpa only [sub_add_cancel, zero_add] using herror.add hsmall
  have hlimit := hdatum.sub hdual
  change Tendsto (fun μ : ℝ => μ⁻¹ • proximalMap H φ μ f) atTop
    (𝓝 (-domainProjection H (conjugateFunction H φ) 0))
  apply (show Tendsto (fun μ : ℝ => μ⁻¹ • f -
      proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f)) atTop
      (𝓝 (-domainProjection H (conjugateFunction H φ) 0)) from
        by simpa only [zero_sub] using hlimit).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
  have he := (moreau_decomposition H φ hp hc hl μ hμ f).1
  have hs := congrArg (fun v : H => μ⁻¹ • v) he
  change μ⁻¹ • (proximalMap H φ μ f + μ •
    proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f)) = μ⁻¹ • f at hs
  rw [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hμ), one_smul] at hs
  exact (eq_sub_iff_add_eq.mpr hs).symm

end ExpandedFA.Proximal
