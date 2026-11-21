import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.SummableErrors
import MathGenome.Internal.RealAnalysis.D11.Ch05.MonotoneSeries
import MathGenome.Internal.RealAnalysis.D11.Ch05.MarkovZeroFinite
import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Summable integral errors (paper.tex:2192–2202).
The nonnegative-series theorem identifies the integral of the pointwise
error series with the sum of the error integrals. A finite nonnegative
integral makes that series finite outside a measurable null envelope.
There its terms tend to zero, giving the required scalar convergence.
-/
open Filter MeasureTheory
open scoped Topology ENNReal

universe u
noncomputable section
namespace D11.Ch07.SummableErrors

open D11.Ch04.AeCommonException
open D11.Ch05.NonnegativeIntegral

theorem summable_errors_ae : Specs.D11.Ch07.SummableErrors.summable_errors_ae := by
  intro X 𝕜 _ _ _ _ μ f g hf hg hsum
  let e : ℕ → X → ℝ≥0∞ := fun n x => ENNReal.ofReal ‖f n x - g x‖
  have he : ∀ n, Measurable (e n) := fun n => (hf n |>.sub hg).norm.ennreal_ofReal
  have hs : Measurable (fun x => ∑' n, e n x) := by
    simpa only [ENNReal.tsum_eq_iSup_nat] using
      Measurable.iSup (fun N => Finset.measurable_sum _ (fun n _ => he n))
  have hseries := D11.Ch05.MonotoneSeries.nonnegative_series μ e he
  change nonnegativeIntegral μ (fun x => ∑' n, e n x) =
    ∑' n, nonnegativeIntegral μ (e n) at hseries
  have hfin : nonnegativeIntegral μ (fun x => ∑' n, e n x) < ∞ := by
    rw [hseries]
    exact hsum
  have hae := D11.Ch05.MarkovZeroFinite.finite_values_ae μ _ hs hfin
  change almostEverywhere μ (fun x => Tendsto (fun n => f n x) atTop (𝓝 (g x)))
  exact almostEverywhere_mono μ _ _ hae fun x hx => by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hzero := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hzero
    simpa only [e, Function.comp_def, ENNReal.toReal_zero,
      ENNReal.toReal_ofReal (norm_nonneg _)] using hreal

end D11.Ch07.SummableErrors
