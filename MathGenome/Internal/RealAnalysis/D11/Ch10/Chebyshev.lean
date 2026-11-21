import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.Chebyshev
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Chebyshev's inequality on arbitrary positive measure spaces.
Integrate the constant `α ^ p` on the measurable strict level set, and
bound its indicator pointwise by `‖f‖ ^ p`. Extended arithmetic retains
the infinite-integral and infinite-level-measure cases without division.
-/
open Set MeasureTheory
open scoped ENNReal
universe u v
noncomputable section
namespace D11.Ch10.Chebyshev

theorem chebyshev : Specs.D11.Ch10.Chebyshev.chebyshev := by
  intro X E _ _ _ _ μ f p α hf hp hα
  change ENNReal.ofReal (α ^ p) * μ {x | α < ‖f x‖} ≤
    D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ
      (fun x => ENNReal.ofReal (‖f x‖ ^ p))
  rw [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral]
  have hlevel : MeasurableSet {x | α < ‖f x‖} :=
    measurableSet_lt measurable_const hf.norm
  calc
    ENNReal.ofReal (α ^ p) * μ {x | α < ‖f x‖} =
        ∫⁻ x, {x | α < ‖f x‖}.indicator (fun _ => ENNReal.ofReal (α ^ p)) x ∂μ := by
      rw [lintegral_indicator hlevel, lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p) ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : α < ‖f x‖
      · rw [Set.indicator_of_mem (show x ∈ {x | α < ‖f x‖} from hx)]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hα.le hx.le hp.le)
      · rw [Set.indicator_of_notMem (show x ∉ {x | α < ‖f x‖} from hx)]
        exact bot_le

end D11.Ch10.Chebyshev
