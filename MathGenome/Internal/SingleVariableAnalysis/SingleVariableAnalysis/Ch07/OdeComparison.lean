import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpAddition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Product
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.ZeroDerivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.OdeComparison
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
The factorial-series exponential is the unique normalized solution of y′ = y
on every real interval containing zero (K03.07.construction_bridges).
The integrating factor y(t)E(-t) has zero real derivative. The upstream
zero-derivative theorem applies with continuity on the entire interval, so
the conclusion includes its endpoints. Multiplying by E(t) recovers y(t).
Real solutions are embedded in ℂ and identified using the proved real-series
restriction bridge. No ODE existence or uniqueness theorem is assumed.
-/

noncomputable section
namespace SingleVariableAnalysis
open Set

theorem real_expSeries_ode_exists :
    Specs.SingleVariableAnalysis.Ch07.OdeComparison.realExistence := by
  intro I _ _
  refine ⟨fun t _ => (real_expSeries_hasDerivAt t).continuousAt.continuousWithinAt,
    fun t _ => real_expSeries_hasDerivAt t,
    fun t _ => (real_expSeries_hasDerivAt t).hasDerivWithinAt, ?_⟩
  apply Complex.ofReal_injective
  change (realSeriesExp 0 : ℂ) = (1 : ℂ)
  rw [← expSeries_real_restriction, Complex.ofReal_zero, expSeries_zero]

theorem complex_expSeries_ode_exists :
    Specs.SingleVariableAnalysis.Ch07.OdeComparison.complexExistence := by
  intro I _ _
  exact ⟨fun t _ => (expSeries_real_hasDerivAt t).continuousAt.continuousWithinAt,
    fun t _ => expSeries_real_hasDerivAt t,
    fun t _ => (expSeries_real_hasDerivAt t).hasDerivWithinAt, expSeries_zero⟩

namespace OdeComparison

theorem negative_exp_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => seriesExp ((-s : ℝ) : ℂ))
      (-seriesExp ((-t : ℝ) : ℂ)) t := by
  have h : HasDerivAt (fun s : ℝ => seriesExp (s : ℂ))
      (seriesExp ((-t : ℝ) : ℂ)) (-t) := expSeries_real_hasDerivAt (-t)
  simpa only [Function.comp_def, neg_one_smul] using
    h.scomp t (hasDerivAt_neg t)

end OdeComparison

theorem complex_expSeries_ode_unique :
    Specs.SingleVariableAnalysis.Ch07.OdeComparison.complexUniqueness := by
  intro I hI h0 y hy hd hy0
  have hf (t : ℝ) (ht : t ∈ interior I) :
      HasDerivAt (fun s : ℝ => y s * seriesExp ((-s : ℝ) : ℂ)) 0 t := by
    convert
      (hd t ht).mul (OdeComparison.negative_exp_hasDerivAt t)
      using 1
    simp only [mul_neg, add_neg_cancel]
  obtain ⟨c, hc⟩ := complex_zero_derivative_constant
    (fun t : ℝ => y t * seriesExp ((-t : ℝ) : ℂ)) I hI
    (hy.mul (fun t _ => (OdeComparison.negative_exp_hasDerivAt t).continuousAt.continuousWithinAt))
    (fun t ht => (hf t ht).differentiableAt) (fun t ht => (hf t ht).deriv)
  have hc1 : c = 1 := by
    have h := hc 0 h0
    simpa only [neg_zero, Complex.ofReal_zero, hy0, expSeries_zero, mul_one] using h.symm
  intro t ht
  change y t = seriesExp (t : ℂ)
  have hcancel : seriesExp ((-t : ℝ) : ℂ) * seriesExp (t : ℂ) = 1 := by
    rw [← expSeries_add, ← Complex.ofReal_add, neg_add_cancel, Complex.ofReal_zero,
      expSeries_zero]
  calc
    y t = y t * (seriesExp ((-t : ℝ) : ℂ) * seriesExp (t : ℂ)) := by
      rw [hcancel, mul_one]
    _ = (y t * seriesExp ((-t : ℝ) : ℂ)) * seriesExp (t : ℂ) := (mul_assoc _ _ _).symm
    _ = seriesExp (t : ℂ) := by rw [hc t ht, hc1, one_mul]

theorem real_expSeries_ode_unique :
    Specs.SingleVariableAnalysis.Ch07.OdeComparison.realUniqueness := by
  intro I hI h0 y hy hd hy0
  have h := complex_expSeries_ode_unique I hI h0 (fun t => (y t : ℂ))
    (Complex.continuous_ofReal.comp_continuousOn hy)
    (fun t ht => (hd t ht).ofReal_comp) (by simp only [hy0, Complex.ofReal_one])
  intro t ht
  apply Complex.ofReal_injective
  exact (h ht).trans (expSeries_real_restriction t)

end SingleVariableAnalysis
