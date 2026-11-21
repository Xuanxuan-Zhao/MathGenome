import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.ComplexMvtFailure
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.Euler
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.PiPeriod

/-!
K03.05.lagrange, paper.tex:821: the unit-circle path is a counterexample
to an exact complex-valued mean value theorem. Its endpoint displacement
vanishes, while its real-parameter velocity is a quarter-turn of a unit
vector, so it cannot equal the zero secant slope. The constructed series
and analytic π are used throughout, without complex differentiation.
-/

noncomputable section
namespace SingleVariableAnalysis

def unitCirclePath (t : ℝ) : ℂ :=
  (realSeriesCos t : ℂ) + Complex.I * (realSeriesSin t : ℂ)

def unitCircleVelocity (t : ℝ) : ℂ :=
  -(realSeriesSin t : ℂ) + Complex.I * (realSeriesCos t : ℂ)

theorem unitCirclePath_endpoint_difference :
    unitCirclePath (2 * analyticPi) - unitCirclePath 0 = 0 := by
  have hs : realSeriesSin (2 * analyticPi) = realSeriesSin 0 := by
    simpa only [zero_add] using PiPeriod.piPeriod_periodic.1 0
  have hc : realSeriesCos (2 * analyticPi) = realSeriesCos 0 := by
    simpa only [zero_add] using PiPeriod.piPeriod_periodic.2 0
  simp only [unitCirclePath, hs, hc, sub_self]

theorem unitCirclePath_hasDerivAt (t : ℝ) :
    HasDerivAt unitCirclePath (unitCircleVelocity t) t := by
  have hs : HasDerivAt realSeriesSin (realSeriesCos t) t :=
    (real_sinCosSeries_hasDerivAt t).1
  have hc : HasDerivAt realSeriesCos (-realSeriesSin t) t :=
    (real_sinCosSeries_hasDerivAt t).2
  simpa only [unitCirclePath, unitCircleVelocity, Complex.ofReal_neg] using!
    hc.ofReal_comp.fun_add (hs.ofReal_comp.const_mul Complex.I)

theorem unitCirclePath_continuousOn :
    ContinuousOn unitCirclePath (Set.Icc 0 (2 * analyticPi)) :=
  (continuous_iff_continuousAt.mpr
    (fun t => (unitCirclePath_hasDerivAt t).continuousAt)).continuousOn

theorem unitCirclePath_eq_expSeries (t : ℝ) :
    unitCirclePath t = seriesExp (Complex.I * (t : ℂ)) :=
  (expSeries_imaginary t).symm

theorem unitCircleVelocity_eq_I_mul (t : ℝ) :
    unitCircleVelocity t = Complex.I * unitCirclePath t := by
  simp only [unitCircleVelocity, unitCirclePath, mul_add, ← mul_assoc,
    Complex.I_mul_I, neg_one_mul]
  ring

theorem unitCirclePath_derivative_modulus (t : ℝ) :
    ‖deriv unitCirclePath t‖ = 1 := by
  have hn : ‖seriesExp (Complex.I * (t : ℂ))‖ = 1 :=
    expSeries_imaginary_norm t
  rw [(unitCirclePath_hasDerivAt t).deriv, unitCircleVelocity_eq_I_mul,
    unitCirclePath_eq_expSeries, norm_mul, Complex.norm_I, hn, one_mul]

theorem unitCirclePath_no_mean_value_point :
    ¬ ∃ c ∈ Set.Ioo 0 (2 * analyticPi),
      unitCirclePath (2 * analyticPi) - unitCirclePath 0 =
        deriv unitCirclePath c * ((2 * analyticPi - 0 : ℝ) : ℂ) := by
  rintro ⟨c, _, heq⟩
  rw [unitCirclePath_endpoint_difference] at heq
  have hlength : ((2 * analyticPi - 0 : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    have hpos : 0 < 2 * analyticPi :=
      mul_pos (by norm_num) PiPeriod.piPeriod_positive.2
    exact ne_of_gt (by simpa only [sub_zero] using hpos)
  have hz : deriv unitCirclePath c = 0 :=
    (mul_eq_zero.mp heq.symm).resolve_right hlength
  have hnorm := unitCirclePath_derivative_modulus c
  rw [hz, norm_zero] at hnorm
  norm_num at hnorm

theorem unitCirclePath_no_mean_value_slope :
    ¬ ∃ c ∈ Set.Ioo 0 (2 * analyticPi),
      HasDerivAt unitCirclePath
        ((unitCirclePath (2 * analyticPi) - unitCirclePath 0) /
          ((2 * analyticPi - 0 : ℝ) : ℂ)) c := by
  rintro ⟨c, _, hc⟩
  rw [unitCirclePath_endpoint_difference, zero_div] at hc
  have hnorm := unitCirclePath_derivative_modulus c
  rw [hc.deriv, norm_zero] at hnorm
  norm_num at hnorm

end SingleVariableAnalysis
