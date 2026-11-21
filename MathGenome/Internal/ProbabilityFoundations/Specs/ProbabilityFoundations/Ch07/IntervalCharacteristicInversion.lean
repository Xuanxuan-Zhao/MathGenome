import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Interval part of paper.tex, Theorem 7.3 (2474–2482), including endpoint atoms.
The quotient is represented by its finite exponential integral; the independent
formula and continuity obligations below identify its continuous extension.
`charFun` is the canonical object used by the upstream transform interfaces,
here on the real inner product space ℝ. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace ProbabilityFoundations.Ch07

/-- The continuous extension of (exp(-ita)-exp(-itb))/(it). -/
def intervalInversionQuotient (a b t : ℝ) : ℂ :=
  ∫ y in a..b, Complex.exp (-(Complex.I * (t : ℂ)) * (y : ℂ))

/-- Symmetric real frequency cutoff in the probability Fourier convention. -/
def intervalInversionCutoff (μ : Measure ℝ) (a b T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t in -T..T, intervalInversionQuotient a b t * charFun μ t

end ProbabilityFoundations.Ch07

namespace Specs.ProbabilityFoundations.Ch07.IntervalCharacteristicInversion
open _root_.ProbabilityFoundations.Ch07

def QuotientFormula : Prop := ∀ a b t : ℝ, t ≠ 0 →
  intervalInversionQuotient a b t =
    (Complex.exp (-Complex.I * (t : ℂ) * (a : ℂ)) -
      Complex.exp (-Complex.I * (t : ℂ) * (b : ℂ))) / (Complex.I * (t : ℂ))

def QuotientAtZero : Prop := ∀ a b : ℝ,
  intervalInversionQuotient a b 0 = ((b - a : ℝ) : ℂ)

def QuotientContinuous : Prop := ∀ a b : ℝ, Continuous (intervalInversionQuotient a b)

def FiniteCutoffIntegrable : Prop := ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
  (a b T : ℝ),
  IntervalIntegrable (fun t => intervalInversionQuotient a b t * charFun μ t) volume (-T) T

def IntervalInversion : Prop := ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
  (a b : ℝ), a < b →
  Tendsto (intervalInversionCutoff μ a b) atTop
    (𝓝 ((μ.real (Set.Ioo a b) : ℂ) +
      (1 / 2 : ℂ) * (μ.real {a} : ℂ) + (1 / 2 : ℂ) * (μ.real {b} : ℂ)))

end Specs.ProbabilityFoundations.Ch07.IntervalCharacteristicInversion
