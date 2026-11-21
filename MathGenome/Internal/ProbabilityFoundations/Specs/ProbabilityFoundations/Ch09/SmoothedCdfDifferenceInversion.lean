import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.SmoothingKernel
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.RealDistributionFunctions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Group.Convolution

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityFoundations.Ch09

noncomputable def smoothingMeasure (J : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (J x))

/-- The law of an independent sum X + W/T. -/
noncomputable def smoothedLaw (μ : Measure ℝ) (J : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  μ.conv ((smoothingMeasure J).map (fun w => w / T))

noncomputable def smoothedCdf (μ : Measure ℝ) (J : ℝ → ℝ) (T x : ℝ) : ℝ :=
  Specs.ProbabilityFoundations.Ch01.RealDistributionFunctions.distributionFunctionValue
    (smoothedLaw μ J T) x

noncomputable def smoothedCharacteristicDifference (μ ν : Measure ℝ)
    (J : ℝ → ℝ) (T t : ℝ) : ℂ :=
  (charFun μ t - charFun ν t) * charFun (smoothingMeasure J) (t / T)

/-- At zero, dslope uses the derivative; elsewhere it is the difference divided by t. -/
noncomputable def characteristicDifferenceQuotient (μ ν : Measure ℝ) : ℝ → ℂ :=
  dslope (fun t => charFun μ t - charFun ν t) 0

noncomputable def smoothedCharacteristicQuotient (μ ν : Measure ℝ)
    (J : ℝ → ℝ) (T t : ℝ) : ℂ :=
  characteristicDifferenceQuotient μ ν t * charFun (smoothingMeasure J) (t / T)

/-- The continuous value of a(t)/(-it) is I times the continuous value of a(t)/t. -/
noncomputable def inverseSmoothedQuotient (μ ν : Measure ℝ)
    (J : ℝ → ℝ) (T x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) * ∫ t : ℝ,
    Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) *
      (Complex.I * smoothedCharacteristicQuotient μ ν J T t)

noncomputable def smoothingFourierBound (μ ν : Measure ℝ) (T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t|

end ProbabilityFoundations.Ch09

namespace Specs.ProbabilityFoundations.Ch09.SmoothedCdfDifferenceInversion
open _root_.ProbabilityFoundations.Ch09

/-- The full integrable-quotient inversion stage of paper.tex:3269–3293.
The laws may have different means. Both first absolute moments are assumed. -/
def SmoothedCdfInversion : Prop :=
  ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (J : ℝ → ℝ), SmoothingKernel.KernelProperties J →
    ∀ (T : ℝ), 0 < T →
    Integrable (fun x : ℝ => |x|) μ → Integrable (fun x : ℝ => |x|) ν →
    let q := smoothedCharacteristicQuotient μ ν J T
    Continuous q ∧
    (∀ t : ℝ, t ≠ 0 → q t = smoothedCharacteristicDifference μ ν J T t / (t : ℂ)) ∧
    q 0 = Complex.I * ((∫ x : ℝ, x ∂μ) - (∫ x : ℝ, x ∂ν) : ℝ) ∧
    Function.support q ⊆ Icc (-T) T ∧
    Integrable q ∧
    (∀ x : ℝ, Integrable (fun t : ℝ =>
      Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) * (Complex.I * q t))) ∧
    Continuous (inverseSmoothedQuotient μ ν J T) ∧
    Tendsto (inverseSmoothedQuotient μ ν J T) atBot (𝓝 0) ∧
    (∀ x : ℝ, (smoothedCdf μ J T x - smoothedCdf ν J T x : ℂ) =
      inverseSmoothedQuotient μ ν J T x) ∧
    IntegrableOn (fun t : ℝ => ‖charFun μ t - charFun ν t‖ / |t|) (Icc (-T) T) ∧
    (∀ x : ℝ, |smoothedCdf μ J T x - smoothedCdf ν J T x| ≤
      smoothingFourierBound μ ν T) ∧
    (⨆ x : ℝ, |smoothedCdf μ J T x - smoothedCdf ν J T x|) ≤
      smoothingFourierBound μ ν T

end Specs.ProbabilityFoundations.Ch09.SmoothedCdfDifferenceInversion
