import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.StieltjesExistence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The example fa2:p3:moment-nonuniqueness, paper.tex.
We represent measures on (0,∞) by their zero extensions to ℝ. The restricted
Lebesgue measure in `measureValue` retains exactly the displayed density on
that open half-line, and assigns no mass at zero or on the negative half-line.
All absolute moments and pairwise distinction are explicit obligations. -/
noncomputable section
open MeasureTheory Set
namespace ExpandedFA.Moments.IndeterminateStieltjesExample

/-- The real density in the manuscript, before extension by zero. -/
def densityValue (a x : ℝ) : ℝ :=
  Real.exp (-(Real.log x) ^ 2) / (Real.sqrt Real.pi * x) *
    (1 + a * Real.sin (2 * Real.pi * Real.log x))

/-- The prescribed positive Borel measure, using the open positive half-line. -/
def measureValue (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (densityValue a x))

/-- The common moment sequence. -/
def sequenceValue (n : ℕ) : ℝ := Real.exp ((n : ℝ) ^ 2 / 4)

namespace Spec

def DensityNonnegative : Prop := ∀ a ∈ Icc (-1 : ℝ) 1,
  ∀ x ∈ Ioi (0 : ℝ), 0 ≤ densityValue a x

def MeasureProperties : Prop := ∀ a ∈ Icc (-1 : ℝ) 1,
  IsProbabilityMeasure (measureValue a) ∧ measureValue a (Iic 0) = 0 ∧
    StieltjesExistence.Represents (measureValue a) sequenceValue ∧
    ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) (measureValue a)

def Distinct : Prop := ∀ a ∈ Icc (-1 : ℝ) 1, ∀ b ∈ Icc (-1 : ℝ) 1,
  a ≠ b → measureValue a ≠ measureValue b

/-- Both Hankel forms are positive, yet there are distinct representing measures. -/
def Indeterminate : Prop := HankelNonnegative sequenceValue ∧
  HankelNonnegative (StieltjesExistence.shiftedMoments sequenceValue) ∧
  ∃ μ ν : Measure ℝ, StieltjesExistence.Represents μ sequenceValue ∧
    StieltjesExistence.Represents ν sequenceValue ∧ μ ≠ ν

end Spec
end ExpandedFA.Moments.IndeterminateStieltjesExample
