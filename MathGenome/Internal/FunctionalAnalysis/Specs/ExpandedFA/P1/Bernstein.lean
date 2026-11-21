import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BernsteinExtremes
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-! The closed-half-line Bernstein theorem, paper.tex:5522–5537 and
5568–5580. The compactified parameter interval is the native `ℝ≥0∞`,
with its order topology and Borel sigma algebra. No continuity premise at
zero is imposed. The exponential coordinate is exp(-rate), including its
value zero at infinity; the implementation must prove the displayed
finite-parameter and endpoint interpretations of the kernel. -/
noncomputable section

namespace ExpandedFA.P1.Bernstein
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- Exactly the manuscript's independent strictly positive increments. -/
def CompletelyMonotone (f : FunctionSpace) : Prop :=
  ∀ hs : List ℝ≥0, (∀ h ∈ hs, 0 < h) → ∀ t,
    0 ≤ alternatingDifference hs f t

/-- Continuous exponential coordinate on the actual compactified interval. -/
def exponentialCoordinate (rate : ℝ≥0∞) : ℝ := (EReal.exp (-(rate : EReal))).toReal

/-- At t = 0, real powers give 0^0 = 1, including rate = ∞. -/
def laplaceKernel (t : ℝ≥0) (rate : ℝ≥0∞) : ℝ := exponentialCoordinate rate ^ (t : ℝ)

def laplaceTransform (ν : Measure ℝ≥0∞) : FunctionSpace :=
  fun t => ∫ rate, laplaceKernel t rate ∂ν

def finiteLaplaceTransform (ν : Measure ℝ≥0) : FunctionSpace :=
  fun t => ∫ rate, Real.exp (-(rate : ℝ) * (t : ℝ)) ∂ν

end ExpandedFA.P1.Bernstein

namespace Specs.ExpandedFA.P1.Bernstein
open _root_.ExpandedFA.P1.Bernstein MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

def KernelInterpretation : Prop :=
  (∀ t rate : ℝ≥0, laplaceKernel t (rate : ℝ≥0∞) = Real.exp (-(rate : ℝ) * (t : ℝ))) ∧
  (∀ t : ℝ≥0, laplaceKernel t ∞ = if t = 0 then 1 else 0)

def Representation : Prop :=
  ∀ f : FunctionSpace, CompletelyMonotone f →
    ∃! ν : Measure ℝ≥0∞, IsFiniteMeasure ν ∧ f = laplaceTransform ν

/-- The limit and exact atom formula, without a right-continuity assumption. -/
def EndpointMass : Prop :=
  ∀ (f : FunctionSpace) (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν],
    f = laplaceTransform ν →
    ∃ L : ℝ, Tendsto f (𝓝[>] (0 : ℝ≥0)) (𝓝 L) ∧
      ν.real {∞} = f 0 - L

/-- Classical measures are native positive Borel measures on finite parameters.
Uniqueness is included in the continuity alternative. -/
def ClassicalRepresentation : Prop :=
  ∀ f : FunctionSpace, CompletelyMonotone f →
    (Tendsto f (𝓝[>] (0 : ℝ≥0)) (𝓝 (f 0)) ↔
      ∃! ν : Measure ℝ≥0, IsFiniteMeasure ν ∧ f = finiteLaplaceTransform ν)

end Specs.ExpandedFA.P1.Bernstein
