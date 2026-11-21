import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Bernstein
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Interior regularity and the endpoint counterexample in
`fa2:p1:bernstein-source-endpoint`. The real extension below agrees with the
original half-line function at every nonnegative time. Derivatives are only
asserted at strictly positive times, so its values at negative times are immaterial.
The restricted integral is precisely the finite-parameter part of the original
compactification, with no assumption that the atom at infinity vanishes. -/
noncomputable section

namespace ExpandedFA.P1.BernsteinInteriorSmooth
open MeasureTheory Set Bernstein
open scoped NNReal ENNReal

def realLaplaceTransform (ν : Measure ℝ≥0∞) (t : ℝ) : ℝ :=
  laplaceTransform ν t.toNNReal

def laplaceMoment (ν : Measure ℝ≥0∞) (m : ℕ) (t : ℝ) : ℝ :=
  ∫ rate in ({∞}ᶜ : Set ℝ≥0∞), rate.toReal ^ m * Real.exp (-rate.toReal * t) ∂ν

end ExpandedFA.P1.BernsteinInteriorSmooth

namespace Specs.ExpandedFA.P1.BernsteinInteriorSmooth
open _root_.ExpandedFA.P1.BernsteinInteriorSmooth
open _root_.ExpandedFA.P1.Bernstein MeasureTheory Set
open scoped NNReal ENNReal

def InteriorSmooth : Prop :=
  ∀ (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν],
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (realLaplaceTransform ν) (Ioi 0)

def AlternatingDerivatives : Prop :=
  ∀ (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν] (m : ℕ) (t : ℝ), 0 < t →
    Integrable (fun rate : ℝ≥0∞ => rate.toReal ^ m * Real.exp (-rate.toReal * t))
      (ν.restrict {∞}ᶜ) ∧
    (-1 : ℝ) ^ m * iteratedDeriv m (realLaplaceTransform ν) t = laplaceMoment ν m t ∧
    0 ≤ laplaceMoment ν m t

def EndpointCounterexample : Prop :=
  CompletelyMonotone infinityExponential ∧
    ¬ ∃ ν : Measure ℝ≥0, IsFiniteMeasure ν ∧ infinityExponential = finiteLaplaceTransform ν

end Specs.ExpandedFA.P1.BernsteinInteriorSmooth
