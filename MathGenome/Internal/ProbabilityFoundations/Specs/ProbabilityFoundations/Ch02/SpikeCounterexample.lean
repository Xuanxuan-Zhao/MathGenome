import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.ConvergenceComparisons
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The second example in paper.tex:719–723. The sample space is literally
`(0,1)`, with the induced Borel sigma algebra and Lebesgue measure pulled back
along inclusion. Index `n : ℕ` represents the positive integer `n+1`.
All moments use real powers, so every real `p > 0` is covered. -/
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Specs.ProbabilityFoundations.Ch02.SpikeCounterexample

abbrev Sample := Set.Ioo (0 : ℝ) 1
noncomputable def spikeMeasure : Measure Sample := Measure.comap Subtype.val volume
noncomputable def spike (p : ℝ) (n : ℕ) : Sample → ℝ :=
  {x : Sample | (x : ℝ) < 1 / ((n : ℝ) + 1)}.indicator
    (fun _ => ((n : ℝ) + 1) ^ (1 / p))

def probabilityType : Prop := IsProbabilityMeasure spikeMeasure

def measurableType : Prop := ∀ (p : ℝ) (n : ℕ), Measurable (spike p n)

def pointwiseType : Prop := ∀ (p : ℝ), 0 < p → ∀ x : Sample,
  Tendsto (fun n => spike p n x) atTop (𝓝 0)

def almostSureType : Prop := ∀ (p : ℝ), 0 < p →
  ∀ᵐ x ∂spikeMeasure, Tendsto (fun n => spike p n x) atTop (𝓝 0)

def probabilityConvergenceType : Prop := ∀ (p : ℝ), 0 < p →
  ∀ hP : IsProbabilityMeasure spikeMeasure,
  @Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces.ConvergesInProbabilityValue
    Sample ℝ _ _ spikeMeasure hP (spike p) (fun _ => 0)

def memLpType : Prop := ∀ (p : ℝ), 0 < p → ∀ n : ℕ,
  MemLp (spike p n) (ENNReal.ofReal p) spikeMeasure

def momentType : Prop := ∀ (p : ℝ), 0 < p → ∀ n : ℕ,
  ∫ x, |spike p n x| ^ p ∂spikeMeasure = 1

def notLpConvergenceType : Prop := ∀ (p : ℝ), 0 < p →
  ¬ Tendsto (fun n => ∫ x, |spike p n x - 0| ^ p ∂spikeMeasure) atTop (𝓝 0)

end Specs.ProbabilityFoundations.Ch02.SpikeCounterexample
