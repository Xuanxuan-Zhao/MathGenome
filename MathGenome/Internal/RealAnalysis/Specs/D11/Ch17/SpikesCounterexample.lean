import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! The concentration example in paper.tex:5292–5301. `Line` is the canonical one-dimensional Euclidean space with completed
Lebesgue measure, and `intervalMeasure` is its restriction to (0,1).
We use zero extensions to this line; the measure is supported on (0,1), so
all integrals and measure convergence statements are on that interval.
Natural index n represents the source's positive integer n+1. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

namespace D11.Ch17.SpikesCounterexample

open D11.Ch03

abbrev Line := Point 1

local instance : MeasurableSpace Line :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1

def intervalMeasure : Measure Line :=
  (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1).restrict
    (openBox (fun _ => 0) (fun _ => 1))

def support (n : ℕ) : Set Line :=
  openBox (fun _ => 0) (fun _ => 1 / ((n : ℝ) + 1))

def spike (n : ℕ) : Line → ℝ :=
  (support n).indicator (fun _ => (n : ℝ) + 1)

end D11.Ch17.SpikesCounterexample

namespace Specs.D11.Ch17.SpikesCounterexample
open _root_.D11.Ch17.SpikesCounterexample
local instance : MeasurableSpace Line :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1
open Specs.D11.Ch17.UniformControls Specs.D11.Ch07.ConvergenceDefinitions

def support_measure : Prop := ∀ n : ℕ,
  intervalMeasure (support n) = ENNReal.ofReal (1 / ((n : ℝ) + 1))

def support_measure_tendsto : Prop :=
  Tendsto (fun n => intervalMeasure (support n)) atTop (𝓝 0)

def measurable_spike : Prop := ∀ n : ℕ, Measurable (spike n)

def integrable_spike : Prop := ∀ n : ℕ,
  Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value intervalMeasure (spike n)

def norm_one : Prop := ∀ n : ℕ,
  Specs.D11.Ch10.LpDefinition.powerNorm_value intervalMeasure 1 (spike n) = 1

def support_integral_one : Prop := ∀ n : ℕ,
  absoluteIntegral_value intervalMeasure (spike n) (support n) = 1

def uniformly_bounded : Prop := uniformL1Bound_value intervalMeasure spike

def pointwise_zero : Prop := pointwiseConverges_value spike (fun _ => 0)

def ae_zero : Prop := aeConverges_value intervalMeasure spike (fun _ => 0)

def in_measure_zero : Prop := inMeasureConverges_value intervalMeasure spike (fun _ => 0)

def not_uiSmall : Prop := ¬ uiSmall_value intervalMeasure spike

def not_L1_zero : Prop := ¬ lpConverges_value intervalMeasure 1 spike (fun _ => 0)

/-- There is no L1 limit, including a proposed nonzero limit. -/
def not_L1_converges : Prop := ∀ g : Line → ℝ,
  ¬ lpConverges_value intervalMeasure 1 spike g

end Specs.D11.Ch17.SpikesCounterexample
