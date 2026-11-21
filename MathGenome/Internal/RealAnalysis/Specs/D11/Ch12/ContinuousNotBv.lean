import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The displayed counterexample at paper.tex:4234–4247, with its endpoint
value and the explicitly adopted failure of absolute continuity. -/
namespace Specs.D11.Ch12.ContinuousNotBv

abbrev oscillation_type := ℝ → ℝ

/-- At zero this expression evaluates to zero; on `(0,1]` it is exactly
`x cos (π/(2x))`. Values outside `[0,1]` do not enter any obligation. -/
noncomputable def oscillation_value : oscillation_type :=
  fun x => x * Real.cos (Real.pi / (2 * x))

def continuous : Prop := ContinuousOn oscillation_value (Set.Icc 0 1)

def infinite_variation : Prop :=
  Specs.D11.Ch12.variation_value oscillation_value 0 1 = ⊤

def not_ac : Prop :=
  ¬ Specs.D11.Ch12.absolutelyContinuousOnIntervalValue oscillation_value 0 1

end Specs.D11.Ch12.ContinuousNotBv
