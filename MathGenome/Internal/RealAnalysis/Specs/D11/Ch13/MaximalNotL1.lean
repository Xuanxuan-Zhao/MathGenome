import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.AveragesMaximalDefinition
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The fixed one-dimensional example in paper.tex:4544–4549.
The shared Euclidean line is identified with ℝ by its sole coordinate.
Nonintegrability of the extended nonnegative maximal function means that
its nonnegative integral is infinite, without totalizing any scalar integral. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D11.Ch13.MaximalNotL1
open _root_.D11.Ch03

local instance : MeasurableSpace (Point 1) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1

def indicator_type := Point 1 → ℝ

def indicator_value : indicator_type :=
  (closedBox (fun _ => 0) (fun _ => 1)).indicator 1

def indicator_locallyIntegrable : Prop :=
  Specs.D11.Ch13.AveragesMaximalDefinition.locallyIntegrable_value indicator_value

def indicator_integrable_norm_one : Prop :=
  Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
    (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1) indicator_value ∧
  (∫ y, ‖indicator_value y‖ ∂(Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1)) = 1

def maximal_lower_bound : Prop :=
  ∀ (hf : Specs.D11.Ch13.AveragesMaximalDefinition.locallyIntegrable_value indicator_value)
    (x : ℝ), 2 ≤ x →
    ENNReal.ofReal (1 / (2 * x)) ≤
      Specs.D11.Ch13.AveragesMaximalDefinition.maximal_value indicator_value hf
        (WithLp.toLp 2 (fun _ : Fin 1 => x))

def maximal_integral_top : Prop :=
  ∀ (hf : Specs.D11.Ch13.AveragesMaximalDefinition.locallyIntegrable_value indicator_value),
    (∫⁻ y, Specs.D11.Ch13.AveragesMaximalDefinition.maximal_value indicator_value hf y
      ∂(Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1)) = ∞

end Specs.D11.Ch13.MaximalNotL1
