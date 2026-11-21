import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions

/-!
Independent statement of paper.tex:2382–2393, Fatou for convergence in measure.
The functions are finite real-valued, measurable in the original sigma-algebra,
and nonnegative everywhere. Convergence uses the shared global strict-deviation
definition. The integral is the shared nonnegative simple-minorant integral,
applied through `ENNReal.ofReal`, which agrees with a nonnegative real value.
Both integral values and their lower limit may be infinite. No assumption on
total mass, sigma-finiteness, or completeness is imposed.
-/

open Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace Specs.D11.Ch07.FatouMeasure

open Specs.D11.Ch07.ConvergenceDefinitions
open Specs.D11.Ch05.NonnegativeIntegral

def fatou_measure : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ) (g : X → ℝ),
    (∀ n, Measurable (f n)) → Measurable g →
    (∀ n x, 0 ≤ f n x) → (∀ x, 0 ≤ g x) →
    inMeasureConverges_value μ f g →
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal (g x)) ≤
      liminf (fun n => nonnegativeIntegral_value μ
        (fun x => ENNReal.ofReal (f n x))) atTop

end Specs.D11.Ch07.FatouMeasure
