import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HilbertTripleTrace
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! The canonical real Hilbert triple, Bochner L² graph, and the complete
P201 time trace and product rule (paper.tex, Section C06, lines 440–500).
No extra regularity, separability, or finite dimensionality is assumed. -/
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
universe u v

namespace P201Specs.Common.TimeTrace
open ExpandedFA.Evolution
open HilbertTripleSpec HilbertTripleTraceSpec

/-- Reuse the canonical graph with the original two L² norms. -/
abbrev EnergySpace {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : HilbertTriple V H) (T : ℝ) := energySpaceValue j T

/-- Scalar pairing of the continuous representatives, extended only for
stating a real derivative. All assertions concern [0,T] or almost every (0,T). -/
def productCurve {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : ℝ} (f g : TraceCurve H T) (t : ℝ) : ℝ :=
  inner ℝ (extendCurve f t) (extendCurve g t)

/-- The complete conclusion, including the sharp averaged energy estimate.
The bound on differences expresses continuity for the sum of the L² norms.
The norm on `TraceCurve` is the supremum norm on the closed time interval. -/
def TimeTraceTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : HilbertTriple V H) (T : ℝ), 0 < T →
  ∃ trace : EnergySpace j T → TraceCurve H T,
    (∀ z, Represents j T z.val.1 (trace z)) ∧
    (∀ z (f : TraceCurve H T), Represents j T z.val.1 f → f = trace z) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z w,
      ‖trace z - trace w‖ ≤ C * (‖z.val.1 - w.val.1‖ + ‖z.val.2 - w.val.2‖)) ∧
    (∀ z (s t : Set.Icc 0 T),
      IntervalIntegrable (energyDensity T z.val.1 z.val.2) volume s.val t.val ∧
      ‖trace z t‖ ^ 2 - ‖trace z s‖ ^ 2 =
        2 * ∫ r in s.val..t.val, energyDensity T z.val.1 z.val.2 r) ∧
    (∀ z, ‖trace z‖ ^ 2 ≤
      T⁻¹ * ‖j.embedding.compLp z.val.1‖ ^ 2 + 2 * ‖z.val.2‖ * ‖z.val.1‖) ∧
    (∀ z w,
      let p := productCurve (trace z) (trace w)
      let d := fun r => z.val.2 r (w.val.1 r) + w.val.2 r (z.val.1 r)
      Integrable d (timeMeasureValue T) ∧
      AbsolutelyContinuousOnInterval p 0 T ∧
      (∀ᵐ r ∂timeMeasureValue T, HasDerivAt p (d r) r) ∧
      (∀ s t : Set.Icc 0 T,
        p t - p s = ∫ r in s.val..t.val, d r))

end P201Specs.Common.TimeTrace
