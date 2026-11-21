import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.LebesgueDifferentiation

/-! Density in centered Euclidean open balls, paper.tex:4428–4437.
The set is measurable for the completed Lebesgue structure and need not
have finite measure. For positive radii the ball and its intersection with
the set have finite measure, and the denominator is strictly positive. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace Specs.D11.Ch13.DensityPoints
open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := lebesgueSpace_value n

/-- One measurable null exceptional set gives density one inside `E` and
density zero outside `E`, with no hypothesis on its total measure. -/
def density_points : Prop :=
  ∀ {n : ℕ} [NeZero n] (E : Set (Point n)), MeasurableSet E →
    ∃ N : Set (Point n), MeasurableSet N ∧ lebesgue_value n N = 0 ∧
      ∀ x ∉ N,
        (x ∈ E → Tendsto
          (fun r : ℝ => (lebesgue_value n (E ∩ Metric.ball x r)).toReal /
            (lebesgue_value n (Metric.ball x r)).toReal)
          (𝓝[>] (0 : ℝ)) (𝓝 1)) ∧
        (x ∉ E → Tendsto
          (fun r : ℝ => (lebesgue_value n (E ∩ Metric.ball x r)).toReal /
            (lebesgue_value n (Metric.ball x r)).toReal)
          (𝓝[>] (0 : ℝ)) (𝓝 0))

end Specs.D11.Ch13.DensityPoints
