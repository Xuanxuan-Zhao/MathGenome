import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.Real.Sqrt

/-! Independent statements for `paper.tex`, Example d10:18:rational-incomplete.
The metric is fixed to the standard rational metric, induced by the real
absolute difference. Completeness has the epsilon/sequence meaning of chapter 9.
-/

namespace Specs.D10Topology.Ch18.RationalIncomplete
open Specs.D10Topology.Ch09.MetricConventions

/-- Identify the displayed metric with the source's usual absolute difference. -/
def rational_distance : Prop :=
  ∀ p q : ℚ, distance (inferInstance : PseudoMetricSpace ℚ) p q =
    |(p : ℝ) - (q : ℝ)|

/-- A Cauchy sequence with real limit √2 and with no rational limit. -/
def rational_cauchy_without_limit : Prop :=
  ∃ s : ℕ → ℚ,
    CauchySequence (inferInstance : PseudoMetricSpace ℚ) s ∧
    SequenceConverges (inferInstance : PseudoMetricSpace ℝ)
      (fun n => (s n : ℝ)) (Real.sqrt 2) ∧
    ∀ q : ℚ, ¬ SequenceConverges (inferInstance : PseudoMetricSpace ℚ) s q

/-- The usual rational metric is not complete. -/
def rational_not_complete : Prop :=
  ¬ SequentiallyComplete (inferInstance : PseudoMetricSpace ℚ)

end Specs.D10Topology.Ch18.RationalIncomplete
