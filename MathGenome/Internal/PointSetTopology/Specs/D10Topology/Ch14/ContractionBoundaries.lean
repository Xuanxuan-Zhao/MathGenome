import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricComparison

/-! The four examples in paper.tex, d10:14:contraction-boundaries.
The intervals have exactly their usual real subspace metrics. Completeness
uses the canonical sequential definition fixed in Chapter 9. -/
namespace Specs.D10Topology.Ch14.ContractionBoundaries
open Specs.D10Topology.Ch09.MetricConventions
open Specs.D10Topology.Ch09.MetricComparison

/-- Halving on the usual open interval is a 1/2-contraction, but has no fixed point. -/
def interval_counterexample : Prop :=
  ¬ SequentiallyComplete (inferInstance : MetricSpace OpenUnitInterval).toPseudoMetricSpace ∧
  ∃ T : OpenUnitInterval → OpenUnitInterval,
    (∀ x, (T x).val = x.val / 2) ∧
    (∀ x y, dist (T x) (T y) ≤ (1 / 2 : ℝ) * dist x y) ∧
    ¬ ∃ x, T x = x

/-- Real translation is nonexpansive with constant one on a complete space. -/
def translation_counterexample : Prop :=
  SequentiallyComplete Real.metricSpace.toPseudoMetricSpace ∧
  ∃ T : ℝ → ℝ,
    (∀ x, T x = x + 1) ∧
    (∀ x y, dist (T x) (T y) ≤ (1 : ℝ) * dist x y) ∧
    ¬ ∃ x, T x = x

/-- Strict distance decrease on the complete closed ray still need not give a fixed point. -/
def strict_decrease_counterexample : Prop :=
  SequentiallyComplete (inferInstance : MetricSpace (Set.Ici (1 : ℝ))).toPseudoMetricSpace ∧
  ∃ T : Set.Ici (1 : ℝ) → Set.Ici (1 : ℝ),
    (∀ x, (T x).val = x.val + 1 / x.val) ∧
    (∀ x y, x ≠ y → dist (T x) (T y) < dist x y) ∧
    ¬ ∃ x, T x = x

/-- The empty metric space is complete, and its unique self-map has no fixed point. -/
def empty_counterexample : Prop :=
  SequentiallyComplete (inferInstance : MetricSpace Empty).toPseudoMetricSpace ∧
  ∃! T : Empty → Empty, ¬ ∃ x, T x = x

end Specs.D10Topology.Ch14.ContractionBoundaries
