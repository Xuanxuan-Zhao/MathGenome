import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions

/-! Independent statement of paper.tex, d10:14:banach.
The metric, sequential completeness and epsilon convergence are the canonical
Chapter 9 objects. Iteration starts at zero, with no positivity assumption on q.
All estimates concern the same fixed point, for every initial point. -/
universe u

namespace Specs.D10Topology.Ch14.Banach
open Specs.D10Topology.Ch09.MetricConventions

def banach_contraction : Prop :=
  ∀ {X : Type u} (d : MetricSpace X), Nonempty X →
    SequentiallyComplete d.toPseudoMetricSpace →
    ∀ (T : X → X) (q : ℝ), 0 ≤ q → q < 1 →
    (∀ x y, distance d.toPseudoMetricSpace (T x) (T y) ≤
      q * distance d.toPseudoMetricSpace x y) →
    ∃ p : X, T p = p ∧
      (∀ p' : X, T p' = p' → p' = p) ∧
      (∀ x₀ : X,
        SequenceConverges d.toPseudoMetricSpace (fun n : ℕ => T^[n] x₀) p ∧
        (∀ n : ℕ, distance d.toPseudoMetricSpace (T^[n] x₀) p ≤
          q ^ n / (1 - q) * distance d.toPseudoMetricSpace (T^[1] x₀) x₀) ∧
        (∀ n : ℕ, distance d.toPseudoMetricSpace (T^[n] x₀) p ≤
          1 / (1 - q) * distance d.toPseudoMetricSpace (T^[n + 1] x₀) (T^[n] x₀)) ∧
        (∀ n : ℕ, 1 ≤ n → distance d.toPseudoMetricSpace (T^[n] x₀) p ≤
          q / (1 - q) * distance d.toPseudoMetricSpace (T^[n] x₀) (T^[n - 1] x₀))) ∧
      (∀ z : X, distance d.toPseudoMetricSpace z p ≤
        distance d.toPseudoMetricSpace z (T z) / (1 - q))

end Specs.D10Topology.Ch14.Banach
