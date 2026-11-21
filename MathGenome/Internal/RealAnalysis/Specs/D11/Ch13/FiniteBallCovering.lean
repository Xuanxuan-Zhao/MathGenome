import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

/-! Independent statement of paper.tex:4355–4361. The balls are open balls
in the Euclidean norm on `Point d`. The measure is the full Carathéodory
Lebesgue measure from Chapter 3, not just its Borel restriction. A finite
index set can be empty, and no distinctness of input centers is required. -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Specs.D11.Ch13.FiniteBallCovering

open _root_.D11.Ch03 Specs.D11.Ch03.LebesgueMeasures

/-- Select a disjoint subfamily whose concentric triple-radius open balls
cover the original union, with the stated quantitative bound. -/
def finite_ball_covering : Prop :=
  ∀ (d : ℕ) [NeZero d] {ι : Type*} (s : Finset ι)
    (c : ι → Point d) (r : ι → ℝ),
    (∀ i ∈ s, 0 < r i) →
    ∃ t : Finset ι, t ⊆ s ∧
      (↑t : Set ι).PairwiseDisjoint (fun i => Metric.ball (c i) (r i)) ∧
      (⋃ i ∈ s, Metric.ball (c i) (r i)) ⊆
        (⋃ j ∈ t, Metric.ball (c j) (3 * r j)) ∧
      lebesgue_value d (⋃ i ∈ s, Metric.ball (c i) (r i)) ≤
        (3 : ℝ≥0∞) ^ d * ∑ j ∈ t, lebesgue_value d (Metric.ball (c j) (r j))

end Specs.D11.Ch13.FiniteBallCovering
