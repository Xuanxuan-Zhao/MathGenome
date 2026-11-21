import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions

/-! Independent statement of the Cauchy-subsequence equivalence in
`paper.tex`, d10:09:total-bounded-basics. The subsequence indices are strictly
increasing natural numbers. No nonemptiness or infinitude assumption is made. -/

universe u

namespace Specs.D10Topology.Ch09.TotalBoundedSequences
open Specs.D10Topology.Ch09.MetricConventions

/-- Total boundedness is equivalent to the existence of a Cauchy subsequence
of every sequence, for the specified metric. -/
def totallyBounded_iff_cauchy_subsequence : Prop :=
  ∀ {X : Type u} [d : MetricSpace X],
    TotallyBounded d.toPseudoMetricSpace ↔
      ∀ s : ℕ → X, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        CauchySequence d.toPseudoMetricSpace (s ∘ φ)

end Specs.D10Topology.Ch09.TotalBoundedSequences
