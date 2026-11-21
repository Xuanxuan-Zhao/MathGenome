import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricCompletion
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness

/-! Independent statements for paper.tex, d10:09:precompact-completion.
The completion carries its canonical extending metric. Subsets carry the
restricted metric, including its requirement that finite ball centers belong
to the subset. None of the statements assumes a nonempty space or subset. -/

open Set
universe u

namespace Specs.D10Topology.Ch09.PrecompactCompletion

open MetricConventions MetricCompletion
open Specs.D10Topology.Ch05.Compactness

def totallyBounded_iff_completion_compact : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    TotallyBounded d.toPseudoMetricSpace ↔
      @CoverCompact (completionValue d)
        (metricTopology (completionMetricValue d).toPseudoMetricSpace)

def closure_compact_iff_totallyBounded : Prop :=
  ∀ {X : Type u} [d : MetricSpace X] (A : Set X),
    SequentiallyComplete d.toPseudoMetricSpace →
      (SubspaceCompact (closure A) ↔
        TotallyBounded (inferInstance : MetricSpace A).toPseudoMetricSpace)

def uniformlyEquivalent_totallyBounded_subsets : Prop :=
  ∀ {X : Type u} (d e : MetricSpace X),
    UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace →
      ∀ A : Set X,
        TotallyBounded
          (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace ↔
        TotallyBounded
          (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective e).toPseudoMetricSpace

end Specs.D10Topology.Ch09.PrecompactCompletion
