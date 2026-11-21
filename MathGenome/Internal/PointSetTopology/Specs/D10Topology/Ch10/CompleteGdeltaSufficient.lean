import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.GDelta.Basic

/-!
Independent specification for paper.tex, d10:10:complete-gdelta (b).
The ambient metric is complete in the manuscript's sequential sense. A G_delta
set carries the induced topology on its subtype. The conclusion quantifies over
a new metric and requires both equality of topologies and sequential completeness,
using the shared `CompletelyMetrizable` definition. No nonemptiness, separability,
or condition on the complements of the open sets is imposed.
-/

universe u

namespace Specs.D10Topology.Ch10.CompleteGdeltaSufficient
open Specs.D10Topology.Ch09.MetricConventions

def complete_gdelta_sufficient : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X),
    SequentiallyComplete d.toPseudoMetricSpace →
    @IsGδ X (metricTopology d.toPseudoMetricSpace) A →
    CompletelyMetrizable
      ((metricTopology d.toPseudoMetricSpace).induced (Subtype.val : A → X))

end Specs.D10Topology.Ch10.CompleteGdeltaSufficient
