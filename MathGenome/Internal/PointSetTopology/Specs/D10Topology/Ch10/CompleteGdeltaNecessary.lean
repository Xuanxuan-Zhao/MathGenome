import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.GDelta.Basic

/-! Independent statement of paper.tex, d10:10:complete-gdelta (a).
The metric witnessing complete metrizability is arbitrary and is required
only to induce the subspace topology. The ambient metric need not be complete.
There is no nonemptiness or countability hypothesis. -/

universe u
namespace Specs.D10Topology.Ch10.CompleteGdeltaNecessary

open Specs.D10Topology.Ch09.MetricConventions

def complete_subspace_is_gdelta : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X),
    CompletelyMetrizable
      (TopologicalSpace.induced (Subtype.val : A → X)
        (metricTopology d.toPseudoMetricSpace)) →
    @IsGδ X (metricTopology d.toPseudoMetricSpace) A

end Specs.D10Topology.Ch10.CompleteGdeltaNecessary
