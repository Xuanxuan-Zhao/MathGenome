import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import Mathlib.Topology.Separation.Regular

/-!
Independent statements for paper.tex, Theorem d10:15:metric-paracompact.
The conclusion is the canonical open-cover/locally-finite-open-refinement
property, without Hausdorffness. Regularity does not include T₁. The metric
assertion uses exactly the topology of the specified metric. Compactness is
the manuscript's open-cover predicate. Empty spaces are allowed throughout.
-/

universe u

namespace Specs.D10Topology.Ch15.StandardParacompactness

def metric_paracompact : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    @LocallyFiniteConventions.Paracompact X
      (Ch09.MetricConventions.metricTopology d.toPseudoMetricSpace)

def regular_lindelof_paracompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    RegularSpace X → LindelofSpace X → LocallyFiniteConventions.Paracompact X

def compact_paracompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    Ch05.Compactness.CoverCompact X → LocallyFiniteConventions.Paracompact X

end Specs.D10Topology.Ch15.StandardParacompactness
