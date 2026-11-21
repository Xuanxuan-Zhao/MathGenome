import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.Instances.Rat

/-!
Independent statements for paper.tex, Example d10:11:rationals.
The rational numbers carry their canonical metric topology, induced from ℝ.
Local compactness here is the source's one-compact-neighborhood predicate.
-/

open Set Topology

namespace Specs.D10Topology.Ch11.RationalsNotLocallyCompact

def rational_topology_induced : Prop :=
  (inferInstance : TopologicalSpace ℚ) =
    TopologicalSpace.induced ((↑) : ℚ → ℝ) (inferInstance : TopologicalSpace ℝ)

def rational_no_compact_neighborhood : Prop :=
  ∀ (q : ℚ) (K : Set ℚ), IsCompact K → K ∉ 𝓝 q

def rational_not_locallyCompact : Prop :=
  ¬ LocalCompactConventions.LocallyCompact ℚ

def rational_metrizable : Prop :=
  Specs.D10Topology.Ch09.MetricConventions.Metrizable
    (inferInstance : TopologicalSpace ℚ)

def real_lch : Prop := LocalCompactConventions.LCH ℝ

/-- The embedding identifies ℚ with a metrizable subspace of an LCH space,
and its induced topology fails source local compactness. -/
def rational_subspace_counterexample : Prop :=
  IsEmbedding ((↑) : ℚ → ℝ) ∧
    Specs.D10Topology.Ch09.MetricConventions.Metrizable
      (inferInstance : TopologicalSpace ℚ) ∧
    LocalCompactConventions.LCH ℝ ∧ ¬ LocalCompactConventions.LocallyCompact ℚ

end Specs.D10Topology.Ch11.RationalsNotLocallyCompact
