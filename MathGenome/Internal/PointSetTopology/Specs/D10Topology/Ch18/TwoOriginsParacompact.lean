import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.TwoOriginsTopology
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions

/-! Independent statement of the remaining assertion in paper.tex,
`d10:18:two-origins`. The topology is the disjoint-sum quotient topology.
Paracompactness has its open-cover meaning, without a separation axiom. -/

open Set TopologicalSpace
open scoped Topology

namespace Specs.D10Topology.Ch18.TwoOriginsParacompact
open _root_.D10Topology.Ch18.TwoOriginsData

/-- Every open cover of the actual doubled-origin quotient has a locally finite
open refinement. -/
def paracompact : Prop := ParacompactSpace Line

/-- The same example is locally metrizable and second countable, paracompact,
but neither Hausdorff nor metrizable. This retains its role in explaining the
Hausdorff hypothesis of the local metrization theorem. -/
def smirnov_counterexample : Prop :=
  ParacompactSpace Line ∧
    (∀ q : Line, ∃ U : Set Line, IsOpen U ∧ q ∈ U ∧ MetrizableSpace U) ∧
    SecondCountableTopology Line ∧ ¬ T2Space Line ∧ ¬ MetrizableSpace Line

end Specs.D10Topology.Ch18.TwoOriginsParacompact
