import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformContinuity

/-! Independent statements of paper.tex, d10:13:topology-comparison.
The order on `TopologicalSpace` is reverse inclusion of open families.
All domain spaces are arbitrary unless `CompactSpace` is explicitly present.
The metric-independence statement uses the fixed topological space C(X,Y),
so changing a compatible metric does not change the underlying function set. -/
noncomputable section
open Set Filter
open scoped Topology Uniformity
universe u v
namespace Specs.D10Topology.Ch13.TopologyComparison
open FunctionTopologies

def compactConvergenceTopology_le_pointwiseTopology : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y],
    compactConvergenceTopology (X := X) (Y := Y) ≤ pointwiseTopology

def uniformTopology_le_compactConvergenceTopology : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y],
    uniformTopology (X := X) (Y := Y) ≤ compactConvergenceTopology

def continuous_topology_comparisons : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y],
    uniformContinuousTopology (X := X) (Y := Y) ≤ compactConvergenceContinuousTopology ∧
    compactConvergenceContinuousTopology (X := X) (Y := Y) ≤ pointwiseContinuousTopology

def compactConvergenceContinuousTopology_eq_compactOpen : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y],
    compactConvergenceContinuousTopology (X := X) (Y := Y) = compactOpenContinuousTopology

def compactDomain_compactConvergenceTopology_eq_uniform : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] [CompactSpace X],
    compactConvergenceTopology (X := X) (Y := Y) = uniformTopology

def compactDomain_continuousTopologies_eq : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] [CompactSpace X],
    compactConvergenceContinuousTopology (X := X) (Y := Y) = uniformContinuousTopology ∧
    compactOpenContinuousTopology (X := X) (Y := Y) = uniformContinuousTopology

/-- Two arbitrary compatible metrics give the same uniform topology on C(X,Y).
Both sides use the same space of maps continuous for the given topology tY. -/
def compactDomain_uniformTopology_metric_independent : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X]
    (tY : TopologicalSpace Y) (m₁ m₂ : MetricSpace Y),
    m₁.toUniformSpace.toTopologicalSpace = tY →
    m₂.toUniformSpace.toTopologicalSpace = tY →
    TopologicalSpace.induced (fun f : @ContinuousMap X Y _ tY => (f : X → Y))
      (@uniformTopology X Y m₁) =
    TopologicalSpace.induced (fun f : @ContinuousMap X Y _ tY => (f : X → Y))
      (@uniformTopology X Y m₂)

/-- Even the singleton domain transfers the usual/arctan distinction to
function-space uniformities. This is compatible with equality of topologies. -/
def targetMetric_uniformity_counterexample : Prop :=
  Ch12.UniformContinuity.arctanMetric.toUniformSpace.toTopologicalSpace =
    Ch12.UniformContinuity.usualRealMetric.toUniformSpace.toTopologicalSpace ∧
  @uniformUniformity Unit ℝ Ch12.UniformContinuity.arctanMetric ≠
    @uniformUniformity Unit ℝ Ch12.UniformContinuity.usualRealMetric

end Specs.D10Topology.Ch13.TopologyComparison
