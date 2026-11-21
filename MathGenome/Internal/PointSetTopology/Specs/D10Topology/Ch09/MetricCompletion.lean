import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.MetricSpace.Completion

/-! Independent specification for d10:09:completion. The chosen model is the
Hausdorff uniform completion equipped with its extending finite-valued metric.
All propositions below concern the specified metric, including on empty spaces.
-/

universe u

namespace Specs.D10Topology.Ch09.MetricCompletion

open MetricConventions

def completionType := {X : Type u} → MetricSpace X → Type u
def completionValue : completionType := fun d =>
  @UniformSpace.Completion _ d.toUniformSpace

def completionMetricType := {X : Type u} → (d : MetricSpace X) →
  MetricSpace (completionValue d)
noncomputable def completionMetricValue : completionMetricType := fun d =>
  @UniformSpace.Completion.instMetricSpace _ d.toPseudoMetricSpace

def completionEmbeddingType := {X : Type u} → (d : MetricSpace X) →
  X → completionValue d
def completionEmbeddingValue : completionEmbeddingType := fun d =>
  @UniformSpace.Completion.coe' _ d.toUniformSpace

def completion_complete : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    SequentiallyComplete (completionMetricValue d).toPseudoMetricSpace

def completion_isometry : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    Isometry d.toPseudoMetricSpace (completionMetricValue d).toPseudoMetricSpace
      (completionEmbeddingValue d)

def completion_injective : Prop :=
  ∀ {X : Type u} (d : MetricSpace X), Function.Injective (completionEmbeddingValue d)

def completion_isEmbedding : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    @Topology.IsEmbedding X (completionValue d)
      (metricTopology d.toPseudoMetricSpace)
      (metricTopology (completionMetricValue d).toPseudoMetricSpace)
      (completionEmbeddingValue d)

def completion_dense : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    @DenseRange (completionValue d)
      (metricTopology (completionMetricValue d).toPseudoMetricSpace) X
      (completionEmbeddingValue d)

def completion_empty : Prop :=
  ∀ {X : Type u} [IsEmpty X] (d : MetricSpace X), IsEmpty (completionValue d)

/-- The source existence conclusion, with the embedding topology made explicit. -/
def exists_metric_completion : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    ∃ (Xhat : Type u) (e : MetricSpace Xhat) (j : X → Xhat),
      SequentiallyComplete e.toPseudoMetricSpace ∧
      Isometry d.toPseudoMetricSpace e.toPseudoMetricSpace j ∧
      Function.Injective j ∧
      @Topology.IsEmbedding X Xhat (metricTopology d.toPseudoMetricSpace)
        (metricTopology e.toPseudoMetricSpace) j ∧
      @DenseRange Xhat (metricTopology e.toPseudoMetricSpace) X j

end Specs.D10Topology.Ch09.MetricCompletion
