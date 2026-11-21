import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Algebra.Group.Basic

/-! Statements for the intrinsic-completeness remark, paper.tex:6066–6080.
The results hold for additive commutative groups, hence in particular for TVSs.
A compatible invariant metric is supplied explicitly; no preexisting uniform
structure, complete metric, or completeness certificate is assumed. -/

open Set Filter Topology
universe u v

namespace ExpandedFA.IntrinsicCompleteness

/-- The intrinsic Cauchy condition uses only the topology and subtraction. -/
def ZeroCauchy {E : Type u} [AddCommGroup E] [TopologicalSpace E]
    {ι : Type v} [Preorder ι] (a : ι → E) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), ∃ i, ∀ j, i ≤ j → ∀ k, i ≤ k → a j - a k ∈ U

/-- A metric inducing the given topology and invariant under translations. -/
structure CompatibleInvariantMetric (E : Type u) [AddCommGroup E]
    [t : TopologicalSpace E] where
  metric : MetricSpace E
  compatible : metric.toUniformSpace.toTopologicalSpace = t
  invariant : ∀ x y z : E,
    @dist E metric.toDist (x + z) (y + z) = @dist E metric.toDist x y

/-- The ordinary epsilon-tail condition for the specified metric. -/
def MetricCauchy {E : Type u} [AddCommGroup E] [TopologicalSpace E]
    (d : CompatibleInvariantMetric E) {ι : Type v} [Preorder ι] (a : ι → E) : Prop :=
  ∀ ε > (0 : ℝ), ∃ i, ∀ j, i ≤ j → ∀ k, i ≤ k →
    @dist E d.metric.toDist (a j) (a k) < ε

/-- All intrinsically Cauchy directed nets in the space's universe converge. -/
def NetComplete (E : Type u) [AddCommGroup E] [TopologicalSpace E] : Prop :=
  ∀ (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (a : ι → E), ZeroCauchy a → ∃ x, Tendsto a atTop (𝓝 x)

/-- The same condition restricted to sequences. -/
def SequenceComplete (E : Type u) [AddCommGroup E] [TopologicalSpace E] : Prop :=
  ∀ a : ℕ → E, ZeroCauchy a → ∃ x, Tendsto a atTop (𝓝 x)

end ExpandedFA.IntrinsicCompleteness

namespace Specs.ExpandedFA.IntrinsicCompleteness
open _root_.ExpandedFA.IntrinsicCompleteness

/-- The neighborhood and metric definitions of Cauchy agree. -/
def cauchyCriterion : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [TopologicalSpace E]
    (d : CompatibleInvariantMetric E) (ι : Type v) [Preorder ι] (a : ι → E),
    ZeroCauchy a ↔ MetricCauchy d a

/-- Any two compatible invariant metrics have the same Cauchy nets. -/
def metricIndependence : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [TopologicalSpace E]
    (d e : CompatibleInvariantMetric E) (ι : Type v) [Preorder ι] (a : ι → E),
    MetricCauchy d a ↔ MetricCauchy e a

/-- Metric completeness gives convergence for directed nets in any universe. -/
def completeMetricNets : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [TopologicalSpace E]
    (d : CompatibleInvariantMetric E), @CompleteSpace E d.metric.toUniformSpace →
    ∀ (ι : Type v) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
      (a : ι → E), ZeroCauchy a → ∃ x, Tendsto a atTop (𝓝 x)

/-- Completeness of the supplied metric equals intrinsic net completeness. -/
def completeMetricIffNet : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [TopologicalSpace E]
    (d : CompatibleInvariantMetric E),
    @CompleteSpace E d.metric.toUniformSpace ↔ NetComplete E

/-- Sequence completeness uses the same Cauchy condition. -/
def completeMetricIffSequence : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [TopologicalSpace E]
    (d : CompatibleInvariantMetric E),
    @CompleteSpace E d.metric.toUniformSpace ↔ SequenceComplete E

/-- For an invariant-metrizable topology, sequences suffice for all nets. -/
def sequenceIffNet : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [TopologicalSpace E]
    (_d : CompatibleInvariantMetric E), SequenceComplete E ↔ NetComplete E

/-- Invariant-metric completeness is independent of the metric choice. -/
def completeMetricIndependence : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [TopologicalSpace E]
    (d e : CompatibleInvariantMetric E),
    @CompleteSpace E d.metric.toUniformSpace ↔ @CompleteSpace E e.metric.toUniformSpace

/-- Arbitrary compatible metrics on the real TVS can lose completeness. -/
def nonInvariantCounterexample : Prop :=
  CompleteSpace ℝ ∧ ∃ m : MetricSpace ℝ,
    m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace ℝ) ∧
    ¬ @CompleteSpace ℝ m.toUniformSpace

end Specs.ExpandedFA.IntrinsicCompleteness
