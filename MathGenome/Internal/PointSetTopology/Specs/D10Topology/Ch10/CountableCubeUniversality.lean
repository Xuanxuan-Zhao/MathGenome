import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.UrysohnMetrization
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness

/-! Independent statements for paper.tex, `d10:10:hilbert-cube-universal`.
The countable cube uses positive natural indices and the product of the usual
subspace topologies on [0,1]. All statements include empty spaces.
A compatible totally bounded metric is an existential metric on the original
set with exactly its given topology, with no constraint on a prior uniformity. -/

open Topology TopologicalSpace
universe u

namespace Specs.D10Topology.Ch10.CountableCubeUniversality

open Ch09.MetricConventions

def cube_iff_secondCountable_t3 : Prop :=
  ∀ {X : Type u} [TopologicalSpace X],
    (∃ e : X → (ℕ+ → unitInterval), IsEmbedding e) ↔
      SecondCountableTopology X ∧ (RegularSpace X ∧ T1Space X)

def cube_iff_separable_metrizable : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    (∃ e : X → (ℕ+ → unitInterval), IsEmbedding e) ↔
      SeparableSpace X ∧ Metrizable t

def compact_hausdorff_secondCountable_metrizable : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    Ch05.Compactness.CoverCompact X → T2Space X → SecondCountableTopology X →
      Metrizable t

def cube_embedding_totallyBounded_metric : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (e : X → (ℕ+ → unitInterval)),
    IsEmbedding e → ∃ d : MetricSpace X,
      metricTopology d.toPseudoMetricSpace = t ∧ TotallyBounded d.toPseudoMetricSpace

def compatible_totallyBounded_metric_iff_separable : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X], Metrizable t →
    ((∃ d : MetricSpace X, metricTopology d.toPseudoMetricSpace = t ∧
      TotallyBounded d.toPseudoMetricSpace) ↔ SeparableSpace X)

end Specs.D10Topology.Ch10.CountableCubeUniversality
