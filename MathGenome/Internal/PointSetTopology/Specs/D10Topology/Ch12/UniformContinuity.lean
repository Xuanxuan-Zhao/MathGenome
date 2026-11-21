import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformTopology
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Independent specification for paper.tex, d10:12:continuity-calculus.
The two metrics are structures on the same underlying real type. All metric
and uniform-space parameters below are explicit where their choice matters.
Natural indices begin at zero; this does not change any tail assertion. -/

open Set Filter
open scoped Topology Uniformity
universe u v w

namespace Specs.D10Topology.Ch12.UniformContinuity

open UniformConventions UniformTopology
open Ch09.MetricConventions

@[instance_reducible] noncomputable def usualRealMetric : MetricSpace ℝ := inferInstance
@[instance_reducible] noncomputable def arctanMetric : MetricSpace ℝ :=
  MetricSpace.induced Real.arctan Real.arctan_injective usualRealMetric

def realMetricType := MetricSpace ℝ
noncomputable def usualRealMetricValue : realMetricType := usualRealMetric
noncomputable def arctanMetricValue : realMetricType := arctanMetric

def entourageContinuous_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (f : X → Y),
    EntourageContinuous f → @Continuous X Y uniformTopology uniformTopology f

def entourageContinuous_id : Prop :=
  ∀ {X : Type u} [UniformSpace X], EntourageContinuous (id : X → X)

def entourageContinuous_comp : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [UniformSpace X] [UniformSpace Y] [UniformSpace Z] (f : X → Y) (g : Y → Z),
    EntourageContinuous f → EntourageContinuous g → EntourageContinuous (g ∘ f)

def usualRealMetric_distance : Prop := ∀ x y : ℝ,
  distance usualRealMetric.toPseudoMetricSpace x y = |x - y|

def arctanMetric_distance : Prop := ∀ x y : ℝ,
  distance arctanMetric.toPseudoMetricSpace x y = |Real.arctan x - Real.arctan y|

def arctanMetric_topology : Prop :=
  metricTopology arctanMetric.toPseudoMetricSpace =
    metricTopology usualRealMetric.toPseudoMetricSpace

def usualRealMetric_complete : Prop :=
  @Complete ℝ usualRealMetric.toUniformSpace

def arctanMetric_nat_cauchy : Prop :=
  CauchySequence arctanMetric.toPseudoMetricSpace (fun n : ℕ => (n : ℝ))

def arctanMetric_nat_no_limit : Prop :=
  ¬ ∃ x : ℝ, SequenceConverges arctanMetric.toPseudoMetricSpace (fun n : ℕ => (n : ℝ)) x

def arctanMetric_incomplete : Prop :=
  ¬ @Complete ℝ arctanMetric.toUniformSpace

def arctanMetric_adjacent_tendsto : Prop :=
  Tendsto (fun n : ℕ => distance arctanMetric.toPseudoMetricSpace
    (n : ℝ) ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ))

def usualRealMetric_adjacent : Prop := ∀ n : ℕ,
  distance usualRealMetric.toPseudoMetricSpace (n : ℝ) ((n : ℝ) + 1) = 1

def arctanMetric_id_not_uniform : Prop :=
  ¬ @EntourageContinuous ℝ ℝ arctanMetric.toUniformSpace
    usualRealMetric.toUniformSpace id

def arctanMetric_uniformity_ne : Prop :=
  arctanMetric.toUniformSpace ≠ usualRealMetric.toUniformSpace

end Specs.D10Topology.Ch12.UniformContinuity
