import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness

/-! Independent statements of paper.tex, Theorem d10:09:lebesgue.
Compactness is the open-cover property for the displayed metric topology.
The diameter is extended-valued; lambda is a positive finite real number.
Neither the source space nor the cover is assumed nonempty. -/

open Set
open scoped Topology
universe u v

namespace Specs.D10Topology.Ch09.LebesgueUniformContinuity
open Specs.D10Topology.Ch09.MetricConventions
open Specs.D10Topology.Ch05.Compactness

/-- Every nonempty sufficiently small subset lies in a single cover member. -/
def lebesgue_number : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    @CoverCompact X (metricTopology d.toPseudoMetricSpace) →
    ∀ U : Set (Set X),
      (∀ V ∈ U, IsOpen[metricTopology d.toPseudoMetricSpace] V) →
      (univ : Set X) ⊆ ⋃₀ U →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ A : Set X, A.Nonempty →
        diameter d.toPseudoMetricSpace A < ENNReal.ofReal ε₀ →
        ∃ V ∈ U, A ⊆ V

/-- Heine--Cantor with an arbitrary metric target and no nonemptiness assumption. -/
def compact_continuous_uniformlyContinuous : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X) (e : MetricSpace Y),
    @CoverCompact X (metricTopology d.toPseudoMetricSpace) →
    ∀ f : X → Y,
      @Continuous X Y (metricTopology d.toPseudoMetricSpace)
        (metricTopology e.toPseudoMetricSpace) f →
      UniformlyContinuous d.toPseudoMetricSpace e.toPseudoMetricSpace f

end Specs.D10Topology.Ch09.LebesgueUniformContinuity
