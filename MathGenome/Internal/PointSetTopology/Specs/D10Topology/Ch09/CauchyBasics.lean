import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions

/-!
Independent statements for Proposition d10:09:cauchy-basics in paper.tex.
Completeness and convergence always use the displayed metric. Subsets carry
its restriction, including the empty subset. Subsequence indices are strictly
increasing natural numbers, as in the manuscript.
-/
open scoped Topology
universe u v

namespace Specs.D10Topology.Ch09.CauchyBasics
open Specs.D10Topology.Ch09.MetricConventions

def convergent_cauchy : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (s : ℕ → X) (x : X),
    SequenceConverges d.toPseudoMetricSpace s x → CauchySequence d.toPseudoMetricSpace s

def cauchy_convergent_subsequence : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (s : ℕ → X) (x : X) (φ : ℕ → ℕ),
    CauchySequence d.toPseudoMetricSpace s → StrictMono φ →
    SequenceConverges d.toPseudoMetricSpace (s ∘ φ) x →
    SequenceConverges d.toPseudoMetricSpace s x

def uniformlyContinuous_cauchy : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X) (e : MetricSpace Y)
    (f : X → Y) (s : ℕ → X),
    UniformlyContinuous d.toPseudoMetricSpace e.toPseudoMetricSpace f →
    CauchySequence d.toPseudoMetricSpace s →
    CauchySequence e.toPseudoMetricSpace (f ∘ s)

def closed_subspace_complete : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X),
    SequentiallyComplete d.toPseudoMetricSpace →
    IsClosed[metricTopology d.toPseudoMetricSpace] A →
    SequentiallyComplete
      (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace

def complete_subspace_closed : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X),
    SequentiallyComplete
      (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace →
    IsClosed[metricTopology d.toPseudoMetricSpace] A

def uniformlyEquivalent_complete_iff : Prop :=
  ∀ {X : Type u} (d e : MetricSpace X),
    UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace →
    (SequentiallyComplete d.toPseudoMetricSpace ↔ SequentiallyComplete e.toPseudoMetricSpace)

end Specs.D10Topology.Ch09.CauchyBasics
