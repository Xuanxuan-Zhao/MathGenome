import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness

/-! Independent statements for paper.tex, d10:09:compact-equivalences.
Compactness is the open-cover property for the displayed metric topology.
Subsequence indices are strictly increasing, and no nonemptiness hypothesis
is imposed. Completeness and total boundedness use that same metric. -/

universe u

namespace Specs.D10Topology.Ch09.CompactEquivalences
open Specs.D10Topology.Ch09.MetricConventions
open Specs.D10Topology.Ch05.Compactness

def sequentiallyCompactType := {X : Type u} → PseudoMetricSpace X → Prop

/-- Every sequence admits a convergent subsequence in the space itself. -/
def SequentiallyCompact : sequentiallyCompactType := fun d =>
  ∀ s : ℕ → _, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ x, SequenceConverges d (s ∘ φ) x

def sequentiallyCompactValue : sequentiallyCompactType := @SequentiallyCompact

def coverCompact_iff_sequentiallyCompact : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    @CoverCompact X (metricTopology d.toPseudoMetricSpace) ↔
      SequentiallyCompact d.toPseudoMetricSpace

def sequentiallyCompact_iff_complete_totallyBounded : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    SequentiallyCompact d.toPseudoMetricSpace ↔
      SequentiallyComplete d.toPseudoMetricSpace ∧ TotallyBounded d.toPseudoMetricSpace

def coverCompact_iff_complete_totallyBounded : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    @CoverCompact X (metricTopology d.toPseudoMetricSpace) ↔
      SequentiallyComplete d.toPseudoMetricSpace ∧ TotallyBounded d.toPseudoMetricSpace

end Specs.D10Topology.Ch09.CompactEquivalences
