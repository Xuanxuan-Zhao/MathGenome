import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.CompactEquivalences
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.CauchyBasics
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.TotalBoundedSequences
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import Mathlib.Topology.Sequences

/-! The three compactness conditions of paper.tex, d10:09:compact-equivalences.

The open-cover and epsilon convergence bridges identify the first equivalence
with compactness versus sequential compactness in a metric topology. The second
equivalence uses the upstream Cauchy-subsequence characterization of total
boundedness and the Cauchy sequence with convergent subsequence principle.
All statements permit the empty metric space. -/

open Set Filter
open scoped Topology
universe u

namespace D10Topology.Ch09

abbrev SequentiallyCompact {X : Type u} (d : PseudoMetricSpace X) : Prop :=
  Specs.D10Topology.Ch09.CompactEquivalences.SequentiallyCompact d

theorem coverCompact_iff_sequentiallyCompact {X : Type u} (d : MetricSpace X) :
    @Ch05.CoverCompact X (metricTopology d.toPseudoMetricSpace) ↔
      SequentiallyCompact d.toPseudoMetricSpace := by
  let := d
  constructor
  · intro hc s
    have hk : IsCompact (univ : Set X) :=
      (Ch05.coverCompact_iff_isCompact_univ X).mp hc
    obtain ⟨x, _, φ, hφ, hx⟩ := hk.isSeqCompact (fun n => mem_univ (s n))
    exact ⟨φ, hφ, x, (sequenceConverges_iff_mathlib _ _ _).mpr hx⟩
  · intro hs
    have hk : IsSeqCompact (univ : Set X) := by
      intro s _
      obtain ⟨φ, hφ, x, hx⟩ := hs s
      exact ⟨x, mem_univ x, φ, hφ, (sequenceConverges_iff_mathlib _ _ _).mp hx⟩
    exact (Ch05.coverCompact_iff_isCompact_univ X).mpr hk.isCompact

theorem sequentiallyCompact_iff_complete_totallyBounded {X : Type u} (d : MetricSpace X) :
    SequentiallyCompact d.toPseudoMetricSpace ↔
      SequentiallyComplete d.toPseudoMetricSpace ∧ TotallyBounded d.toPseudoMetricSpace := by
  let := d
  constructor
  · intro hs
    constructor
    · intro s hc
      obtain ⟨φ, hφ, x, hx⟩ := hs s
      exact ⟨x, cauchy_convergent_subsequence d s x φ hc hφ hx⟩
    · apply totallyBounded_iff_cauchy_subsequence.mpr
      intro s
      obtain ⟨φ, hφ, x, hx⟩ := hs s
      exact ⟨φ, hφ, convergent_cauchy d (s ∘ φ) x hx⟩
  · rintro ⟨hc, ht⟩ s
    obtain ⟨φ, hφ, hCauchy⟩ := totallyBounded_iff_cauchy_subsequence.mp ht s
    obtain ⟨x, hx⟩ := hc (s ∘ φ) hCauchy
    exact ⟨φ, hφ, x, hx⟩

theorem coverCompact_iff_complete_totallyBounded {X : Type u} (d : MetricSpace X) :
    @Ch05.CoverCompact X (metricTopology d.toPseudoMetricSpace) ↔
      SequentiallyComplete d.toPseudoMetricSpace ∧ TotallyBounded d.toPseudoMetricSpace :=
  (coverCompact_iff_sequentiallyCompact d).trans
    (sequentiallyCompact_iff_complete_totallyBounded d)

end D10Topology.Ch09
