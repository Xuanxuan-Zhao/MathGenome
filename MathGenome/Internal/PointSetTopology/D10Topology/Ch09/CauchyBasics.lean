import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.CauchyBasics
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-! Proposition d10:09:cauchy-basics. The canonical epsilon definitions are
related to Mathlib by the previously proved MetricConventions bridges.
No ambient completeness is assumed when proving that a complete subset is
closed, and no nonemptiness hypothesis is used for either subspace theorem. -/

open Filter
open scoped Topology
universe u v

namespace D10Topology.Ch09

theorem convergent_cauchy {X : Type u} (d : MetricSpace X) (s : ℕ → X) (x : X)
    (h : SequenceConverges d.toPseudoMetricSpace s x) :
    CauchySequence d.toPseudoMetricSpace s := by
  let := d
  exact (cauchySequence_iff_mathlib _ _).mpr
    ((sequenceConverges_iff_mathlib _ _ _).mp h).cauchySeq

theorem cauchy_convergent_subsequence {X : Type u} (d : MetricSpace X)
    (s : ℕ → X) (x : X) (φ : ℕ → ℕ)
    (hs : CauchySequence d.toPseudoMetricSpace s) (hφ : StrictMono φ)
    (hx : SequenceConverges d.toPseudoMetricSpace (s ∘ φ) x) :
    SequenceConverges d.toPseudoMetricSpace s x := by
  let := d
  exact (sequenceConverges_iff_mathlib _ _ _).mpr
    (tendsto_nhds_of_cauchySeq_of_subseq ((cauchySequence_iff_mathlib _ _).mp hs)
      hφ.tendsto_atTop ((sequenceConverges_iff_mathlib _ _ _).mp hx))

theorem uniformlyContinuous_cauchy {X : Type u} {Y : Type v}
    (d : MetricSpace X) (e : MetricSpace Y) (f : X → Y) (s : ℕ → X)
    (hf : UniformlyContinuous d.toPseudoMetricSpace e.toPseudoMetricSpace f)
    (hs : CauchySequence d.toPseudoMetricSpace s) :
    CauchySequence e.toPseudoMetricSpace (f ∘ s) := by
  let := d
  let := e
  exact (cauchySequence_iff_mathlib _ _).mpr
    (((uniformlyContinuous_iff_mathlib _ _ _).mp hf).comp_cauchySeq
      ((cauchySequence_iff_mathlib _ _).mp hs))

theorem closed_subspace_complete {X : Type u} (d : MetricSpace X) (A : Set X)
    (hc : SequentiallyComplete d.toPseudoMetricSpace)
    (hA : IsClosed[metricTopology d.toPseudoMetricSpace] A) :
    SequentiallyComplete
      (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace := by
  let := d
  let := (sequentiallyComplete_iff_mathlib _).mp hc
  exact (sequentiallyComplete_iff_mathlib _).mpr hA.isComplete.completeSpace_coe

theorem complete_subspace_closed {X : Type u} (d : MetricSpace X) (A : Set X)
    (hc : SequentiallyComplete
      (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace) :
    IsClosed[metricTopology d.toPseudoMetricSpace] A := by
  let := d
  have hc' : CompleteSpace A := (sequentiallyComplete_iff_mathlib _).mp hc
  exact (completeSpace_coe_iff_isComplete.mp hc').isClosed

private theorem uniformlyContinuous_sequenceConverges {X : Type u} {Y : Type v}
    (d : MetricSpace X) (e : MetricSpace Y) (f : X → Y) (s : ℕ → X) (x : X)
    (hf : UniformlyContinuous d.toPseudoMetricSpace e.toPseudoMetricSpace f)
    (hs : SequenceConverges d.toPseudoMetricSpace s x) :
    SequenceConverges e.toPseudoMetricSpace (f ∘ s) (f x) := by
  let := d
  let := e
  exact (sequenceConverges_iff_mathlib _ _ _).mpr
    (((uniformlyContinuous_iff_mathlib _ _ _).mp hf).continuous.continuousAt.tendsto.comp
      ((sequenceConverges_iff_mathlib _ _ _).mp hs))

theorem uniformlyEquivalent_complete_iff {X : Type u} (d e : MetricSpace X)
    (h : UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace) :
    SequentiallyComplete d.toPseudoMetricSpace ↔ SequentiallyComplete e.toPseudoMetricSpace := by
  constructor
  · intro hc s hs
    obtain ⟨x, hx⟩ := hc s (uniformlyContinuous_cauchy e d id s h.2 hs)
    exact ⟨x, uniformlyContinuous_sequenceConverges d e id s x h.1 hx⟩
  · intro hc s hs
    obtain ⟨x, hx⟩ := hc s (uniformlyContinuous_cauchy d e id s h.1 hs)
    exact ⟨x, uniformlyContinuous_sequenceConverges e d id s x h.2 hx⟩

end D10Topology.Ch09
