import MathGenome.Internal.MultivariableAnalysis.D04.C01.BoundedSubsequence
import MathGenome.Internal.MultivariableAnalysis.D04.C01.TopologicalTests
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.Compactness
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Sequences

/-! Finite-dimensional compactness, including the empty set and dimension zero.
The finite-dimensional step uses the upstream coordinatewise subsequence
extraction and the closed-set sequence test. The topological step uses the
general equivalence of compactness and sequential compactness in metrizable
spaces; no finite-dimensional closed-bounded compactness theorem is used. -/

open Set Filter Topology
namespace D04

theorem compact_iff_sequentiallyCompact {n : ℕ} (K : Set (E n)) :
    Compact K ↔ SequentiallyCompact K := by
  rw [compact_iff_isCompact, sequentiallyCompact_iff_isSeqCompact]
  exact isCompact_iff_isSeqCompact

private theorem sequentiallyCompact_of_closed_bounded {n : ℕ} (K : Set (E n))
    (hc : Closed K) (hb : ∃ B : ℝ, ∀ x ∈ K, ‖x‖ ≤ B) :
    SequentiallyCompact K := by
  intro x hx
  obtain ⟨B, hB⟩ := hb
  obtain ⟨s, a, hs, ha⟩ := bounded_subsequence x ⟨B, fun k => hB (x k) (hx k)⟩
  have hmem : a ∈ K :=
    (closed_iff_seq_limits K).mp hc (x ∘ s) a (fun k => hx (s k)) ha
  exact ⟨a, hmem, s, hs, ha⟩

theorem compact_iff_closed_bounded {n : ℕ} (K : Set (E n)) :
    Compact K ↔ Closed K ∧ ∃ B : ℝ, ∀ x ∈ K, ‖x‖ ≤ B := by
  constructor
  · intro h
    have hc := (compact_iff_isCompact K).mp h
    exact ⟨(closed_iff_isClosed K).mpr hc.isClosed, hc.isBounded.exists_norm_le⟩
  · rintro ⟨hc, hb⟩
    exact (compact_iff_sequentiallyCompact K).mpr
      (sequentiallyCompact_of_closed_bounded K hc hb)

theorem sequentiallyCompact_iff_closed_bounded {n : ℕ} (K : Set (E n)) :
    SequentiallyCompact K ↔ Closed K ∧ ∃ B : ℝ, ∀ x ∈ K, ‖x‖ ≤ B := by
  rw [← compact_iff_sequentiallyCompact K, compact_iff_closed_bounded K]

theorem compact_empty {n : ℕ} : Compact (∅ : Set (E n)) := by
  exact (compact_iff_isCompact _).mpr isCompact_empty

theorem compact_dimension_zero (K : Set (E 0)) : Compact K := by
  apply (compact_iff_isCompact K).mpr
  apply Set.Subsingleton.isCompact
  intro x _hx y _hy
  exact (vector_dimension_zero x).trans (vector_dimension_zero y).symm

end D04
