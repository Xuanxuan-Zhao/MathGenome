import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.CompactInterval
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.MetricCompactness
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Bolzano
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compact scalar sets and closed real intervals

Scalar part of K03.03.compact_interval (paper.tex:529–540).
For the reverse implications, bounded scalar sequences have convergent
subsequences by the upstream Bolzano–Weierstrass theorems. Closedness keeps
their limits in the set. The metric compactness/sequential compactness
equivalence then gives compactness. For the forward implications, compact
sets in the usual scalar metric are closed and metrically bounded; the
norm characterization gives the displayed finite uniform bound.

The interval result reuses Mathlib's order-compactness theorem, also used
upstream in the real Bolzano proof. No boundedness/compactness equivalence
for arbitrary metric spaces is asserted.
-/
namespace SingleVariableAnalysis

/-- A finite real limit of a sequence in a closed set belongs to that set. -/
theorem real_closed_set_sequence_limit (s : Set ℝ) (hs : IsClosed s)
    (a : ℕ → ℝ) (L : ℝ) (ha : ∀ n, a n ∈ s)
    (hL : RealSequenceConverges a L) : L ∈ s :=
  hs.mem_of_tendsto ((realSequenceConverges_iff a L).mp hL)
    (Filter.Eventually.of_forall ha)

/-- The same closed-set limit property holds for the canonical complex modulus. -/
theorem complex_closed_set_sequence_limit (s : Set ℂ) (hs : IsClosed s)
    (a : ℕ → ℂ) (L : ℂ) (ha : ∀ n, a n ∈ s)
    (hL : ComplexSequenceConverges a L) : L ∈ s :=
  hs.mem_of_tendsto ((complexSequenceConverges_iff a L).mp hL)
    (Filter.Eventually.of_forall ha)

/-- Heine–Borel for every real subset, including the empty set. -/
theorem real_compact_iff_closed_bounded (s : Set ℝ) :
    IsCompact s ↔ IsClosed s ∧ ∃ M : ℝ, ∀ x ∈ s, |x| ≤ M := by
  constructor
  · intro hs
    refine ⟨hs.isClosed, ?_⟩
    simpa only [Real.norm_eq_abs] using
      (isBounded_iff_forall_norm_le.mp hs.isBounded)
  · rintro ⟨hs, M, hM⟩
    apply isCompact_iff_isSeqCompact.mpr
    intro a ha
    obtain ⟨L, φ, hφ, hL⟩ := real_bolzano_weierstrass a
      ⟨M, fun n => hM (a n) (ha n)⟩
    exact ⟨L, real_closed_set_sequence_limit s hs (a ∘ φ) L
      (fun n => ha (φ n)) hL, φ, hφ,
      (realSequenceConverges_iff (a ∘ φ) L).mp hL⟩

/-- Heine–Borel for every complex subset, with no order on complex scalars. -/
theorem complex_compact_iff_closed_bounded (s : Set ℂ) :
    IsCompact s ↔ IsClosed s ∧ ∃ M : ℝ, ∀ z ∈ s, ‖z‖ ≤ M := by
  constructor
  · intro hs
    exact ⟨hs.isClosed, isBounded_iff_forall_norm_le.mp hs.isBounded⟩
  · rintro ⟨hs, M, hM⟩
    apply isCompact_iff_isSeqCompact.mpr
    intro a ha
    obtain ⟨L, φ, hφ, hL⟩ := complex_bolzano_weierstrass a
      ⟨M, fun n => hM (a n) (ha n)⟩
    exact ⟨L, complex_closed_set_sequence_limit s hs (a ∘ φ) L
      (fun n => ha (φ n)) hL, φ, hφ,
      (complexSequenceConverges_iff (a ∘ φ) L).mp hL⟩

/-- No endpoint ordering is necessary: a reversed closed interval is empty. -/
theorem real_closed_interval_compact (a b : ℝ) : IsCompact (Set.Icc a b) :=
  isCompact_Icc

theorem real_empty_compact : IsCompact (∅ : Set ℝ) := isCompact_empty

theorem complex_empty_compact : IsCompact (∅ : Set ℂ) := isCompact_empty

end SingleVariableAnalysis
