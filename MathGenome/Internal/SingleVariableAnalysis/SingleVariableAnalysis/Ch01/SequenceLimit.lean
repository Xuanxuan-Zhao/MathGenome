import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Scalar
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-!
# Sequence limits and eventual assertions

This implements `K03.01.sequence_limit`. A sequence `a : ℕ → ℝ` or
`a : ℕ → ℂ` uses shifted indexing: `a n` denotes the manuscript's
positive-indexed term `a_{n+1}`. Consequently `n ≥ N` represents precisely
the manuscript's tail starting at term `N + 1`; no term is discarded.

The explicit epsilon and threshold definitions are identified with the
canonical metric and order filters. Infinite divergence is a separate
predicate, and is incompatible with a finite real limit.
-/

namespace SingleVariableAnalysis

open scoped Topology

/-- An assertion holds on an entire tail of the shifted sequence. -/
def SequenceEventually (P : ℕ → Prop) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, P n

/-- A finite real limit, with real absolute value in the epsilon condition. -/
def RealSequenceConverges (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → SequenceEventually (fun n => |a n - L| < ε)

/-- A finite complex limit, with the canonical complex modulus. -/
def ComplexSequenceConverges (a : ℕ → ℂ) (L : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → SequenceEventually (fun n => ‖a n - L‖ < ε)

/-- Real divergence to positive infinity uses every real threshold. -/
def DivergesToPosInfinity (a : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, SequenceEventually (fun n => B < a n)

/-- Real divergence to negative infinity uses every real threshold. -/
def DivergesToNegInfinity (a : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, SequenceEventually (fun n => a n < B)

theorem sequenceEventually_iff (P : ℕ → Prop) :
    SequenceEventually P ↔ Filter.Eventually P Filter.atTop :=
  Filter.eventually_atTop.symm

theorem realSequenceConverges_iff (a : ℕ → ℝ) (L : ℝ) :
    RealSequenceConverges a L ↔ Filter.Tendsto a Filter.atTop (𝓝 L) := by
  simpa only [RealSequenceConverges, SequenceEventually, Real.dist_eq] using
    (Metric.tendsto_atTop (u := a) (a := L)).symm

theorem complexSequenceConverges_iff (a : ℕ → ℂ) (L : ℂ) :
    ComplexSequenceConverges a L ↔ Filter.Tendsto a Filter.atTop (𝓝 L) := by
  simpa only [ComplexSequenceConverges, SequenceEventually, dist_eq_norm] using
    (Metric.tendsto_atTop (u := a) (a := L)).symm

theorem divergesToPosInfinity_iff (a : ℕ → ℝ) :
    DivergesToPosInfinity a ↔ Filter.Tendsto a Filter.atTop Filter.atTop := by
  constructor
  · intro h
    exact Filter.tendsto_atTop.mpr fun B =>
      ((sequenceEventually_iff _).mp (h B)).mono fun _ hn => hn.le
  · intro h B
    exact (sequenceEventually_iff _).mpr (h.eventually_gt_atTop B)

theorem divergesToNegInfinity_iff (a : ℕ → ℝ) :
    DivergesToNegInfinity a ↔ Filter.Tendsto a Filter.atTop Filter.atBot := by
  constructor
  · intro h
    exact Filter.tendsto_atBot.mpr fun B =>
      ((sequenceEventually_iff _).mp (h B)).mono fun _ hn => hn.le
  · intro h B
    exact (sequenceEventually_iff _).mpr (h.eventually_lt_atBot B)

theorem posInfinity_not_finite (a : ℕ → ℝ) (h : DivergesToPosInfinity a)
    (L : ℝ) : ¬ RealSequenceConverges a L := by
  intro hc
  obtain ⟨N, hN⟩ := h (L + 1)
  obtain ⟨M, hM⟩ := hc 1 zero_lt_one
  have hu := (abs_lt.mp (hM (max N M) (le_max_right _ _))).2
  have hv : a (max N M) < L + 1 := by
    simpa only [add_comm] using (sub_lt_iff_lt_add.mp hu)
  exact (not_lt_of_gt (hN (max N M) (le_max_left _ _))) hv

theorem negInfinity_not_finite (a : ℕ → ℝ) (h : DivergesToNegInfinity a)
    (L : ℝ) : ¬ RealSequenceConverges a L := by
  intro hc
  obtain ⟨N, hN⟩ := h (L - 1)
  obtain ⟨M, hM⟩ := hc 1 zero_lt_one
  have hu := (abs_lt.mp (hM (max N M) (le_max_right _ _))).1
  have hv : L - 1 < a (max N M) := by
    simpa only [sub_eq_add_neg, add_comm] using (lt_sub_iff_add_lt.mp hu)
  exact (not_lt_of_gt (hN (max N M) (le_max_left _ _))) hv

theorem infinity_directions_exclusive (a : ℕ → ℝ) (h : DivergesToPosInfinity a) :
    ¬ DivergesToNegInfinity a := by
  intro hn
  obtain ⟨N, hN⟩ := h 0
  obtain ⟨M, hM⟩ := hn 0
  exact (not_lt_of_gt (hN (max N M) (le_max_left _ _)))
    (hM (max N M) (le_max_right _ _))

end SingleVariableAnalysis
