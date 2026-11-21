import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit
import Mathlib.Topology.MetricSpace.Bounded

/-!
Independent specification of the scalar part of K03.03.compact_interval,
paper.tex:529–540. Compactness is the canonical finite-open-subcover notion
in the usual scalar topology. Boundedness is written explicitly as a finite
uniform bound on absolute values or moduli. No set is assumed nonempty.

The general metric-space equivalence is specified separately in
Ch03.MetricCompactness. Sequences use the shared shifted positive indexing:
Lean index n represents source index n+1.
-/
namespace Specs.SingleVariableAnalysis.Ch03.CompactInterval

open Specs.SingleVariableAnalysis.Ch01.SequenceLimit

def realCompactIffClosedBounded : Prop :=
  ∀ s : Set ℝ, IsCompact s ↔
    IsClosed s ∧ ∃ M : ℝ, ∀ x ∈ s, |x| ≤ M

def complexCompactIffClosedBounded : Prop :=
  ∀ s : Set ℂ, IsCompact s ↔
    IsClosed s ∧ ∃ M : ℝ, ∀ z ∈ s, ‖z‖ ≤ M

/-- This includes singleton intervals and the empty interval when b < a. -/
def realClosedIntervalCompact : Prop :=
  ∀ a b : ℝ, IsCompact (Set.Icc a b)

def realClosedSetSequenceLimit : Prop :=
  ∀ (s : Set ℝ), IsClosed s → ∀ (a : ℕ → ℝ) (L : ℝ),
    (∀ n, a n ∈ s) → realSequenceConvergesValue a L → L ∈ s

def complexClosedSetSequenceLimit : Prop :=
  ∀ (s : Set ℂ), IsClosed s → ∀ (a : ℕ → ℂ) (L : ℂ),
    (∀ n, a n ∈ s) → complexSequenceConvergesValue a L → L ∈ s

def realEmptyCompact : Prop := IsCompact (∅ : Set ℝ)

def complexEmptyCompact : Prop := IsCompact (∅ : Set ℂ)

end Specs.SingleVariableAnalysis.Ch03.CompactInterval
