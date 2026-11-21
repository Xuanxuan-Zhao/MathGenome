import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
Independent specification of K03.11.comparison (paper.tex:1003–1011).
All series use the upstream ordinary, inclusive partial-sum predicates.
The hypotheses hold only eventually, so initial terms may be negative or
zero. The comparison constant is any real number. Finite ratio limits and
divergence of the ratio to +∞ are kept distinct.

In the counterexamples, Lean index n represents the positive index n+1:
the terms are exactly 1/(n+1)² and 1/(n+1), with no division by zero.
-/

namespace Specs.SingleVariableAnalysis.Ch11.Comparison

open PartialSums
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit

def seriesComparison : Prop :=
  ∀ (a b : ℕ → ℝ) (C : ℝ),
    sequenceEventuallyValue (fun n => 0 ≤ a n) →
    sequenceEventuallyValue (fun n => 0 ≤ b n) →
    sequenceEventuallyValue (fun n => a n ≤ C * b n) →
    realSeriesConvergesValue b → realSeriesConvergesValue a

def seriesComparisonDivergence : Prop :=
  ∀ (a b : ℕ → ℝ) (C : ℝ),
    sequenceEventuallyValue (fun n => 0 ≤ a n) →
    sequenceEventuallyValue (fun n => 0 ≤ b n) →
    sequenceEventuallyValue (fun n => a n ≤ C * b n) →
    realSeriesDivergesValue a → realSeriesDivergesValue b

def limitComparisonPositive : Prop :=
  ∀ (a b : ℕ → ℝ) (L : ℝ),
    sequenceEventuallyValue (fun n => 0 ≤ a n) →
    sequenceEventuallyValue (fun n => 0 < b n) → 0 < L →
    realSequenceConvergesValue (fun n => a n / b n) L →
    (realSeriesConvergesValue a ↔ realSeriesConvergesValue b)

def limitComparisonZero : Prop :=
  ∀ (a b : ℕ → ℝ),
    sequenceEventuallyValue (fun n => 0 ≤ a n) →
    sequenceEventuallyValue (fun n => 0 < b n) →
    realSequenceConvergesValue (fun n => a n / b n) 0 →
    realSeriesConvergesValue b → realSeriesConvergesValue a

def limitComparisonInfinity : Prop :=
  ∀ (a b : ℕ → ℝ),
    sequenceEventuallyValue (fun n => 0 ≤ a n) →
    sequenceEventuallyValue (fun n => 0 < b n) →
    divergesToPosInfinityValue (fun n => a n / b n) →
    realSeriesConvergesValue a → realSeriesConvergesValue b

def zeroLimitCounterexample : Prop :=
  (∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1)^2 ∧ 0 < 1 / ((n : ℝ) + 1)) ∧
    realSequenceConvergesValue
      (fun n => (1 / ((n : ℝ) + 1)^2) / (1 / ((n : ℝ) + 1))) 0 ∧
    realSeriesConvergesValue (fun n => 1 / ((n : ℝ) + 1)^2) ∧
    realSeriesDivergesValue (fun n => 1 / ((n : ℝ) + 1))

def infiniteLimitCounterexample : Prop :=
  (∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) ∧ 0 < 1 / ((n : ℝ) + 1)^2) ∧
    divergesToPosInfinityValue
      (fun n => (1 / ((n : ℝ) + 1)) / (1 / ((n : ℝ) + 1)^2)) ∧
    realSeriesDivergesValue (fun n => 1 / ((n : ℝ) + 1)) ∧
    realSeriesConvergesValue (fun n => 1 / ((n : ℝ) + 1)^2)

end Specs.SingleVariableAnalysis.Ch11.Comparison
