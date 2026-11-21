import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Limsup

/-!
Independent specification of K03.11.ratio, paper.tex:1019–1027.
All series use ordinary inclusive partial sums; scalar limits are finite.
The extended-real tail limsup/liminf apply without boundedness assumptions.
The harmonic and reciprocal-square witnesses use positive indices n+1.
-/
namespace Specs.SingleVariableAnalysis.Ch11.Ratio

open Ch01.SequenceLimit Ch01.Limsup PartialSums Absolute

def realRatioTest : Prop :=
  ∀ a : ℕ → ℝ, sequenceEventuallyValue (fun n => a n ≠ 0) →
    sequenceLimsupValue (fun n => |a (n+1) / a n|) < 1 →
    realAbsolutelyConvergesValue a ∧ realSeriesConvergesValue a

def complexRatioTest : Prop :=
  ∀ a : ℕ → ℂ, sequenceEventuallyValue (fun n => a n ≠ 0) →
    sequenceLimsupValue (fun n => ‖a (n+1) / a n‖) < 1 →
    complexAbsolutelyConvergesValue a ∧ complexSeriesConvergesValue a

def realRatioDivergence : Prop :=
  ∀ a : ℕ → ℝ, sequenceEventuallyValue (fun n => a n ≠ 0) →
    sequenceEventuallyValue (fun n => 1 ≤ |a (n+1) / a n|) →
    realSeriesDivergesValue a

def complexRatioDivergence : Prop :=
  ∀ a : ℕ → ℂ, sequenceEventuallyValue (fun n => a n ≠ 0) →
    sequenceEventuallyValue (fun n => 1 ≤ ‖a (n+1) / a n‖) →
    complexSeriesDivergesValue a

def realLiminfRatioDivergence : Prop :=
  ∀ a : ℕ → ℝ, sequenceEventuallyValue (fun n => a n ≠ 0) →
    1 < sequenceLiminfValue (fun n => |a (n+1) / a n|) →
    realSeriesDivergesValue a

def complexLiminfRatioDivergence : Prop :=
  ∀ a : ℕ → ℂ, sequenceEventuallyValue (fun n => a n ≠ 0) →
    1 < sequenceLiminfValue (fun n => ‖a (n+1) / a n‖) →
    complexSeriesDivergesValue a

/-- Explicit nonzero witnesses with the same ratio limit and opposite verdicts. -/
def ratioLimitOneExamples : Prop :=
  (∀ n : ℕ, 1 / ((n : ℝ)+1) ≠ 0 ∧ 1 / ((n : ℝ)+1)^2 ≠ 0) ∧
  realSequenceConvergesValue
    (fun n : ℕ => |(1 / (((n+1 : ℕ) : ℝ)+1)) / (1 / ((n : ℝ)+1))|) 1 ∧
  realSequenceConvergesValue
    (fun n : ℕ => |(1 / (((n+1 : ℕ) : ℝ)+1)^2) / (1 / ((n : ℝ)+1)^2)|) 1 ∧
  realSeriesDivergesValue (fun n : ℕ => 1 / ((n : ℝ)+1)) ∧
  realAbsolutelyConvergesValue (fun n : ℕ => 1 / ((n : ℝ)+1)^2)

end Specs.SingleVariableAnalysis.Ch11.Ratio
