import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-! Independent statements of K03.01.stolz (paper.tex:321–334).
Lean index `n` represents manuscript index `n + 1`, as in SequenceLimit.
The denominator is real in both scalar choices; complex division uses its
canonical embedding. Only finite scalar limits are asserted. -/

namespace Specs.SingleVariableAnalysis.Ch01.Stolz

open SequenceLimit

def denominatorEventuallyPositive : Prop :=
  ∀ b : ℕ → ℝ, divergesToPosInfinityValue b →
    sequenceEventuallyValue (fun n => 0 < b n)

def realStolz : Prop :=
  ∀ (a b : ℕ → ℝ) (L : ℝ), StrictMono b →
    divergesToPosInfinityValue b →
    realSequenceConvergesValue (fun n => (a (n + 1) - a n) / (b (n + 1) - b n)) L →
    realSequenceConvergesValue (fun n => a n / b n) L

def complexStolz : Prop :=
  ∀ (a : ℕ → ℂ) (b : ℕ → ℝ) (L : ℂ), StrictMono b →
    divergesToPosInfinityValue b →
    complexSequenceConvergesValue
      (fun n => (a (n + 1) - a n) / ((b (n + 1) - b n : ℝ) : ℂ)) L →
    complexSequenceConvergesValue (fun n => a n / (b n : ℂ)) L

end Specs.SingleVariableAnalysis.Ch01.Stolz
