import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-!
Independent specification of `K03.01.squeeze` (paper.tex:236–244).
Sequences use the upstream shift: Lean index `n` denotes source index `n + 1`.
The second assertion applies to each of the two permitted scalar types, real
and complex. Its real majorant need only dominate the error eventually; no
global sign condition on the majorant is imposed.
-/

namespace Specs.SingleVariableAnalysis.Ch01.Squeeze

open SequenceLimit

/-- Real sequences between two eventually ordered sequences with the same limit. -/
def realSequenceSqueeze : Prop :=
  ∀ (a b c : ℕ → ℝ) (L : ℝ),
    sequenceEventuallyValue (fun n => a n ≤ b n ∧ b n ≤ c n) →
    realSequenceConvergesValue a L →
    realSequenceConvergesValue c L →
    realSequenceConvergesValue b L

/-- The scalar absolute estimate for the real scalar choice. -/
def realSequenceAbsoluteEstimate : Prop :=
  ∀ (z : ℕ → ℝ) (L : ℝ) (d : ℕ → ℝ),
    sequenceEventuallyValue (fun n => |z n - L| ≤ d n) →
    realSequenceConvergesValue d 0 →
    realSequenceConvergesValue z L

/-- The scalar absolute estimate for the complex scalar choice. -/
def complexSequenceAbsoluteEstimate : Prop :=
  ∀ (z : ℕ → ℂ) (L : ℂ) (d : ℕ → ℝ),
    sequenceEventuallyValue (fun n => ‖z n - L‖ ≤ d n) →
    realSequenceConvergesValue d 0 →
    complexSequenceConvergesValue z L

end Specs.SingleVariableAnalysis.Ch01.Squeeze
