import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Monotone

/-!
Independent specification of K03.01.e_sequence (paper.tex:341–354), up to the
finite positive limit. The identification with exp(1) is a downstream goal.
Lean index n represents the manuscript's positive index n+1.
-/
namespace Specs.SingleVariableAnalysis.Ch01.ESequence

def eSequenceType : Type := ℕ → ℝ

noncomputable def eSequenceValue : eSequenceType :=
  fun n => (1 + 1 / (n + 1 : ℝ)) ^ (n + 1)

def eSequenceStrictMono : Prop := StrictMono eSequenceValue

def eSequenceLowerBound : Prop := ∀ n : ℕ, 2 ≤ eSequenceValue n

def eSequenceUpperBound : Prop := ∀ n : ℕ, eSequenceValue n < 3

def eSequenceLimitType : Type := ℝ

noncomputable def eSequenceLimitValue : ℝ :=
  sSup (Set.range eSequenceValue)

def eSequenceConverges : Prop :=
  SequenceLimit.realSequenceConvergesValue eSequenceValue eSequenceLimitValue

/-- A real number, hence finite, with an explicit positive lower bound. -/
def eSequenceLimitBounds : Prop :=
  2 ≤ eSequenceLimitValue ∧ eSequenceLimitValue ≤ 3

def eSequenceFinitePositiveLimit : Prop :=
  ∃ L : ℝ, 0 < L ∧ SequenceLimit.realSequenceConvergesValue eSequenceValue L

end Specs.SingleVariableAnalysis.Ch01.ESequence
