import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.ESequence

/-!
Independent specification of the sequence assertion in
K03.07.construction_bridges (paper.tex:1868–1883) and the postponed
identification in K03.01.e_sequence (paper.tex:341–354).
Lean index n denotes the manuscript's positive integer n+1, as in the
shared Chapter 1 sequence interface. Powers in the sequence are natural
integer powers, even when an early base is nonpositive. Only an eventual
positive-base tail is used to compare them with real powers.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.SequenceComparison
open Filter
open scoped Topology

def eventuallyPositiveBases : Prop :=
  ∀ x : ℝ, ∀ᶠ n : ℕ in atTop, 0 < 1 + x / (n + 1 : ℝ)

def sequenceLimit : Prop :=
  ∀ x : ℝ, Ch01.SequenceLimit.realSequenceConvergesValue
    (fun n : ℕ => (1 + x / (n + 1 : ℝ)) ^ (n + 1))
    (ExpConstruction.realSeriesExpValue x)

def zeroTerms : Prop :=
  ∀ n : ℕ, (1 + (0 : ℝ) / (n + 1 : ℝ)) ^ (n + 1) = 1

def classicalLimit : Prop :=
  Ch01.ESequence.eSequenceLimitValue = ExpConstruction.realSeriesExpValue 1

def classicalLimitCanonical : Prop :=
  Ch01.ESequence.eSequenceLimitValue = Real.exp 1

end Specs.SingleVariableAnalysis.Ch07.SequenceComparison
