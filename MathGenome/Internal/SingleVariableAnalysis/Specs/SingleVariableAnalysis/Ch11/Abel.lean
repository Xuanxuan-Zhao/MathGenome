import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
Independent specification of Abel's test, K03.11.abel (paper.tex:1073–1081).
The series predicates mean ordinary convergence of inclusive partial sums
indexed from zero, with finite real or complex limits. The real multiplier
may be nondecreasing or nonincreasing, and its absolute values are bounded.
No sign, nonvanishing, or absolute convergence assumption is imposed.
-/
namespace Specs.SingleVariableAnalysis.Ch11.Abel

open PartialSums

def realAbel : Prop :=
  ∀ (a b : ℕ → ℝ), realSeriesConvergesValue a →
    (Monotone b ∨ Antitone b) → (∃ M : ℝ, ∀ n, |b n| ≤ M) →
    realSeriesConvergesValue (fun n => a n * b n)

def complexAbel : Prop :=
  ∀ (a : ℕ → ℂ) (b : ℕ → ℝ), complexSeriesConvergesValue a →
    (Monotone b ∨ Antitone b) → (∃ M : ℝ, ∀ n, |b n| ≤ M) →
    complexSeriesConvergesValue (fun n => a n * (b n : ℂ))

end Specs.SingleVariableAnalysis.Ch11.Abel
