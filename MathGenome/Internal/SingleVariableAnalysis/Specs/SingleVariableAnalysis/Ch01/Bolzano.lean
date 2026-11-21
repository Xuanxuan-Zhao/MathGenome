import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Subsequence

/-!
Independent specification of `K03.01.bolzano` (paper.tex:271–278).

Boundedness means a finite uniform bound on the absolute values/moduli of all
terms. The limits are in the canonical real or complex field. As in the
upstream sequence interface, Lean index `n` denotes source index `n + 1`.
The strictly increasing selection map therefore represents precisely a
subsequence of the manuscript's positive-indexed sequence.
-/

namespace Specs.SingleVariableAnalysis.Ch01.Bolzano

/-- Every bounded real sequence has a subsequence with a finite real limit. -/
def realBolzanoWeierstrass : Prop :=
  ∀ a : ℕ → ℝ, (∃ M : ℝ, ∀ n, |a n| ≤ M) →
    ∃ L : ℝ, Subsequence.realSubsequentialLimitValue a L

/-- Every bounded complex sequence has a subsequence with a complex limit. -/
def complexBolzanoWeierstrass : Prop :=
  ∀ a : ℕ → ℂ, (∃ M : ℝ, ∀ n, ‖a n‖ ≤ M) →
    ∃ L : ℂ, Subsequence.complexSubsequentialLimitValue a L

end Specs.SingleVariableAnalysis.Ch01.Bolzano
