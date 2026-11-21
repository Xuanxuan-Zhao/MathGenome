import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-!
Independent specification of `K03.01.cauchy` (paper.tex:279–286).
Lean index `n` represents the paper's positive index `n + 1`, as in the
shared sequence interface. Both indices in the Cauchy condition lie on
one common tail. The existential limit is a finite scalar in the same
canonical field; complex completeness is a conclusion, not a hypothesis.
The rational counterexample is allocated separately to RationalIncomplete.
-/

namespace Specs.SingleVariableAnalysis.Ch01.Cauchy

def realCauchyCriterion : Prop :=
  ∀ a : ℕ → ℝ,
    (∃ L : ℝ, SequenceLimit.realSequenceConvergesValue a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |a n - a m| < ε

def complexCauchyCriterion : Prop :=
  ∀ a : ℕ → ℂ,
    (∃ L : ℂ, SequenceLimit.complexSequenceConvergesValue a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖a n - a m‖ < ε

end Specs.SingleVariableAnalysis.Ch01.Cauchy
