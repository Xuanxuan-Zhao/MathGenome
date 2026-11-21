import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.BetaDefinition
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! K03.18.beta_recurrence, paper.tex:4007–4031.
The Beta value here is the shared independently convergent improper Darboux
integral, not a value defined by a Gamma quotient. -/
namespace Specs.SingleVariableAnalysis.Ch18.BetaRecurrence
open scoped BigOperators
open BetaDefinition

def betaAddOneLeft : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  betaValue (p + 1) q = p * betaValue p q / (p + q)

def betaAddOneRight : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  betaValue p (q + 1) = q * betaValue p q / (p + q)

def betaOneRight : Prop := ∀ p : ℝ, 0 < p → betaValue p 1 = 1 / p

/-- The range includes both the initial factor s and the final factor s+n,
including n=0, when the numerator is 0! = 1. -/
def betaNatAddOneRight : Prop := ∀ s : ℝ, 0 < s → ∀ n : ℕ,
  betaValue s ((n : ℝ) + 1) =
    (n.factorial : ℝ) / ∏ j ∈ Finset.range (n + 1), (s + (j : ℝ))

end Specs.SingleVariableAnalysis.Ch18.BetaRecurrence
