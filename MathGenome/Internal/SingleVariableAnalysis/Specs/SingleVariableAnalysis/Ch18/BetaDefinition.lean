import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers

/-! K03.18.beta_definition, paper.tex:3990–4008.
The value is selected from the independent improper Darboux limits, with a
harmless total extension outside the convergence domain. The theorems below
must prove existence on the entire positive parameter domain. No value of the
integrand at a singular endpoint enters any proper truncation. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.BetaDefinition
open Ch10.SeveralEndpoints

abbrev integrandType := ℝ → ℝ → ℝ → ℝ
def integrandValue : integrandType := fun p q t =>
  Ch07.RealPowers.realPowerValue t (p - 1) *
    Ch07.RealPowers.realPowerValue (1 - t) (q - 1)

abbrev betaType := ℝ → ℝ → ℝ
def betaValue : betaType := by
  classical
  exact fun p q => if h : convergesValue .real (integrandValue p q) (0 : WithBot ℝ) (1 : WithTop ℝ)
  then integralValue .real (integrandValue p q) 0 1 h else 0

def integrandPositive : Prop := ∀ p q t : ℝ, 0 < t → t < 1 →
  0 < integrandValue p q t

def localIntegrability : Prop := ∀ p q : ℝ,
  locallyIntegrableValue .real (integrandValue p q) 0 1

def betaHasIntegral : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  hasIntegralValue .real (integrandValue p q) 0 1 (betaValue p q)

/-- Every split gives the same sum of separately finite endpoint limits. -/
def betaIndependentEndpoints : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  ∀ c : regularPointValue (0 : WithBot ℝ) (1 : WithTop ℝ),
    hasIntegralAtSplitValue .real (integrandValue p q) 0 1 c (betaValue p q)

def betaAbsoluteConvergence : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  hasIntegralValue .real (fun t => ‖integrandValue p q t‖) 0 1 (betaValue p q)

def betaPositive : Prop := ∀ p q : ℝ, 0 < p → 0 < q → 0 < betaValue p q

def betaSymmetry : Prop := ∀ p q : ℝ, 0 < p → 0 < q → betaValue p q = betaValue q p

end Specs.SingleVariableAnalysis.Ch18.BetaDefinition
