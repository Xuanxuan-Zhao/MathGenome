import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RegulatedApproximation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral

/-! Independent statements for the boundedness and proper Riemann-integrability
consequence of K03.15.regulated (paper.tex:3610–3625). The one-sided-limit
hypothesis is the shared `RegulatedOn`; it imposes no relation between a node's
assigned value and either limit, and no bounded-variation hypothesis. The proper
integrability predicates are the existing bounded Darboux predicates, with
complex integrability defined componentwise. Singleton intervals are included.
The uniform finite-step approximation assertions remain in the prerequisite
`RegulatedApproximation` specification. -/

namespace Specs.SingleVariableAnalysis.Ch15.Regulated
open _root_.SingleVariableAnalysis

def realRegulatedRiemann : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ f : ℝ → ℝ, RegulatedOn f a b →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc a b, |f x| ≤ M) ∧
    Ch08.Integral.realIntegrableValue f a b

def complexRegulatedRiemann : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ f : ℝ → ℂ, RegulatedOn f a b →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) ∧
    Ch08.Integral.complexIntegrableValue f a b

end Specs.SingleVariableAnalysis.Ch15.Regulated
