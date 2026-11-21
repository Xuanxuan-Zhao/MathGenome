import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.WatsonTail
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaDefinition

/-! K03.17.watson, paper.tex:4597–4636.  The value in the expansion is
specified by two independent endpoint limits of proper Darboux integrals.
The bound is uniform for all sufficiently large positive real λ. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.Watson
open _root_.SingleVariableAnalysis
open Ch10.OneEndpoint Ch10.SeveralEndpoints Ch17.WatsonTail
open scoped BigOperators

def expansion : Prop :=
  ∀ (k : ScalarKind) (N : ℕ) (α : ℝ) (a : Fin N → Scalar k) (q : ℝ → Scalar k),
    ∀ (_hN : 1 ≤ N) (hα : 0 < α), locallyIntegrableValue k q (0 : WithBot ℝ) ⊤ →
    localExpansion k N α a q → exponentialGrowth k q →
    ∃ L : ℝ, 0 < L ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ lam : ℝ, L ≤ lam →
      ∃ I : Scalar k,
        Ch10.Absolute.absoluteValue k (damped k q lam) (0 : WithBot ℝ) ⊤ ∧
        hasIntegralValue k (damped k q lam) (0 : WithBot ℝ) ⊤ I ∧
        ‖I - ∑ j : Fin N,
          (Ch18.GammaDefinition.gammaIntegralValue (α + (j : ℕ)) (by positivity) /
            lam ^ (α + (j : ℕ))) • a j‖ ≤ B * lam ^ (-α - (N : ℝ))

end Specs.SingleVariableAnalysis.Ch17.Watson
