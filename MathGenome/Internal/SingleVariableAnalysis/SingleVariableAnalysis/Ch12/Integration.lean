import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Integration
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.UniformStability

/-!
K03.12.integration: uniform limits and the proper Riemann integral.
The Chapter 08 stability theorem uses exactly the canonical Darboux
predicates, values and interval-restricted uniform convergence required here.
Its proof first bounds the limit using one approximant, applies the Darboux
gap estimate in the real case, and treats complex integrability componentwise.
The integral norm estimate gives the same sharp length factor for both scalars.
No continuity or measure-integrability assumptions are added.
-/
namespace SingleVariableAnalysis.Riemann

theorem real_uniform_integration :
    Specs.SingleVariableAnalysis.Ch12.Integration.realUniformIntegration := by
  exact real_uniform_stability

theorem complex_uniform_integration :
    Specs.SingleVariableAnalysis.Ch12.Integration.complexUniformIntegration := by
  exact complex_uniform_stability

theorem real_degenerate_integration :
    Specs.SingleVariableAnalysis.Ch12.Integration.realDegenerateIntegration := by
  intro f a
  exact ⟨realIntegrable_degenerate f a, realIntegral_degenerate f a⟩

theorem complex_degenerate_integration :
    Specs.SingleVariableAnalysis.Ch12.Integration.complexDegenerateIntegration := by
  intro f a
  exact ⟨integrable_degenerate .complex f a, integral_degenerate .complex f a⟩

end SingleVariableAnalysis.Riemann
