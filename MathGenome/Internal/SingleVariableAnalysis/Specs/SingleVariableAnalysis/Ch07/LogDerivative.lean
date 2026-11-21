import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogConstruction

/-!
Independent specification for the derivative part of K03.07.log_derivative,
paper.tex:1610–1626. The function is the inverse of the shared factorial-series
exponential. Its ambient totalization is differentiated only at positive inputs,
which are interior points of its mathematical domain. The integral comparison
is a separate downstream obligation.
-/
namespace Specs.SingleVariableAnalysis.Ch07.LogDerivative

def derivative : Prop :=
  ∀ x : ℝ, 0 < x → HasDerivAt LogConstruction.seriesLogValue (1 / x) x

end Specs.SingleVariableAnalysis.Ch07.LogDerivative
