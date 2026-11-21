import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.UnboundedDerivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Primitive

/-!
Independent specification of K03.09.derivative_not_integrable (paper.tex:2737–2750)
and its general compact-interval conclusion in K03.04.unbounded_derivative
(paper.tex:776–785). The function is exactly the upstream example, extended to
all real arguments. The primitive is continuous at included endpoints, and
proper integrability means the bounded Darboux predicate, not a measure integral.
The general nonintegrability conclusion requires precisely a < 0 < b.
-/
namespace Specs.SingleVariableAnalysis.Ch09.DerivativeNotIntegrable

open Set
open Ch04.UnboundedDerivative Ch08.DarbouxSums Ch08.Integral Ch09.Primitive

/-- Differentiability everywhere supplies the primitive condition; continuity
at any included endpoints is retained as well. -/
def continuousPrimitiveOn : Prop := ∀ I : Set ℝ,
  continuousPrimitiveOnValue functionValue (deriv functionValue) I

/-- On every compact interval with zero in its interior the derivative is unbounded. -/
def notBoundedOnInterval : Prop := ∀ a b : ℝ, a < 0 → 0 < b →
  ¬ boundedOnIntervalValue (deriv functionValue) a b

/-- The full interval conclusion, using the manuscript's proper Riemann predicate. -/
def notIntegrableOnInterval : Prop := ∀ a b : ℝ, a < 0 → 0 < b →
  ¬ realIntegrableValue (deriv functionValue) a b

/-- The stated example on [-1,1]: a primitive of an everywhere defined
actual derivative, whose derivative is unbounded and not properly integrable. -/
def exampleOnUnitInterval : Prop :=
  continuousPrimitiveOnValue functionValue (deriv functionValue) (Icc (-1) 1) ∧
  ¬ boundedOnIntervalValue (deriv functionValue) (-1) 1 ∧
  ¬ realIntegrableValue (deriv functionValue) (-1) 1

end Specs.SingleVariableAnalysis.Ch09.DerivativeNotIntegrable
