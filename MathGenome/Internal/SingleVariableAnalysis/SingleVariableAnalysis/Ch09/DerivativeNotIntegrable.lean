import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.DerivativeNotIntegrable
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.UnboundedDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Primitive

/-!
# A primitive whose derivative is not properly Riemann integrable

The upstream example is differentiable everywhere. Its derivative is unbounded
below on every sufficiently short interval to the right of zero. Any interval
[a,b] with a < 0 < b contains such an interval, whereas proper Darboux
integrability explicitly requires boundedness on the whole closed interval.
-/
namespace SingleVariableAnalysis

open Set

/-- The example is a continuous primitive of its actual derivative on any domain. -/
theorem unboundedDerivative_continuousPrimitiveOn (I : Set ℝ) :
    ContinuousPrimitiveOn unboundedDerivativeExample (deriv unboundedDerivativeExample) I := by
  exact ⟨unboundedDerivative_differentiable.continuous.continuousOn,
    fun x _ => (unboundedDerivative_differentiable x).hasDerivAt⟩

/-- Unboundedness near zero rules out boundedness on every interval containing
zero in its interior. Only the lower-bound component is needed. -/
theorem unboundedDerivative_not_boundedOnInterval (a b : ℝ) (ha : a < 0) (hb : 0 < b) :
    ¬ Riemann.BoundedOnInterval (deriv unboundedDerivativeExample) a b := by
  rintro ⟨⟨B, hB⟩, _⟩
  obtain ⟨x, hx, hxb, hd⟩ := unboundedDerivative_locally_unbounded_below b hb B
  have hmem : deriv unboundedDerivativeExample x ∈
      (deriv unboundedDerivativeExample) '' Icc a b :=
    ⟨x, ⟨(ha.trans hx).le, hxb.le⟩, rfl⟩
  exact (not_lt_of_ge (hB hmem)) hd

/-- This is proper Riemann nonintegrability, directly through the boundedness
requirement in the accepted Darboux interface. -/
theorem unboundedDerivative_not_riemannIntegrable (a b : ℝ) (ha : a < 0) (hb : 0 < b) :
    ¬ Riemann.RealIntegrable (deriv unboundedDerivativeExample) a b := by
  intro h
  exact unboundedDerivative_not_boundedOnInterval a b ha hb (Riemann.RealIntegrable.bounded h)

/-- K03.09.derivative_not_integrable on its stated interval [-1,1]. -/
theorem primitive_with_nonintegrable_derivative :
    ContinuousPrimitiveOn unboundedDerivativeExample (deriv unboundedDerivativeExample)
        (Icc (-1) 1) ∧
      ¬ Riemann.BoundedOnInterval (deriv unboundedDerivativeExample) (-1) 1 ∧
      ¬ Riemann.RealIntegrable (deriv unboundedDerivativeExample) (-1) 1 := by
  exact ⟨unboundedDerivative_continuousPrimitiveOn _,
    unboundedDerivative_not_boundedOnInterval (-1) 1 (by norm_num) (by norm_num),
    unboundedDerivative_not_riemannIntegrable (-1) 1 (by norm_num) (by norm_num)⟩

end SingleVariableAnalysis
