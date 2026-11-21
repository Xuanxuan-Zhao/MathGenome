import MathGenome.Internal.Specs.D05.M15.PolynomialBridge.Domain
import MathGenome.Internal.D05.Foundations.FormalPolynomials
import MathGenome.Internal.D05.M15.SymmetricBasis

/-!
The formal polynomial domain theorem uses the coefficient-polynomial domain
instance. The symmetric-algebra conclusion is transported through the already
constructed monomial-coordinate algebra equivalence. Evaluation as a function
plays no role, so the proof also applies over finite fields.
-/

namespace D05.M15.PolynomialBridge.Domain

open D05.Foundations
open Specs.D05.M15.Symmetric

universe u v

theorem formal_polynomial_domain :
    Specs.D05.M15.PolynomialBridge.Domain.formal_polynomial_domain.{u} := by
  intro K _ n
  infer_instance

theorem formal_polynomial_mul_ne_zero :
    Specs.D05.M15.PolynomialBridge.Domain.formal_polynomial_mul_ne_zero.{u} := by
  intro K _ n p q hp hq
  have := formal_polynomial_domain K n
  exact mul_ne_zero hp hq

theorem coefficient_convolution_nonzero :
    Specs.D05.M15.PolynomialBridge.Domain.coefficient_convolution_nonzero.{u} := by
  intro K _ n a b ha hb
  let e := D05.Foundations.FormalPolynomials.coefficientRingEquiv K n
  have : IsDomain (PolynomialCoefficients K n) :=
    e.symm.toMulEquiv.isDomain _
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  by_contra! h
  apply hab
  apply AddMonoidAlgebra.ext
  ext γ
  rw [D05.Foundations.FormalPolynomials.familyOperations K n a b γ |>.2.2.2]
  exact h γ

theorem symmetric_domain_of_basis :
    Specs.D05.M15.PolynomialBridge.Domain.symmetric_domain_of_basis.{u,v} := by
  intro K V _ _ _ n b
  have := formal_polynomial_domain K n
  exact (D05.M15.SymmetricBasis.polynomialEquiv b).toMulEquiv.isDomain _

theorem symmetric_domain :
    Specs.D05.M15.PolynomialBridge.Domain.symmetric_domain.{u,v} := by
  intro K V _ _ _ _
  exact symmetric_domain_of_basis (Module.finBasis K V)

end D05.M15.PolynomialBridge.Domain
