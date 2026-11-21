import MathGenome.Internal.Specs.D07.Ch12.CharacteristicZeroSeparability
import MathGenome.Internal.D07.Ch12.DerivativeCriterion

/-!
Characteristic-zero separability, K07.12.characteristic_zero_separability.

An irreducible polynomial has positive degree. In characteristic zero its
derivative is therefore nonzero, so the upstream irreducible derivative
criterion proves separability. Apply this to the minimal polynomial of
each algebraic element to obtain separability of any algebraic extension.
This does not assert separability for polynomials with repeated factors.
-/

universe u v

namespace D07.Ch12.CharacteristicZeroSeparability

open Specs.D07.Ch12.CharacteristicZeroSeparability

theorem irreducible_polynomial_separable : IrreduciblePolynomialSeparable.{u} := by
  intro K _ _ f hf
  apply (DerivativeCriterion.irreducible_separable_iff_derivative_ne_zero K f hf).mpr
  exact Polynomial.derivative_ne_zero.mpr (Nat.ne_of_gt hf.natDegree_pos)

theorem algebraic_extension_separable : AlgebraicExtensionSeparable.{u, v} := by
  intro K L _ _ _ _ h
  refine ⟨fun α => ?_⟩
  exact irreducible_polynomial_separable K (minpoly K α)
    (minpoly.irreducible (h.isAlgebraic α).isIntegral)

end D07.Ch12.CharacteristicZeroSeparability
