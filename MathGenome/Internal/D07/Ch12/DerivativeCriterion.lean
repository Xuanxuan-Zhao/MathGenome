import MathGenome.Internal.Specs.D07.Ch12.DerivativeCriterion
import MathGenome.Internal.D07.Ch12.SeparableDefinition

/-!
The derivative criterion, K07.12.derivative_criterion.

The upstream simple-root characterization identifies the separability
predicate used here with the source's splitting-field definition. Its
coprimality form is equivalent to the normalized gcd being one.
For irreducibles, the derivative has smaller degree whenever it is nonzero,
so irreducibility makes it coprime to the original polynomial.

In positive characteristic `expand_contract` reconstructs a polynomial
with zero derivative by retaining precisely its coefficients at exponents
divisible by p. Expansion is composition with X^p. Conversely the chain
rule makes the derivative of every such composition zero.
-/

universe u

namespace D07.Ch12.DerivativeCriterion

open Polynomial Specs.D07.Ch12.DerivativeCriterion
open scoped Classical

theorem separable_iff_gcd_one : SeparableIffGcdOne.{u} := by
  intro K _ f _
  change IsCoprime f f.derivative ↔ gcd f f.derivative = 1
  rw [← gcd_isUnit_iff, ← normalize_eq_one, normalize_gcd]

theorem irreducible_separable_iff_derivative_ne_zero :
    IrreducibleSeparableIffDerivativeNeZero.{u} := by
  intro K _ f hf
  exact Polynomial.separable_iff_derivative_ne_zero hf

theorem irreducible_gcd_one_iff_derivative_ne_zero :
    IrreducibleGcdOneIffDerivativeNeZero.{u} := by
  intro K _ f hf
  exact (separable_iff_gcd_one K f hf.ne_zero).symm.trans
    (irreducible_separable_iff_derivative_ne_zero K f hf)

theorem derivative_zero_iff_substitution : DerivativeZeroIffSubstitution.{u} := by
  intro K _ p _ hp f
  constructor
  · intro hf
    refine ⟨Polynomial.contract p f, ?_⟩
    exact (Polynomial.expand_contract p hf (Nat.ne_of_gt hp)).symm
  · rintro ⟨g, rfl⟩
    change (Polynomial.expand K p g).derivative = 0
    rw [Polynomial.derivative_expand]
    simp

theorem nonzero_derivative_counterexample : NonzeroDerivativeCounterexample.{u} := by
  intro K _ _
  constructor
  · have hdeg : (X - 1 : Polynomial K).natDegree = 1 := by
      simpa only [Polynomial.C_1] using Polynomial.natDegree_X_sub_C (1 : K)
    rw [Polynomial.derivative_ne_zero]
    simp [hdeg]
  · intro h
    have hpow := h.of_pow (Polynomial.not_isUnit_X_sub_C (1 : K)) (by decide : 2 ≠ 0)
    exact (by decide : ¬ (2 : ℕ) = 1) hpow.2

end D07.Ch12.DerivativeCriterion
