import MathGenome.Internal.Specs.D07.Ch11.PolynomialArithmetic
import MathGenome.Internal.D07.Ch11.PolynomialDefinition

/-!
The polynomial ring over any associative unital coefficient ring,
K07.11.polynomial_arithmetic. All noncommutative assertions retain the
order of coefficient factors, and no nontriviality assumption is used.
-/

universe u

namespace D07.Ch11.PolynomialArithmetic

open Polynomial
open Specs.D07.Ch11.PolynomialArithmetic

theorem coefficientAddition : CoefficientAddition.{u} := by
  intro R _ f g n
  exact Polynomial.coeff_add f g n

theorem coefficientNegation : CoefficientNegation.{u} := by
  intro R _ f n
  exact Polynomial.coeff_neg f n

theorem coefficientMultiplication : CoefficientMultiplication.{u} := by
  intro R _ f g n
  exact Polynomial.coeff_mul f g n

theorem supportAddition : SupportAddition.{u} := by
  intro R _ f g
  exact Polynomial.support_add

theorem supportNegation : SupportNegation.{u} := by
  intro R _ f
  exact Polynomial.support_neg

theorem supportMultiplication : SupportMultiplication.{u} := by
  intro R _ f g n hn
  have hcoeff : (f * g).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  rw [coefficientMultiplication R f g n] at hcoeff
  obtain ⟨⟨i, j⟩, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  have hi : i ∈ f.support := Polynomial.mem_support_iff.mpr fun h => by
    apply hne
    simp only [h, zero_mul]
  have hj : j ∈ g.support := Polynomial.mem_support_iff.mpr fun h => by
    apply hne
    simp only [h, mul_zero]
  exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr ⟨hi, hj⟩,
    Finset.mem_antidiagonal.mp hij⟩

theorem finiteSupportClosure : FiniteSupportClosure.{u} := by
  intro R _ f g
  exact ⟨PolynomialDefinition.finiteCoefficientSupport R (f + g),
    PolynomialDefinition.finiteCoefficientSupport R (-f),
    PolynomialDefinition.finiteCoefficientSupport R (f * g)⟩

theorem polynomialRingStructure : PolynomialRingStructure.{u} := by
  intro R _
  exact ⟨inferInstance, rfl, rfl, rfl⟩

theorem multiplicativeLaws : MultiplicativeLaws.{u} := by
  intro R _ f g h
  exact ⟨mul_assoc f g h, by rw [map_one, one_mul],
    by rw [map_one, mul_one], mul_add f g h, add_mul f g h⟩

theorem constantRingHomomorphism : ConstantRingHomomorphism.{u} := by
  intro R _
  exact ⟨Polynomial.C, fun _ => rfl⟩

theorem polynomialCommutativeRingStructure : PolynomialCommutativeRingStructure.{u} := by
  intro R _
  exact ⟨inferInstance, rfl⟩

theorem indeterminateConstantCoefficients : IndeterminateConstantCoefficients.{u} := by
  intro R _ a n
  constructor
  · rw [Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial]
    simpa only [eq_comm] using (Polynomial.coeff_monomial (n := 1) (m := n) (a := a))
  · rw [Polynomial.C_mul_X_eq_monomial]
    simpa only [eq_comm] using (Polynomial.coeff_monomial (n := 1) (m := n) (a := a))

theorem indeterminateCommutesConstants : IndeterminateCommutesConstants.{u} := by
  intro R _ a
  exact Polynomial.X_mul_C a

theorem indeterminateCentral : IndeterminateCentral.{u} := by
  intro R _ f
  exact Polynomial.X_mul

end D07.Ch11.PolynomialArithmetic
