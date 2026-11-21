import MathGenome.Internal.Specs.D07.Ch11.DegreeArithmetic
import MathGenome.Internal.D07.Ch11.DegreeConventions
import MathGenome.Internal.D07.Ch11.PolynomialArithmetic
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
K07.11.degree_arithmetic. The coefficient at the sum of the natural degrees
is the product of leading coefficients. When it is nonzero, it detects a
nonzero product and forces the upper degree bound to be an equality.
Units and domains give the required nonvanishing in their respective cases.
In `ZMod 4`, the leading product `2 * 2` instead vanishes.
-/

universe u

namespace D07.Ch11.DegreeArithmetic

open Polynomial
open Specs.D07.Ch11.DegreeArithmetic

theorem degreeAdditionBound : DegreeAdditionBound.{u} := by
  intro R _ f g
  exact Polynomial.degree_add_le f g

theorem degreeMultiplicationBound : DegreeMultiplicationBound.{u} := by
  intro R _ f g
  exact Polynomial.degree_mul_le f g

theorem productOfNonzeroLeadingCoefficients :
    ProductOfNonzeroLeadingCoefficients.{u} := by
  intro R _ f g _ _ hlc
  have hprod : (f * g).leadingCoeff ≠ 0 := by
    rwa [Polynomial.leadingCoeff_mul' hlc]
  exact ⟨Polynomial.leadingCoeff_ne_zero.mp hprod,
    Polynomial.degree_mul' hlc, Polynomial.leadingCoeff_mul' hlc⟩

theorem leadingProductNonzeroOfUnit : LeadingProductNonzeroOfUnit.{u} := by
  intro R _ f g hf hg hunit
  rcases hunit with hu | hu
  · intro hzero
    exact (DegreeConventions.nonzeroLeadingCoefficient R g hg)
      (hu.mul_right_eq_zero.mp hzero)
  · intro hzero
    exact (DegreeConventions.nonzeroLeadingCoefficient R f hf)
      (hu.mul_left_eq_zero.mp hzero)

theorem productOfUnitLeadingCoefficient : ProductOfUnitLeadingCoefficient.{u} := by
  intro R _ f g hf hg hu
  exact productOfNonzeroLeadingCoefficients R f g hf hg
    (leadingProductNonzeroOfUnit R f g hf hg hu)

theorem polynomialDomain : PolynomialDomain.{u} := by
  intro R _ _
  infer_instance

theorem productOverDomain : ProductOverDomain.{u} := by
  intro R _ _ f g hf hg
  exact productOfNonzeroLeadingCoefficients R f g hf hg
    (mul_ne_zero (DegreeConventions.nonzeroLeadingCoefficient R f hf)
      (DegreeConventions.nonzeroLeadingCoefficient R g hg))

theorem degreeDropExample : DegreeDropExample := by
  have htwo : (2 : ZMod 4) ≠ 0 := by decide
  have hfour : (2 : ZMod 4) * 2 = 0 := by decide
  have hd : (C (2 : ZMod 4) * X).degree = (1 : WithBot ℕ) :=
    Polynomial.degree_C_mul_X htwo
  have hn : C (2 : ZMod 4) * X ≠ 0 := by
    intro hzero
    have hc := congrArg (fun p : Polynomial (ZMod 4) => p.coeff 1) hzero
    exact htwo (by simpa using hc)
  have hz : (C (2 : ZMod 4) * X) * (C 2 * X) = 0 := by
    rw [mul_mul_mul_comm, ← map_mul, hfour, map_zero, zero_mul]
  change C (2 : ZMod 4) * X ≠ 0 ∧ C (2 : ZMod 4) * X ≠ 0 ∧ _
  refine ⟨hn, hn, hd, hd, hz, ?_, ?_, ?_⟩
  · simpa only [pow_two] using hz
  · rw [hz, Polynomial.degree_zero]
  · rw [hz, Polynomial.degree_zero, hd]
    decide

end D07.Ch11.DegreeArithmetic
