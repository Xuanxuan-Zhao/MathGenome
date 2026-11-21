import MathGenome.Internal.Specs.D07.Ch15.CyclotomicPolynomials
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Cyclotomic integrality, degree, factorization, and rational irreducibility.
The library's integer cyclotomic polynomial is identified with the source's
complex primitive-root product before its algebraic properties are used.
The finite-field example uses its coefficient image, not a product over
primitive roots restricted to the coefficient field.
-/

namespace D07.Ch15.CyclotomicPolynomials

open Polynomial Specs.D07.Ch15.CyclotomicPolynomials

theorem primitive_roots_meaning : PrimitiveRootsMeaning := by
  intro n hn ζ
  exact mem_primitiveRoots hn

theorem integer_realization : IntegerRealization := by
  intro n _
  exact (int_cyclotomic_spec n).1

theorem unique_integer_realization : UniqueIntegerRealization := by
  intro n hn
  refine ⟨cyclotomic n ℤ, integer_realization n hn, ?_⟩
  intro P hP
  exact Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    (hP.trans (integer_realization n hn).symm)

private theorem complex_realization (n : ℕ) :
    cyclotomic n ℂ = complexPrimitiveProduct n := by
  rw [← map_cyclotomic_int n ℂ]
  exact (int_cyclotomic_spec n).1

theorem coefficient_compatibility : CoefficientCompatibility := by
  intro n _
  refine ⟨map_cyclotomic n _, ?_, map_cyclotomic n _⟩
  rw [map_cyclotomic, complex_realization]

theorem monicity : Monicity := by
  intro n _
  exact ⟨cyclotomic.monic n ℤ, cyclotomic'.monic n ℂ⟩

theorem degree : Degree := by
  intro n _
  rw [← complex_realization]
  exact ⟨degree_cyclotomic n ℤ, natDegree_cyclotomic n ℤ,
    degree_cyclotomic n ℂ, natDegree_cyclotomic n ℂ⟩

theorem divisor_factorization : DivisorFactorization := by
  intro n hn
  exact (prod_cyclotomic_eq_X_pow_sub_one hn ℤ).symm

theorem complex_divisor_factorization : ComplexDivisorFactorization := by
  intro n hn
  simp_rw [← complex_realization]
  exact (prod_cyclotomic_eq_X_pow_sub_one hn ℂ).symm

theorem rational_irreducibility : RationalIrreducibility := by
  intro n hn
  exact cyclotomic.irreducible_rat hn

theorem integral_irreducibility : IntegralIrreducibility := by
  intro n hn
  exact ⟨cyclotomic.isPrimitive n ℤ, cyclotomic.irreducible hn⟩

theorem minimal_polynomial : MinimalPolynomial := by
  intro n hn ζ hζ
  rw [map_cyclotomic]
  exact (cyclotomic_eq_minpoly_rat hζ hn).symm

theorem first_cyclotomic : FirstCyclotomic := by
  rw [FirstCyclotomic, ← complex_realization]
  exact ⟨cyclotomic_one ℤ, cyclotomic_one ℂ⟩

/-- A computation in every commutative coefficient ring, used for all three
coefficient fields in the example. -/
theorem cyclotomic_four (R : Type*) [CommRing R] :
    cyclotomic 4 R = X ^ 2 + 1 := by
  simpa [Finset.sum_range_succ, add_comm] using
    (cyclotomic_prime_pow_eq_geom_sum (R := R) (n := 1) Nat.prime_two)

theorem fourth_cyclotomic : FourthCyclotomic := by
  refine ⟨cyclotomic_four ℤ, ?_, ?_⟩
  · rw [← complex_realization, cyclotomic_four]
  · rw [← cyclotomic_four ℚ]
    exact rational_irreducibility 4 (by decide)

theorem quartic_factorization : QuarticFactorization := by
  unfold QuarticFactorization
  ring

theorem mod_five_factorization : ModFiveFactorization := by
  refine ⟨cyclotomic_four (ZMod 5), ?_⟩
  have hfour : (-4 : ZMod 5) = 1 := by decide
  calc
    (X ^ 2 + 1 : Polynomial (ZMod 5)) = X ^ 2 + C (-4) := by rw [hfour, C_1]
    _ = (X - C 2) * (X + C 2) := by
      rw [show (-4 : ZMod 5) = -(2 ^ 2) by decide, map_neg, map_pow]
      ring

theorem mod_five_reducibility : ModFiveReducibility := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hminus : (X - C 2 : Polynomial (ZMod 5)).degree = 1 := degree_X_sub_C 2
  have hplus : (X + C 2 : Polynomial (ZMod 5)).degree = 1 := degree_X_add_C 2
  have hminus_unit : ¬IsUnit (X - C 2 : Polynomial (ZMod 5)) := by
    intro h
    have := Polynomial.degree_eq_zero_of_isUnit h
    rw [hminus] at this
    exact one_ne_zero this
  have hplus_unit : ¬IsUnit (X + C 2 : Polynomial (ZMod 5)) := by
    intro h
    have := Polynomial.degree_eq_zero_of_isUnit h
    rw [hplus] at this
    exact one_ne_zero this
  refine ⟨hminus, hplus, hminus_unit, hplus_unit, ?_, by decide⟩
  intro h
  have heq : cyclotomic 4 (ZMod 5) = (X - C 2) * (X + C 2) :=
    mod_five_factorization.1.trans mod_five_factorization.2
  exact (h.isUnit_or_isUnit heq).elim hminus_unit hplus_unit

end D07.Ch15.CyclotomicPolynomials
