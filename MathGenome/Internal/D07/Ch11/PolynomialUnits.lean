import MathGenome.Internal.Specs.D07.Ch11.PolynomialUnits
import MathGenome.Internal.D07.Ch11.CoefficientMap
import MathGenome.Internal.D07.Ch11.PolynomialUnitsNilpotentCoefficientIdeal
import MathGenome.Internal.D07.Ch09.NilpotentPrimeSeparation
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
Units of formal polynomial rings. Necessity of nilpotent positive
coefficients follows by reducing modulo each prime ideal, where a unit
polynomial must be constant. Sufficiency uses the proved finite
coefficient-ideal nilpotence argument. Both directions allow the zero ring.
-/

universe u

namespace D07.Ch11.PolynomialUnits

open Polynomial
open Specs.D07.Ch11.PolynomialUnits

theorem domainUnitIffConstant : DomainUnitIffConstant.{u} := by
  intro R _ _ f
  exact Polynomial.isUnit_iff.trans
    (exists_congr fun a => and_congr_right fun _ => eq_comm)

theorem unitIffCoefficients : UnitIffCoefficients.{u} := by
  intro R _ f
  constructor
  · intro hf
    constructor
    · simpa only [Polynomial.constantCoeff_apply] using
        hf.map (Polynomial.constantCoeff : Polynomial R →+* R)
    · intro i hi
      apply (D07.Ch09.NilpotentPrimeSeparation.memEveryPrimeIffNilpotent R
        (f.coeff i)).mp
      intro P hP
      let : P.IsPrime := hP
      let φ : R →+* R ⧸ P := Ideal.Quotient.mk P
      have hmap : IsUnit (mapRingHom φ f) := hf.map (mapRingHom φ)
      obtain ⟨a, _, ha⟩ :=
        (domainUnitIffConstant (R ⧸ P) (mapRingHom φ f)).mp hmap
      have hzero : φ (f.coeff i) = 0 := by
        rw [← D07.Ch11.CoefficientMap.coefficientFormula R (R ⧸ P) φ f i, ha]
        exact Polynomial.coeff_C_of_ne_zero (Nat.ne_of_gt hi)
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  · rintro ⟨hunit, hnil⟩
    obtain ⟨g, hfg, _⟩ :=
      D07.Ch11.PolynomialUnitsNilpotentCoefficientIdeal.polynomialInverse R f hunit hnil
    exact IsUnit.of_mul_eq_one g hfg

theorem nonconstantUnitExample : NonconstantUnitExample := by
  have hfour : (2 : ZMod 4) * 2 = 0 := by decide
  have hsquare : (C (2 : ZMod 4) * X) ^ 2 = 0 := by
    rw [mul_pow, ← map_pow, pow_two (2 : ZMod 4), hfour, map_zero, zero_mul]
  have hinv : (1 + C (2 : ZMod 4) * X) * (1 - C 2 * X) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, ← pow_two, hsquare]
    simp
  change _ ∧ _ ∧ _ ∧ _
  refine ⟨hinv, by rw [mul_comm]; exact hinv,
    IsUnit.of_mul_eq_one _ hinv, ?_⟩
  intro a ha
  have hc := congrArg (fun p : Polynomial (ZMod 4) => p.coeff 1) ha
  have : (2 : ZMod 4) = 0 := by
    simpa [Polynomial.coeff_one] using hc
  exact (by decide : (2 : ZMod 4) ≠ 0) this

end D07.Ch11.PolynomialUnits
