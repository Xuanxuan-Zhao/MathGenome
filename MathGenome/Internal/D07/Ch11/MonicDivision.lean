import MathGenome.Internal.Specs.D07.Ch11.MonicDivision
import MathGenome.Internal.D07.Ch11.DegreeArithmetic
import Mathlib.Algebra.Polynomial.Div
import Lean.Elab.Tactic.Omega

/-!
K07.11.monic_division. Mathlib's monic division provides reconstruction,
the strict remainder bound, and uniqueness. For a unit leading coefficient
`u`, normalize the divisor to `C u⁻¹ * g`. This preserves its degree.
Multiplying a quotient by `C u⁻¹` transports division back to `g`, and
multiplication by `C u` transports it in the other direction, including
uniqueness. No field or absence-of-zero-divisors assumption is used.
-/

universe u

namespace D07.Ch11.MonicDivision

open Polynomial
open Specs.D07.Ch11.MonicDivision

theorem monicDivision : UniqueMonicDivision.{u} := by
  intro R _ _ f g hg
  refine ⟨(f /ₘ g, f %ₘ g), ⟨?_, Polynomial.degree_modByMonic_lt f hg⟩, ?_⟩
  · simpa only [add_comm, mul_comm] using (Polynomial.modByMonic_add_div f g).symm
  · rintro ⟨q, r⟩ ⟨heq, hdeg⟩
    have h := Polynomial.div_modByMonic_unique q r hg
      ⟨by simpa only [add_comm, mul_comm] using heq.symm, hdeg⟩
    exact Prod.ext h.1.symm h.2.symm

theorem unitLeadingCoefficientDivision : UnitLeadingCoefficientDivision.{u} := by
  intro R _ _ f g hg
  obtain ⟨u, hu⟩ := hg
  let h : Polynomial R := C (↑(u⁻¹) : R) * g
  have hh : h.Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by
    rw [← hu]
    exact u.inv_mul)
  have hd : h.degree = g.degree :=
    Polynomial.degree_C_mul_of_isUnit (u⁻¹).isUnit g
  obtain ⟨⟨q, r⟩, ⟨heq, hdeg⟩, huniq⟩ := monicDivision R f h hh
  refine ⟨(q * C (↑(u⁻¹) : R), r), ⟨?_, ?_⟩, ?_⟩
  · simpa only [h, mul_assoc] using heq
  · exact hd ▸ hdeg
  · rintro ⟨q', r'⟩ ⟨heq', hdeg'⟩
    have hinv : C (↑u : R) * C (↑(u⁻¹) : R) = (1 : Polynomial R) := by
      rw [← map_mul, u.mul_inv, map_one]
    have ht : (q' * C (↑u : R), r') = (q, r) := huniq _ ⟨by
      simpa only [h, mul_assoc, ← mul_assoc (C (↑u : R)), hinv, one_mul]
        using heq', by rwa [hd]⟩
    have htq : q' * C (↑u : R) = q := congrArg Prod.fst ht
    have htr : r' = r := congrArg Prod.snd ht
    have hq : q' = q * C (↑(u⁻¹) : R) := by
      calc
        q' = (q' * C (↑u : R)) * C (↑(u⁻¹) : R) := by
          rw [mul_assoc, hinv, mul_one]
        _ = q * C (↑(u⁻¹) : R) := by rw [htq]
    exact Prod.ext hq htr

theorem divisionByOne : DivisionByOne.{u} := by
  intro R _ _ f q r heq hdeg
  have hr : r = 0 := Polynomial.degree_eq_bot.mp (by
    simpa only [Polynomial.degree_one, WithBot.lt_zero_iff_eq_bot] using hdeg)
  exact ⟨by simpa only [hr, mul_one, add_zero] using heq.symm, hr⟩

theorem constantDivisorObstruction : ConstantDivisorObstruction := by
  refine ⟨by simp, by simp, ?_⟩
  rintro ⟨q, r, heq, hdeg⟩
  have hr : r = 0 := Polynomial.degree_eq_bot.mp
    ((WithBot.lt_zero_iff_eq_bot r.degree).mp hdeg)
  have hc := congrArg (fun p : Polynomial ℤ => p.coeff 1) heq
  simp only [hr, add_zero, Polynomial.coeff_X_one, Polynomial.coeff_mul_C] at hc
  omega

end D07.Ch11.MonicDivision
