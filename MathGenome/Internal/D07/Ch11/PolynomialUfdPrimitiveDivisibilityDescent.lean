import MathGenome.Internal.Specs.D07.Ch11.PolynomialUfdPrimitiveDivisibilityDescent
import MathGenome.Internal.D07.Ch11.PrimitiveScalar
import MathGenome.Internal.D07.Ch11.GaussContent
import MathGenome.Internal.D07.Ch11.FieldPolynomialPid
import Mathlib.RingTheory.Polynomial.Basic

/-!
The prime-factor step in K07.11.polynomial_ufd. For a nonzero dividend,
write the fraction-field quotient as a scalar times a primitive polynomial.
Gauss's product theorem and scalar descent put that scalar in R. Primality
then descends from the field polynomial ring. The constant-prime theorem
uses the coefficient-ideal prime criterion, not polynomial unique factorization.
-/

universe u v

namespace D07.Ch11.PolynomialUfdPrimitiveDivisibilityDescent

open Polynomial
open Specs.D07.Ch11.PolynomialUfdPrimitiveDivisibilityDescent

theorem primitiveDivisibilityDescent : PrimitiveDivisibilityDescent.{u, v} := by
  intro R _ _ _ K _ _ _ h a hh _ hdiv
  by_cases ha : a = 0
  · rw [ha]
    exact dvd_zero h
  obtain ⟨Q, hQ⟩ := hdiv
  have hinj := Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  have hQ0 : Q ≠ 0 := by
    intro hz
    have haz : a.map (algebraMap R K) = 0 := by simpa only [hz, mul_zero] using hQ
    apply ha
    apply hinj
    simpa only [Polynomial.map_zero] using haz
  obtain ⟨t, Q₀, hprim, he⟩ :=
    PrimitiveScalar.primitiveScalarDecomposition R K Q hQ0
  have hprod := GaussContent.primitiveProduct R h Q₀ hh hprim
  have hae : a.map (algebraMap R K) =
      C (t : K) * (h * Q₀).map (algebraMap R K) := by
    rw [hQ, he, Polynomial.map_mul]
    ac_rfl
  obtain ⟨r, hr⟩ := PrimitiveScalar.integralPrimitiveScalar R K (h * Q₀) a t hprod hae
  refine ⟨C r * Q₀, hinj ?_⟩
  rw [Polynomial.map_mul, Polynomial.map_mul, map_C, hr, hQ, he]

theorem primitiveIrreducibleIsPrime : PrimitiveIrreducibleIsPrime.{u, v} := by
  intro R _ _ _ K _ _ _ h hh hdeg hirr
  let : UniqueFactorizationMonoid (Polynomial K) :=
    (FieldPolynomialPid.fieldPolynomialUFD K).1
  have hprime : Prime (h.map (algebraMap R K)) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  refine ⟨hh.ne_zero, ?_, ?_⟩
  · intro hu
    exact hirr.not_isUnit (hu.map (mapRingHom (algebraMap R K)))
  · intro a b hab
    have hm : h.map (algebraMap R K) ∣
        a.map (algebraMap R K) * b.map (algebraMap R K) := by
      have hm := map_dvd (mapRingHom (algebraMap R K)) hab
      change h.map (algebraMap R K) ∣ (a * b).map (algebraMap R K) at hm
      rwa [Polynomial.map_mul] at hm
    rcases hprime.dvd_or_dvd hm with ha | hb
    · exact Or.inl (primitiveDivisibilityDescent R K h a hh hdeg ha)
    · exact Or.inr (primitiveDivisibilityDescent R K h b hh hdeg hb)

theorem constantPrime : ConstantPrime.{u} := by
  intro R _ _ _ p hp
  exact Polynomial.prime_C_iff.mpr hp

end D07.Ch11.PolynomialUfdPrimitiveDivisibilityDescent
