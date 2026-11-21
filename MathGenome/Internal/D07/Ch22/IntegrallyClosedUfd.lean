import MathGenome.Internal.Specs.D07.Ch22.IntegrallyClosedUfd
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.NormNum

/-!
UFDs are integrally closed, with reduced fractions and the rational
half example (paper.tex:7269–7285).

Mathlib's integral root theorem proves the main assertion by clearing
denominators in a monic equation and applying unique factorization.
After applying that theorem, any reduced presentation r/s of an integral
element satisfies r = a*s in R. Thus s divides r, and reducedness makes
s a unit. This argument covers a zero numerator without cancellation.
-/

universe u v

namespace D07.Ch22.IntegrallyClosedUfd

open Specs.D07.Ch22.IntegrallyClosedUfd

theorem integrallyClosedCharacterization : IntegrallyClosedCharacterization.{u} := by
  intro R _ _
  exact isIntegrallyClosed_iff (FractionRing R)

theorem ufdIsIntegrallyClosed : UfdIsIntegrallyClosed.{u} := by
  intro R _ _ _
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

theorem integralFractionInRing : IntegralFractionInRing.{u, v} := by
  intro R K _ _ _ _ _ _ x hx
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hx

theorem reducedRepresentation : ReducedRepresentation.{u, v} := by
  intro R K _ _ _ _ _ _ x
  refine ⟨IsFractionRing.num R x, IsFractionRing.den R x,
    mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den R x).property,
    (IsFractionRing.mk'_num_den' R x).symm, ?_⟩
  intro p hp hpr hps
  exact hp.not_isUnit (IsFractionRing.num_den_reduced R x hpr hps)

theorem reducedIntegralDenominator : ReducedIntegralDenominator.{u, v} := by
  intro R K _ _ _ _ _ _ r s hs hred hx
  obtain ⟨a, ha⟩ := integralFractionInRing R K _ hx
  have hs' : algebraMap R K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs
  have hrs : r = a * s := by
    apply IsFractionRing.injective R K
    rw [map_mul, ha, div_mul_cancel₀ _ hs']
  have hsr : s ∣ r := ⟨a, by simpa only [mul_comm] using hrs⟩
  have hrel : IsRelPrime s r :=
    (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hs).mpr
      (by
        intro p hps hpr hp
        exact hred p hp hpr hps)
  exact hrel.isUnit_of_dvd hsr

theorem zeroBoundary : ZeroBoundary.{u, v} := by
  intro R K _ _ _ _ _
  refine ⟨by simp, isIntegral_zero, ?_⟩
  intro p hp _ hp1
  exact hp.not_isUnit (isUnit_of_dvd_one hp1)

theorem rationalHalfExample : RationalHalfExample := by
  constructor
  · intro h
    have htwo : IsUnit (2 : ℤ) :=
      reducedIntegralDenominator ℤ ℚ 1 2 (by norm_num)
        (fun p hp hp1 _ => hp.not_isUnit (isUnit_of_dvd_one hp1)) (by simpa using h)
    norm_num [Int.isUnit_iff] at htwo
  · refine ⟨Polynomial.X - Polynomial.C (1 / 2 : ℚ),
      Polynomial.X_sub_C_ne_zero _, ?_⟩
    simp

end D07.Ch22.IntegrallyClosedUfd
