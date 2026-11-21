import MathGenome.Internal.Specs.D07.Ch11.PrimitiveScalar
import MathGenome.Internal.D07.Ch11.ContentPrimitive
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! Clearing denominators, extracting primitive parts, and descending scalars. -/

universe u v

namespace D07.Ch11.PrimitiveScalar

open Polynomial
open scoped nonZeroDivisors
open Specs.D07.Ch11.PrimitiveScalar

theorem primitiveScalarDecomposition : PrimitiveScalarDecomposition.{u, v} := by
  intro R _ _ _ K _ _ _ A hA
  let B : R[X] := IsLocalization.integerNormalization R⁰ A
  have hB : B ≠ 0 := by
    exact fun hz => hA (IsFractionRing.integerNormalization_eq_zero_iff.mp hz)
  obtain ⟨d, hd, he⟩ := IsLocalization.integerNormalization_spec R⁰ A
  have hd0 : algebraMap R K d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hd)
  let c := Specs.D07.Ch11.ContentPrimitive.content B
  have hc := ContentPrimitive.contentIsGcd R B
  have hc0 : c ≠ 0 := fun hz => hB ((ContentPrimitive.contentEqZero R B c hc).mp hz)
  have hcK : algebraMap R K c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hc0
  obtain ⟨A₀, ⟨hBA, hprim⟩, _⟩ := ContentPrimitive.primitivePartExists R B c hB hc
  refine ⟨Units.mk0 (algebraMap R K c / algebraMap R K d) (div_ne_zero hcK hd0),
    A₀, hprim, ?_⟩
  change A = C (algebraMap R K c / algebraMap R K d) * A₀.map (algebraMap R K)
  have hden : C (algebraMap R K d) * A =
      C (algebraMap R K c) * A₀.map (algebraMap R K) := by
    simpa only [B, hBA, Polynomial.map_mul, map_C, Algebra.smul_def,
      algebraMap_apply] using he.symm
  apply mul_left_cancel₀ (show C (algebraMap R K d) ≠ 0 from C_ne_zero.mpr hd0)
  rw [hden, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hd0]

theorem integralPrimitiveScalar : IntegralPrimitiveScalar.{u, v} := by
  intro R _ _ _ K _ _ _ h g t hh he
  let := Specs.D07.Ch11.ContentPrimitive.contentStructure R
  have hlift : C (t : K) ∈ lifts (algebraMap R K) :=
    hh.mul_map_mem_lifts_iff.mp ⟨g, he⟩
  obtain ⟨r, hr⟩ := (lifts_iff_coeff_lifts (C (t : K))).mp hlift 0
  exact ⟨r, by simpa only [coeff_C_zero] using hr⟩

theorem primitiveScalarUnit : PrimitiveScalarUnit.{u, v} := by
  intro R _ _ _ K _ _ _ h g t hh hg he
  obtain ⟨r, hr⟩ := integralPrimitiveScalar R K h g t hh he
  have hgr : g = C r * h := by
    apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    simpa only [Polynomial.map_mul, map_C, hr] using he
  have hrunit : IsUnit r := hg r ⟨h, hgr⟩
  obtain ⟨r, rfl⟩ := hrunit
  exact ⟨r, hr⟩

end D07.Ch11.PrimitiveScalar
