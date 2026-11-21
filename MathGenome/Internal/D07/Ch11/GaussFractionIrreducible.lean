import MathGenome.Internal.Specs.D07.Ch11.GaussFractionIrreducible
import MathGenome.Internal.D07.Ch11.GaussContent
import MathGenome.Internal.D07.Ch11.PrimitiveScalar
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! Gauss's lemma and rescaling specified fraction-field factors. -/

universe u v

namespace D07.Ch11.GaussFractionIrreducible

open Polynomial
open Specs.D07.Ch11.GaussFractionIrreducible

theorem primitiveIrreducibleIff : PrimitiveIrreducibleIff.{u, v} := by
  intro R _ _ _ K _ _ _ f hf
  let := Specs.D07.Ch11.ContentPrimitive.contentStructure R
  exact hf.irreducible_iff_irreducible_map_fraction_map

theorem rescaleFactorization : RescaleFactorization.{u, v} := by
  intro R _ _ _ K _ _ _ f A B hf he hAdeg hBdeg
  have hmap : f.map (algebraMap R K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (IsFractionRing.injective R K)).mpr hf
  have hA : A ≠ 0 := left_ne_zero_of_mul (he ▸ hmap)
  have hB : B ≠ 0 := right_ne_zero_of_mul (he ▸ hmap)
  obtain ⟨u, A₀, hA₀, hAu⟩ :=
    PrimitiveScalar.primitiveScalarDecomposition R K A hA
  obtain ⟨v, B₀, hB₀, hBv⟩ :=
    PrimitiveScalar.primitiveScalarDecomposition R K B hB
  have hprod := GaussContent.primitiveProduct R A₀ B₀ hA₀ hB₀
  have hscalar : f.map (algebraMap R K) =
      C (↑(u * v) : K) * (A₀ * B₀).map (algebraMap R K) := by
    rw [he, hAu, hBv, Polynomial.map_mul, Units.val_mul, map_mul]
    ring
  obtain ⟨r, hr⟩ :=
    PrimitiveScalar.integralPrimitiveScalar R K (A₀ * B₀) f (u * v) hprod hscalar
  let a : R[X] := C r * A₀
  have ha : a.map (algebraMap R K) = C (v : K) * A := by
    simp only [a, Polynomial.map_mul, map_C, hr, Units.val_mul, hAu, map_mul]
    ring
  have hb : B₀.map (algebraMap R K) = C (↑(v⁻¹) : K) * B := by
    rw [hBv, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  have hfab : f = a * B₀ := by
    apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    rw [Polynomial.map_mul, ha, hb]
    calc
      f.map (algebraMap R K) = A * B := he
      _ = C (v : K) * A * (C (↑(v⁻¹) : K) * B) := by
        rw [mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
  have hadeg : a.degree = A.degree := by
    rw [← degree_map_eq_of_injective (IsFractionRing.injective R K) a, ha]
    exact degree_C_mul (Units.ne_zero v)
  have hbdeg : B₀.degree = B.degree := by
    rw [← degree_map_eq_of_injective (IsFractionRing.injective R K) B₀, hb]
    exact degree_C_mul (Units.ne_zero (v⁻¹))
  refine ⟨a, B₀, v, hfab, ha, hb, hadeg, hbdeg, ?_, ?_⟩
  · simpa only [natDegree, hadeg] using hAdeg
  · simpa only [natDegree, hbdeg] using hBdeg

theorem monicIrreducibleIff : MonicIrreducibleIff.{u, v} := by
  intro R _ _ _ K _ _ _ f hf
  exact primitiveIrreducibleIff R K f hf.isPrimitive

theorem primitiveConstant : PrimitiveConstant.{u, v} := by
  intro R _ _ _ K _ _ _ f hf hd
  have he : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hd
  have hu : IsUnit f := by
    rw [he]
    exact isUnit_C.mpr (hf (f.coeff 0) (he ▸ dvd_rfl))
  have hmap : IsUnit (f.map (algebraMap R K)) := hu.map (mapRingHom (algebraMap R K))
  exact ⟨hu, hmap, fun h => h.not_isUnit hu, fun h => h.not_isUnit hmap⟩

theorem nonprimitiveCounterexample : NonprimitiveCounterexample := by
  let f : ℤ[X] := C 2 * X + C 2
  have he : f = C 2 * (X + 1) := by simp [f, mul_add]
  have htwo : ¬IsUnit (C (2 : ℤ)) := by
    rw [isUnit_C]
    norm_num [Int.isUnit_iff]
  have hlin : ¬IsUnit (X + 1 : ℤ[X]) := by
    intro h
    have hd := Polynomial.natDegree_eq_zero_of_isUnit h
    simp at hd
  refine ⟨?_, he, htwo, hlin, ?_, ?_⟩
  · intro h
    have hunit : IsUnit (2 : ℤ) := h 2 ⟨X + 1, he⟩
    exact htwo (isUnit_C.mpr hunit)
  · intro h
    exact (h.isUnit_or_isUnit he).elim htwo hlin
  · apply irreducible_of_degree_eq_one
    have hm : (C (2 : ℤ) * X + C 2).map (algebraMap ℤ ℚ) =
        C (2 : ℚ) * X + C 2 := by simp [C_ofNat]
    rw [hm]
    exact degree_linear (by norm_num)

end D07.Ch11.GaussFractionIrreducible
