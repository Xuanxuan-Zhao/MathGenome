import MathGenome.Internal.Specs.D07.Ch11.RationalRoot
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Coprime.Lemmas

/-!
The rational root test, including signed reduced denominators and the
constant, zero-root and monic cases (paper.tex:2479–2499).

Scaling the roots clears denominators without replacing r/s by a chosen
normal form. The constant and leading terms of the scaled polynomial
then give the two divisibilities, and Bézout coprimality cancels the
powers of the other factor. This argument permits r=0 and s<0.
-/

namespace D07.Ch11.RationalRoot

open Polynomial
open Specs.D07.Ch11.RationalRoot

/-- Clearing denominators yields an integer polynomial with root r. -/
theorem isRoot_scaleRoots {f : Polynomial ℤ} {r s : ℤ} (hs : s ≠ 0)
    (hroot : f.eval₂ (Int.castRingHom ℚ) ((r : ℚ) / (s : ℚ)) = 0) :
    (f.scaleRoots s).IsRoot r := by
  apply isRoot_of_eval₂_map_eq_zero (f := Int.castRingHom ℚ)
    (Int.cast_injective (α := ℚ))
  exact scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero
    (Int.cast_injective (α := ℚ)) hroot (mem_nonZeroDivisors_iff_ne_zero.mpr hs)

theorem rationalRootDivisibility : RationalRootDivisibility := by
  intro f _ r s hcop hs hroot
  have hscaled := isRoot_scaleRoots hs hroot
  have hcop' : IsCoprime r s := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hconstant : r ∣ f.coeff 0 * s ^ f.natDegree := by
    have h := dvd_term_of_isRoot_of_dvd_terms (p := r) 0 hscaled (fun j hj => by
      apply dvd_mul_of_dvd_right
      simpa using (pow_dvd_pow r (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj))))
    simpa only [coeff_scaleRoots, Nat.sub_zero, pow_zero, mul_one] using h
  have hleading : s ∣ f.leadingCoeff * r ^ f.natDegree := by
    rw [← coeff_scaleRoots_natDegree f s]
    apply dvd_term_of_isRoot_of_dvd_terms _ hscaled
    intro j hj
    by_cases hlt : j < f.natDegree
    · rw [coeff_scaleRoots]
      apply dvd_mul_of_dvd_left
      apply dvd_mul_of_dvd_right
      simpa using (pow_dvd_pow s (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt)))
    · rw [coeff_scaleRoots, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne
        (Nat.le_of_not_gt hlt) (Ne.symm hj)), zero_mul, zero_mul]
      exact dvd_zero s
  exact ⟨hcop'.pow_right.dvd_of_dvd_mul_right hconstant,
    hcop'.symm.pow_right.dvd_of_dvd_mul_right hleading⟩

theorem noRootDegreeZero : NoRootDegreeZero := by
  intro f hf hdeg q hroot
  have hC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
  have hzero : f.coeff 0 = 0 := by
    apply Int.cast_injective (α := ℚ)
    rw [hC, eval₂_C] at hroot
    exact hroot
  exact hf (by rw [hC, hzero, C_0])

theorem zeroRootReduced : ZeroRootReduced := by
  intro f hf s hcop hs hroot
  have hdvd := rationalRootDivisibility f hf 0 s hcop hs hroot
  have hsunit : IsUnit s := (isCoprime_zero_left.mp
    (Int.isCoprime_iff_gcd_eq_one.mpr hcop))
  exact ⟨Int.isUnit_iff.mp hsunit, zero_dvd_iff.mp hdvd.1, hdvd⟩

theorem monicDenominator : MonicDenominator := by
  intro f hf r s hcop hs hroot
  have hdvd : s ∣ (1 : ℤ) := by
    simpa only [hf.leadingCoeff] using
      (rationalRootDivisibility f hf.ne_zero r s hcop hs hroot).2
  exact ⟨hdvd, Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)⟩

theorem monicRationalRoot : MonicRationalRoot := by
  intro f hf q hroot
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hf (show aeval q f = 0 from hroot)
  exact ⟨z, hz⟩

end D07.Ch11.RationalRoot
