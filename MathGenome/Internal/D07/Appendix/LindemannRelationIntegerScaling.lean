import MathGenome.Internal.Specs.D07.Appendix.LindemannRelationIntegerScaling
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Int.Basic

namespace D07.Appendix.LindemannRelationIntegerScaling

open Polynomial
open Specs.D07.Appendix.LindemannRelationIntegerScaling

/-- Clearing denominators and scaling once more by the same denominator makes
the scale positive even if the localization API chose a negative denominator. -/
theorem positive_integer_scale (P : ℚ[X]) (hP : P.Monic) :
    ∃ (a : ℤ) (Q : ℤ[X]), 0 < a ∧ Q.Monic ∧
      Q.map (algebraMap ℤ ℚ) = P.scaleRoots (a : ℚ) := by
  let d := IsLocalization.commonDenom (nonZeroDivisors ℤ) P.support P.coeff
  have hd : (d : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hl := IsLocalization.scaleRoots_commonDenom_mem_lifts
    (nonZeroDivisors ℤ) P (by rw [hP.leadingCoeff]; exact one_mem _)
  obtain ⟨q, hq, _, hqm⟩ := lifts_and_natDegree_eq_and_monic hl
    ((monic_scaleRoots_iff _).mpr hP)
  refine ⟨(d : ℤ) * d, q.scaleRoots (d : ℤ), mul_self_pos.mpr hd,
    (monic_scaleRoots_iff _).mpr hqm, ?_⟩
  rw [map_scaleRoots q (d : ℤ) (algebraMap ℤ ℚ) (by rw [hqm.leadingCoeff]; simp),
    hq, ← scaleRoots_mul]
  congr 1
  exact (Int.cast_mul (d : ℤ) (d : ℤ)).symm

/-- The coefficientwise root-scaling operation is exactly the displayed
change of variable when the scale is nonzero. -/
theorem scaleRoots_change_variable (P : ℚ[X]) (a : ℚ) (ha : a ≠ 0) :
    P.scaleRoots a = C (a ^ P.natDegree) * P.comp (C a⁻¹ * X) := by
  have h := scaleRoots_eval₂_mul (p := P) (C : ℚ →+* ℚ[X]) (C a⁻¹ * X) a
  change (P.scaleRoots a).comp (C a * (C a⁻¹ * X)) =
    C a ^ P.natDegree * P.comp (C a⁻¹ * X) at h
  simpa only [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul,
    comp_X, ← C_pow] using h

/-- Scaling a finite list product preserves all root multiplicities. -/
theorem scaleRoots_root_list (β : List ℂ) (a : ℂ) :
    ((β.map (fun b => X - C b)).prod).scaleRoots a =
      (β.map (fun b => X - C (a * b))).prod := by
  induction β with
  | nil => simp
  | cons b β ih =>
    simp only [List.map_cons, List.prod_cons, mul_scaleRoots_of_noZeroDivisors,
      X_sub_C_scaleRoots, ih, mul_comm b a]

/-- Monicity and degree of the formal root-list product, including the empty list. -/
theorem root_list_monic_degree (β : List ℂ) :
    (β.map (fun b => X - C b)).prod.Monic ∧
      (β.map (fun b => X - C b)).prod.natDegree = β.length := by
  induction β with
  | nil => simp
  | cons b β ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    exact ⟨(monic_X_sub_C b).mul ih.1, by
      rw [natDegree_mul (monic_X_sub_C b).ne_zero ih.1.ne_zero,
        natDegree_X_sub_C, ih.2, Nat.add_comm]⟩

/-- At zero each factor is the negative of its nonzero listed root. -/
theorem root_list_constant_ne_zero (β : List ℂ) (hβ : ∀ b ∈ β, b ≠ 0) :
    (β.map (fun b => X - C b)).prod.coeff 0 ≠ 0 := by
  induction β with
  | nil => simp
  | cons b β ih =>
    have hb := hβ b List.mem_cons_self
    have ht : ∀ c ∈ β, c ≠ 0 := fun c hc => hβ c (List.mem_cons_of_mem b hc)
    simpa only [List.map_cons, List.prod_cons, mul_coeff_zero, coeff_sub,
      coeff_X_zero, coeff_C_zero, zero_sub] using mul_ne_zero (neg_ne_zero.mpr hb) (ih ht)

theorem integer_scaling : IntegerScaling := by
  intro β P hβ hP
  have hm : P.Monic := (Polynomial.monic_map_iff).mp (hP ▸ (root_list_monic_degree β).1)
  have hn : P.natDegree = β.length := by
    rw [← hm.natDegree_map (algebraMap ℚ ℂ), hP]
    exact (root_list_monic_degree β).2
  obtain ⟨a, Q, ha, hQm, hQ⟩ := positive_integer_scale P hm
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hQC : Q.map (algebraMap ℤ ℂ) =
      (β.map (fun b => X - C ((a : ℂ) * b))).prod := by
    calc
      _ = (Q.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ) := by
        rw [map_map]; rfl
      _ = (P.scaleRoots (a : ℚ)).map (algebraMap ℚ ℂ) := by rw [hQ]
      _ = (P.map (algebraMap ℚ ℂ)).scaleRoots (a : ℂ) := by
        rw [map_scaleRoots P (a : ℚ) (algebraMap ℚ ℂ) (by rw [hm.leadingCoeff]; simp)]
        simp
      _ = _ := by rw [hP, scaleRoots_root_list]
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro hz
    have hc : (Q.map (algebraMap ℤ ℂ)).coeff 0 = 0 := by simp [hz]
    rw [hQC] at hc
    apply root_list_constant_ne_zero (β.map (fun b => (a : ℂ) * b)) ?_ ?_
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      exact mul_ne_zero haC (hβ b hb)
    · simpa only [List.map_map, Function.comp_def] using hc
  refine ⟨a, Q, ha, hQm, hQ0, ?_, ?_, hQC⟩
  · rw [← hQm.natDegree_map (algebraMap ℤ ℚ), hQ, natDegree_scaleRoots, hn]
  · rw [hQ, scaleRoots_change_variable P (a : ℚ) haQ, hn]

/-- A prime larger than the absolute value of a nonzero integer cannot divide it. -/
theorem primes_avoiding_integer (n : ℤ) (hn : n ≠ 0) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ Nat.Prime p ∧ ¬ (p : ℤ) ∣ n := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max B n.natAbs + 1)
  refine ⟨p, lt_of_le_of_lt (le_max_left _ _) (Nat.lt_of_succ_le hp), hprime, ?_⟩
  intro hdiv
  have hle := Int.natAbs_le_of_dvd_ne_zero hdiv hn
  simp only [Int.natAbs_natCast] at hle
  exact (not_le_of_gt (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_of_succ_le hp))) hle

theorem arbitrarily_large_primes : ArbitrarilyLargePrimes := by
  intro k a Q hk ha hQ
  have hn : k * a * Q.coeff 0 ≠ 0 := mul_ne_zero (mul_ne_zero hk.ne' ha.ne') hQ
  exact ⟨hn, primes_avoiding_integer _ hn⟩

end D07.Appendix.LindemannRelationIntegerScaling
