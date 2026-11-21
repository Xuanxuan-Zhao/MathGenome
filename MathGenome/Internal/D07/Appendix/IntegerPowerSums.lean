import MathGenome.Internal.Specs.D07.Appendix.IntegerPowerSums
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-! Integer power sums, including empty lists and roots with multiplicity. -/

noncomputable section
namespace D07.Appendix.IntegerPowerSums

open Polynomial
open Specs.D07.Appendix.IntegerPowerSums

/-- Vieta identifies elementary symmetric sums with signed integer coefficients. -/
lemma elementary_mem_integer_range (m : ℕ) (γ : Fin m → ℂ) (Q : Polynomial ℤ)
    (hQ : Q.map (Int.castRingHom ℂ) = ∏ j, (X - C (γ j))) (j : ℕ) :
    MvPolynomial.aeval γ (MvPolynomial.esymm (Fin m) ℤ j) ∈
      (Int.castRingHom ℂ).range := by
  classical
  by_cases hj : j ≤ m
  · let s : Multiset ℂ := Finset.univ.val.map γ
    have hs : s.card = m := by simp [s]
    have hp : (s.map fun t => X - C t).prod = Q.map (Int.castRingHom ℂ) := by
      rw [hQ, Finset.prod_eq_multiset_prod]
      simp only [s, Multiset.map_map, Function.comp_def]
    have hc := Multiset.prod_X_sub_C_coeff s (k := m - j) (by omega)
    rw [hp, Polynomial.coeff_map, hs, Nat.sub_sub_self hj] at hc
    change (Q.coeff (m - j) : ℂ) = (-1) ^ j * s.esymm j at hc
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    refine ⟨(-1) ^ j * Q.coeff (m - j), ?_⟩
    change (((-1) ^ j * Q.coeff (m - j) : ℤ) : ℂ) = s.esymm j
    push_cast
    rw [hc, ← mul_assoc, ← pow_add]
    simp [← two_mul, pow_mul]
  · have hz : MvPolynomial.esymm (Fin m) ℤ j = 0 := by
      have he : (Finset.univ : Finset (Fin m)).powersetCard j = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simpa using Nat.lt_of_not_ge hj)
      simp [MvPolynomial.esymm, he]
    simp [hz]

/-- Newton's recurrence uses only integer ring operations, including at orders
larger than the number of roots. -/
theorem power_sums_integral : PowerSumsIntegral := by
  intro m γ Q hQ r
  classical
  have hp (k : ℕ) :
      MvPolynomial.aeval γ (MvPolynomial.psum (Fin m) ℤ k) ∈
        (Int.castRingHom ℂ).range := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk : k = 0
      · subst k
        simp
      · have he := congrArg (MvPolynomial.aeval γ)
          (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin m) ℤ k (Nat.pos_of_ne_zero hk))
        simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum] at he
        rw [he]
        apply Subring.sub_mem
        · apply Subring.mul_mem
          · exact Subring.mul_mem _
              (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
              (natCast_mem (Int.castRingHom ℂ).range k)
          · exact elementary_mem_integer_range m γ Q hQ k
        · apply Subring.sum_mem
          intro a ha
          have ha' := Finset.mem_filter.mp ha
          have ha'' := Finset.mem_antidiagonal.mp ha'.1
          have hapos : 0 < a.1 := ha'.2.1
          apply Subring.mul_mem
          · exact Subring.mul_mem _
              (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
              (elementary_mem_integer_range m γ Q hQ a.1)
          · exact ih a.2 (by omega)
  obtain ⟨z, hz⟩ := hp r
  refine ⟨z, ?_⟩
  simpa [MvPolynomial.psum] using hz.symm

/-- Expand an integer polynomial in monomials and sum over the root list. -/
theorem polynomial_sums_integral : PolynomialSumsIntegral := by
  intro m γ Q hQ A
  classical
  have hA : (∑ j, A.eval₂ (Int.castRingHom ℂ) (γ j)) ∈
      (Int.castRingHom ℂ).range := by
    induction A using Polynomial.induction_on' with
    | add A B hA hB =>
      simpa only [Polynomial.eval₂_add, Finset.sum_add_distrib] using
        (Int.castRingHom ℂ).range.add_mem hA hB
    | monomial k a =>
      have hp : (∑ j, γ j ^ k) ∈ (Int.castRingHom ℂ).range := by
        obtain ⟨z, hz⟩ := power_sums_integral m γ Q hQ k
        exact ⟨z, hz.symm⟩
      simpa only [Polynomial.eval₂_monomial, ← Finset.mul_sum] using
        (Int.castRingHom ℂ).range.mul_mem
          (show (Int.castRingHom ℂ) a ∈ (Int.castRingHom ℂ).range from ⟨a, rfl⟩) hp
  obtain ⟨z, hz⟩ := hA
  exact ⟨z, hz.symm⟩

end D07.Appendix.IntegerPowerSums
