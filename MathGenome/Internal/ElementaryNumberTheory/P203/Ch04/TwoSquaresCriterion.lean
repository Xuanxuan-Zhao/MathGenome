import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.TwoSquaresCriterion
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.FactorizationValuations
import Mathlib.NumberTheory.SumTwoSquares

namespace P203.Ch04
open P203Specs.Ch01 P203Specs.Ch04

/-- Taking absolute values of the integer witnesses gives natural witnesses. -/
theorem int_two_squares_iff_nat (n : ℕ) :
    (∃ a b : ℤ, (n : ℤ) = a ^ 2 + b ^ 2) ↔
      ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a.natAbs, b.natAbs, ?_⟩
    have h : (n : ℤ) = (a.natAbs : ℤ) ^ 2 + (b.natAbs : ℤ) ^ 2 := by
      simpa only [Int.natCast_natAbs, sq_abs] using hab
    exact_mod_cast h
  · rintro ⟨a, b, hab⟩
    exact ⟨a, b, by exact_mod_cast hab⟩

/-- The finite canonical valuation agrees with the exponent used by Mathlib's
natural-number two-squares criterion. -/
theorem finite_valuation_eq_padicValNat (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) :
    (primeValuation p (n : ℤ)).toNat = padicValNat p n := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  rw [(Ch01.valuationFactorizationBridge p hp (n : ℤ) hn').1]
  simpa only [Int.natAbs_natCast, ENat.toNat_natCast] using Nat.factorization_def n hp

/-- An absent prime has valuation zero; the all-primes quantifier in the source
therefore imposes no extra condition beyond the prime-factor indexing. -/
theorem finite_valuation_eq_zero_of_not_dvd (n p : ℕ) (hn : n ≠ 0)
    (hp : p.Prime) (h : ¬ p ∣ n) :
    (primeValuation p (n : ℤ)).toNat = 0 := by
  rw [finite_valuation_eq_padicValNat n p hn hp,
    ← Nat.factorization_def n hp, Nat.factorization_eq_zero_of_not_dvd h]

private theorem nat_two_squares_criterion (n : ℕ) (hn : 0 < n) :
    (∃ a b : ℤ, (n : ℤ) = a ^ 2 + b ^ 2) ↔
      ∀ p : ℕ, p.Prime → p % 4 = 3 →
        Even ((primeValuation p (n : ℤ)).toNat) := by
  rw [int_two_squares_iff_nat, Nat.eq_sq_add_sq_iff]
  constructor
  · intro h p hp hp4
    by_cases hd : p ∣ n
    · rw [finite_valuation_eq_padicValNat n p hn.ne' hp]
      exact h p (Nat.mem_primeFactors.mpr ⟨hp, hd, hn.ne'⟩) hp4
    · rw [finite_valuation_eq_zero_of_not_dvd n p hn.ne' hp hd]
      exact Even.zero
  · intro h p hp hp4
    have hprime := Nat.prime_of_mem_primeFactors hp
    rw [← finite_valuation_eq_padicValNat n p hn.ne' hprime]
    exact h p hprime hp4

theorem twoSquaresCriterion : TwoSquaresCriterion := by
  intro n hn
  have he : (n.natAbs : ℤ) = n := (Int.natCast_natAbs n).trans (abs_of_pos hn)
  have hn' : 0 < n.natAbs := Int.natAbs_pos.mpr (ne_of_gt hn)
  simpa only [he] using nat_two_squares_criterion n.natAbs hn'

theorem oddPrimeTwoSquares : OddPrimeTwoSquares := by
  intro p hp hodd
  have hp' : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  rw [twoSquaresCriterion p hp']
  constructor
  · intro h
    have hnot3 : p % 4 ≠ 3 := by
      intro hp4
      have heven := h p hp hp4
      have hval : (primeValuation p (p : ℤ)).toNat = 1 := by
        rw [finite_valuation_eq_padicValNat p p hp.ne_zero hp,
          ← Nat.factorization_def p hp, hp.factorization_self]
      rw [hval] at heven
      exact (by decide : ¬ Even (1 : ℕ)) heven
    have hmod2 := Nat.odd_iff.mp hodd
    omega
  · intro hp4 q hq hq4
    have hne : q ≠ p := by intro hqp; subst q; omega
    have hnd : ¬ q ∣ p := by
      intro hd
      exact hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd)
    rw [finite_valuation_eq_zero_of_not_dvd p q hp.ne_zero hq hnd]
    exact Even.zero

end P203.Ch04
