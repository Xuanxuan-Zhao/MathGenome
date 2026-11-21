import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.InfinitePrimes
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.IntervalCases

namespace P203.Ch01
open P203Specs.Ch01

/-- An integer congruent to 3 modulo 4 has a prime divisor in that class.
Factoring off a prime congruent to 1 leaves a smaller number congruent to 3. -/
theorem exists_prime_three_mod_four_dvd (n : ℕ) (hn : n % 4 = 3) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ p ∣ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨p, hp, k, hk⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    by_cases hp4 : p % 4 = 3
    · exact ⟨p, hp, hp4, ⟨k, hk⟩⟩
    have hk4 : k % 4 = 3 := by
      have hm : (p % 4 * (k % 4)) % 4 = 3 := by
        simpa only [← Nat.mul_mod, ← hk] using hn
      have hpbound := Nat.mod_lt p (by omega : 0 < 4)
      interval_cases hpm : p % 4 <;> simp_all
      omega
    have hklt : k < n := by
      have hkpos : 0 < k := by omega
      rw [hk]
      exact lt_mul_of_one_lt_left hkpos hp.one_lt
    obtain ⟨q, hq, hq4, hqdvd⟩ := ih k hklt hk4
    exact ⟨q, hq, hq4, dvd_trans hqdvd (by rw [hk]; exact dvd_mul_left k p)⟩

/-- A factorial gives a positive product even at the bound zero. -/
theorem exists_prime_three_mod_four_gt (n : ℕ) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ n < p := by
  have hpos := Nat.factorial_pos n
  have hmod : (4 * n.factorial - 1) % 4 = 3 := by omega
  obtain ⟨p, hp, hp4, hpdvd⟩ := exists_prime_three_mod_four_dvd _ hmod
  refine ⟨p, hp, hp4, ?_⟩
  by_contra h
  have hpf : p ∣ n.factorial := Nat.dvd_factorial hp.pos (by omega)
  have hpm : p ∣ 4 * n.factorial := dvd_mul_of_dvd_right hpf 4
  have hsum : (4 * n.factorial - 1) + 1 = 4 * n.factorial := by omega
  have hpone : p ∣ 1 := (Nat.dvd_add_iff_right hpdvd).mpr (by
    rw [hsum]
    exact hpm)
  exact hp.not_dvd_one hpone

theorem infinitelyManyPrimes : InfinitePrimes := by
  refine ⟨Nat.infinite_setOfPred_prime, ?_⟩
  intro s
  exact Nat.infinite_setOfPred_prime.exists_notMem_finset s

theorem infinitelyManyPrimesThreeModFour : InfinitePrimesThreeModFour := by
  have hinf : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨n, hn⟩
    obtain ⟨p, hp, hp4, hnp⟩ := exists_prime_three_mod_four_gt n
    exact (not_le_of_gt hnp) (hn ⟨hp, hp4⟩)
  refine ⟨hinf, ?_⟩
  intro s
  obtain ⟨p, ⟨hp, hp4⟩, hps⟩ := hinf.exists_notMem_finset s
  exact ⟨p, hp, hp4, hps⟩

end P203.Ch01
