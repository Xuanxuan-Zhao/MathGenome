import MathGenome.Internal.Specs.D07.Ch15.RegularPolygonsFermatPrimeArithmetic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.GCD.BigOperators

/-! The arithmetic part of the Gauss–Wantzel criterion. -/

namespace D07.Ch15.RegularPolygonsFermatPrimeArithmetic

open scoped BigOperators
open Specs.D07.Ch15.RegularPolygonsFermatPrimeArithmetic

theorem totient_prime_power : TotientPrimePower := by
  intro p e hp he
  refine ⟨Nat.totient_prime_pow hp he, ?_⟩
  rw [Nat.totient_prime_pow hp he, Nat.mul_sub_left_distrib, mul_one]
  congr 1
  rw [← pow_succ, Nat.sub_add_cancel he]

theorem totient_factorization : TotientFactorization := by
  intro n hn
  exact Nat.totient_eq_prod_factorization hn

/-- Factor the positive exponent into a power of two and an odd number.
The odd-power factorization A+1 ∣ A^u+1 forces the odd number to be 1. -/
theorem prime_two_power_add_one : PrimeTwoPowerAddOne := by
  intro c hc hprime
  obtain ⟨b, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hc.ne'
  rw [pow_mul, add_comm] at hprime
  have hA : 1 < 2 ^ (2 ^ b) := Nat.one_lt_pow (pow_ne_zero b (by decide)) (by decide)
  have hd := hu.nat_add_dvd_pow_add_pow (2 ^ (2 ^ b)) 1
  rw [one_pow, hprime.dvd_iff_eq (by omega : 2 ^ (2 ^ b) + 1 ≠ 1),
    Nat.add_right_cancel_iff, Nat.pow_eq_self_iff hA] at hd
  exact ⟨b, by rw [hd, mul_one]⟩

/-- Every divisor of a power of two is itself a power of two. -/
lemma power_two_of_dvd {d k : ℕ} (h : d ∣ 2 ^ k) : ∃ j : ℕ, d = 2 ^ j := by
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact ⟨j, hj⟩

/-- Odd prime divisors of n must be Fermat primes when φ(n) is a power of two. -/
lemma odd_prime_divisor_fermat {n p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ n) (hn : Nat.totient n = 2 ^ k) :
    Odd p ∧ ∃ b : ℕ, p = 1 + 2 ^ (2 ^ b) := by
  have hd : p - 1 ∣ 2 ^ k := by
    rw [← hn, ← Nat.totient_prime hp]
    exact Nat.totient_dvd_of_dvd hpn
  obtain ⟨c, hc⟩ := power_two_of_dvd hd
  have hpc : p = 1 + 2 ^ c := by
    have := hp.two_le
    omega
  have hcpos : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    simp [this] at hpc
    exact hp2 hpc
  obtain ⟨b, hb⟩ := prime_two_power_add_one c hcpos (hpc ▸ hp)
  exact ⟨hp.odd_of_ne_two hp2, b, by rw [hpc, hb]⟩

/-- A repeated odd prime factor would divide φ(n), hence divide 2. -/
lemma odd_prime_factorization_one {n p k : ℕ} (hn0 : n ≠ 0)
    (hp : p ∈ n.primeFactors) (hp2 : p ≠ 2) (hn : Nat.totient n = 2 ^ k) :
    n.factorization p = 1 := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < n.factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  by_contra he
  have hsq : p ^ 2 ∣ n :=
    (hprime.pow_dvd_iff_le_factorization hn0).mpr (by omega)
  have hd : p ∣ 2 ^ k := by
    rw [← hn]
    apply dvd_trans (b := Nat.totient (p ^ 2))
    · rw [Nat.totient_prime_pow hprime (by decide : 0 < 2)]
      simp
    · exact Nat.totient_dvd_of_dvd hsq
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
    (hprime.dvd_of_dvd_pow hd))

/-- Multiplicativity of φ on a product of distinct primes. -/
lemma totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp := hs p (Finset.mem_insert_self ..)
    have ht : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ s, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hp (ht q hq)).mpr (by
        intro he
        exact hps (he ▸ hq))
    rw [Finset.prod_insert hps, Finset.prod_insert hps, Nat.totient_mul hc,
      Nat.totient_prime hp, ih ht]

/-- Finite products of powers of two are powers of two, including the empty product. -/
lemma prod_power_two (s : Finset ℕ) (f : ℕ → ℕ)
    (h : ∀ p ∈ s, ∃ k : ℕ, f p = 2 ^ k) :
    ∃ k : ℕ, (∏ p ∈ s, f p) = 2 ^ k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, rfl⟩
  | @insert p s hps ih =>
    obtain ⟨j, hj⟩ := h p (Finset.mem_insert_self ..)
    obtain ⟨k, hk⟩ := ih (fun q hq => h q (Finset.mem_insert_of_mem hq))
    exact ⟨j + k, by rw [Finset.prod_insert hps, hj, hk, pow_add]⟩

theorem totient_power_two_iff : TotientPowerTwoIff := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨n.factorization 2, n.primeFactors.erase 2, ?_, ?_⟩
    · have hprod : (∏ p ∈ n.primeFactors.erase 2, p ^ n.factorization p) =
          ∏ p ∈ n.primeFactors.erase 2, p := by
        apply Finset.prod_congr rfl
        intro p hp
        obtain ⟨hp2, hpn⟩ := Finset.mem_erase.mp hp
        rw [odd_prime_factorization_one hn0 hpn hp2 hk, pow_one]
      have hfac := Nat.prod_primeFactors_pow_factorization hn0
      by_cases h2 : 2 ∈ n.primeFactors
      · rw [← Finset.mul_prod_erase _ _ h2, hprod] at hfac
        exact hfac
      · have he : n.factorization 2 = 0 :=
          Finsupp.notMem_support_iff.mp h2
        rw [Finset.erase_eq_of_notMem h2] at hprod
        rw [hprod] at hfac
        simpa [he, Finset.erase_eq_of_notMem h2] using hfac
    · intro p hp
      obtain ⟨hp2, hpn⟩ := Finset.mem_erase.mp hp
      have hprime := Nat.prime_of_mem_primeFactors hpn
      exact ⟨hprime, odd_prime_divisor_fermat hprime hp2
        (Nat.dvd_of_mem_primeFactors hpn) hk⟩
  · rintro ⟨a, s, rfl, hs⟩
    have hsprime : ∀ p ∈ s, p.Prime := fun p hp => (hs p hp).1
    have hcop : (2 ^ a).Coprime (∏ p ∈ s, p) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.prod_right
      intro p hp
      exact (hs p hp).2.1.coprime_two_left
    rw [Nat.totient_mul hcop, totient_prod_primes s hsprime]
    have htwo : Nat.totient (2 ^ a) = 2 ^ (a - 1) := by
      cases a with
      | zero => simp
      | succ a => simp [Nat.totient_prime_pow_succ Nat.prime_two]
    obtain ⟨k, hk⟩ := prod_power_two s (fun p => p - 1) (by
      intro p hp
      obtain ⟨b, hb⟩ := (hs p hp).2.2
      exact ⟨2 ^ b, by rw [hb, Nat.add_sub_cancel_left]⟩)
    exact ⟨a - 1 + k, by rw [htwo, hk, pow_add]⟩

end D07.Ch15.RegularPolygonsFermatPrimeArithmetic
