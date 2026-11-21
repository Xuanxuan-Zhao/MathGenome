import MathGenome.Internal.Specs.D07.Ch13.IrreducibilityTest
import MathGenome.Internal.D07.Ch13.UniversalFactorization
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! The irreducibility test of K07.13.irreducibility_test.
Choose an irreducible divisor of f. Its degree divides n by the universal
splitting-polynomial theorem. A proper divisor of n divides n / ℓ for
some prime ℓ ∣ n, which contradicts the gcd test. Thus the divisor has
the full degree of f and is associated to f.
-/

universe u
namespace D07.Ch13.IrreducibilityTest

open Polynomial
open Specs.D07.Ch13.IrreducibilityTest

/-- Every proper divisor of a positive n is contained in one of the
maximal proper divisors n / ℓ, with ℓ prime. -/
lemma exists_prime_quotient_multiple {d n : ℕ} (hdn : d ∣ n) (hlt : d < n) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ n ∧ d ∣ n / ℓ := by
  obtain ⟨k, hk⟩ := hdn
  have hk1 : k ≠ 1 := by
    intro h
    simp only [h, mul_one] at hk
    omega
  obtain ⟨ℓ, hprime, hℓk⟩ := Nat.exists_prime_and_dvd hk1
  have hℓn : ℓ ∣ n := hk ▸ dvd_mul_of_dvd_right hℓk d
  refine ⟨ℓ, hprime, hℓn, (Nat.dvd_div_iff_mul_dvd hℓn).mpr ?_⟩
  rw [hk]
  simpa only [Nat.mul_comm ℓ d] using Nat.mul_dvd_mul_left d hℓk

theorem irreducibility_criterion : IrreducibilityCriterion.{u} := by
  classical
  intro K _ _ q n hq hn f hf hdegree
  have hdiv (m : ℕ) (hm : 1 ≤ m) (g : K[X]) (hg : Irreducible g) :
      g ∣ X ^ (q ^ m) - X ↔ g.natDegree ∣ m :=
    UniversalFactorization.irreducible_divisibility K q m hq hm g hg
  have hcong : (X ^ (q ^ n) : K[X]) % f = X % f ↔
      f ∣ X ^ (q ^ n) - X := by
    rw [← EuclideanDomain.mod_eq_zero, Polynomial.sub_mod, sub_eq_zero]
  rw [hcong]
  constructor
  · intro hi
    refine ⟨(hdiv n hn f hi).mpr (hdegree ▸ dvd_rfl), ?_⟩
    intro ℓ hprime hℓn
    apply hi.gcd_eq_one_iff.mpr
    intro hbad
    have hmpos : 1 ≤ n / ℓ := Nat.div_pos (Nat.le_of_dvd hn hℓn) hprime.pos
    have hdvd := (hdiv (n / ℓ) hmpos f hi).mp hbad
    rw [hdegree] at hdvd
    exact (not_le_of_gt (Nat.div_lt_self hn hprime.one_lt))
      (Nat.le_of_dvd hmpos hdvd)
  · rintro ⟨hfn, hcoprime⟩
    obtain ⟨g, hgi, hgf⟩ := exists_irreducible_of_natDegree_pos
      (f := f) (hdegree ▸ hn)
    have hgn : g.natDegree ∣ n := (hdiv n hn g hgi).mp (hgf.trans hfn)
    have hle : g.natDegree ≤ n := Nat.le_of_dvd hn hgn
    have heq : g.natDegree = n := by
      by_contra hne
      obtain ⟨ℓ, hprime, hℓn, hdℓ⟩ :=
        exists_prime_quotient_multiple hgn (lt_of_le_of_ne hle hne)
      have hmpos : 1 ≤ n / ℓ := Nat.div_pos (Nat.le_of_dvd hn hℓn) hprime.pos
      have hgℓ := (hdiv (n / ℓ) hmpos g hgi).mpr hdℓ
      have hunit : g ∣ (1 : K[X]) := by
        rw [← hcoprime ℓ hprime hℓn]
        exact dvd_gcd hgf hgℓ
      exact hgi.not_isUnit (isUnit_of_dvd_one hunit)
    exact (associated_of_dvd_of_natDegree_le hgf hf.ne_zero
      (by rw [hdegree, heq])).irreducible hgi

end D07.Ch13.IrreducibilityTest
