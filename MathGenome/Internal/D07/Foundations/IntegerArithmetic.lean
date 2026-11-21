import MathGenome.Internal.Specs.D07.Foundations.IntegerArithmetic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Int.NatAbs

/-! Integer arithmetic foundation: gcd and Bézout, Euclid's lemma, and
unique factorization with positive primes. No project prerequisites are used. -/

namespace D07.Foundations.IntegerArithmetic

/-- The extended integer gcd supplies the required positive generator. -/
theorem positive_gcd_bezout : Specs.PositiveGcdBezout := by
  intro a b hab
  refine ⟨(Int.gcd a b : ℤ), ?_, Int.gcd_dvd_left a b, Int.gcd_dvd_right a b,
    (fun _ ha hb => Int.dvd_coe_gcd ha hb), Int.gcdA a b, Int.gcdB a b, ?_⟩
  · exact Int.natCast_pos.mpr (Int.gcd_pos_iff.mpr hab)
  · simpa only [mul_comm] using Int.gcd_eq_gcd_ab a b

/-- Normalization also covers the zero pair. -/
theorem gcd_zero : Specs.GcdZero := by
  simp [Specs.GcdZero]

/-- Natural absolute values transport divisibility, including negative factors. -/
theorem prime_divides_product : Specs.PrimeDividesProduct := by
  intro p hp a b hab
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_mul] at hab
  exact (hp.2.dvd_mul.mp hab).imp Int.natAbs_dvd_natAbs.mp Int.natAbs_dvd_natAbs.mp

/-- Passing to absolute values loses no data on lists of positive primes. -/
private theorem recover_positive_prime_list (l : List ℤ)
    (hl : ∀ p ∈ l, PositivePrime p) :
    (l.map Int.natAbs).map (fun n : ℕ => (n : ℤ)) = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hp := (hl p List.mem_cons_self).1
    have ht : ∀ q ∈ l, PositivePrime q := fun q hq => hl q (List.mem_cons_of_mem p hq)
    simp only [List.map_cons, Int.natAbs_of_nonneg hp.le, ih ht]

/-- Equality of products of positive prime lists gives a permutation, rather
than merely equality up to integer units. -/
theorem positive_prime_lists_perm {l m : List ℤ}
    (hl : ∀ p ∈ l, PositivePrime p) (hm : ∀ p ∈ m, PositivePrime p)
    (hprod : l.prod = m.prod) : l.Perm m := by
  have hnat : (l.map Int.natAbs).prod = (m.map Int.natAbs).prod := by
    change (l.map Int.natAbsHom).prod = (m.map Int.natAbsHom).prod
    rw [List.prod_hom, List.prod_hom, hprod]
  have hlp : ∀ p ∈ l.map Int.natAbs, Nat.Prime p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (hl q hq).2
  have hmp : ∀ p ∈ m.map Int.natAbs, Nat.Prime p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (hm q hq).2
  have hperm := perm_of_prod_eq_prod hnat
    (fun p hp => Nat.prime_iff.mp (hlp p hp))
    (fun p hp => Nat.prime_iff.mp (hmp p hp))
  have hcast := hperm.map (fun n : ℕ => (n : ℤ))
  simpa only [recover_positive_prime_list l hl, recover_positive_prime_list m hm] using hcast

/-- Cast the natural prime factorization of the positive integer's absolute
value; positivity recovers the original integer exactly. -/
theorem unique_prime_factorization : Specs.UniquePrimeFactorization := by
  intro n hn
  let l := n.natAbs.primeFactorsList.map (fun p : ℕ => (p : ℤ))
  have hl : ∀ p ∈ l, PositivePrime p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hprime := Nat.prime_of_mem_primeFactorsList hq
    exact ⟨Int.natCast_pos.mpr hprime.pos, by simpa only [Int.natAbs_natCast] using hprime⟩
  have hprod : l.prod = n := by
    change (n.natAbs.primeFactorsList.map (Nat.castRingHom ℤ)).prod = n
    rw [List.prod_hom, Nat.prod_primeFactorsList (Int.natAbs_ne_zero.mpr hn.ne')]
    exact Int.natAbs_of_nonneg hn.le
  refine ⟨l, hl, hprod, ?_⟩
  intro m hm hprod'
  exact positive_prime_lists_perm hm hl (hprod'.trans hprod.symm)

/-- No positive-prime list multiplies to zero, and only the empty one
multiplies to one. -/
theorem factorization_boundaries : Specs.FactorizationBoundaries := by
  refine ⟨rfl, ?_⟩
  intro l hl
  constructor
  · constructor
    · intro h
      have hperm : l.Perm [] := positive_prime_lists_perm hl (by simp) (by simpa using h)
      exact List.perm_nil.mp hperm
    · rintro rfl
      rfl
  · apply List.prod_ne_zero
    intro hz
    exact (ne_of_gt (hl 0 hz).1) rfl

end D07.Foundations.IntegerArithmetic
