import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.ThreeSquaresRecognition
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch04.TwoSquaresCriterion
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace P203.Ch04
open P203Specs.Ch01 P203Specs.Ch04

/-- Over a prime field of order three modulo four, a zero sum of two squares
has both coordinates zero. -/
theorem eq_zero_of_sq_add_sq_eq_zero (p : ℕ) [Fact p.Prime]
    (hp4 : p % 4 = 3) (x y : ZMod p) (h : x ^ 2 + y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  have hy : y = 0 := by
    by_contra hy
    have hh : x ^ 2 = -y ^ 2 := by linear_combination h
    exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy hh) hp4
  refine ⟨?_, hy⟩
  simpa [hy] using h

/-- A primitive binary norm with nonzero square coefficient cannot vanish
modulo a prime congruent to three modulo four. -/
theorem prime_not_dvd_primitive_norm (p : ℕ) [Fact p.Prime]
    (hp4 : p % 4 = 3) (n u v : ℤ) (hn : IsSquare (n : ZMod p))
    (hn0 : (n : ZMod p) ≠ 0) (huv : Int.gcd u v = 1) :
    ¬ (p : ℤ) ∣ u ^ 2 + n * v ^ 2 := by
  intro hd
  obtain ⟨r, hr⟩ := hn
  have hr0 : r ≠ 0 := by intro he; simp [he] at hr; exact hn0 hr
  have hnorm := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
  push_cast at hnorm
  have hz : (u : ZMod p) ^ 2 + (r * (v : ZMod p)) ^ 2 = 0 := by
    rw [hr] at hnorm
    linear_combination hnorm
  obtain ⟨hu, hv⟩ := eq_zero_of_sq_add_sq_eq_zero p hp4 _ _ hz
  have hv' : (v : ZMod p) = 0 := (mul_eq_zero.mp hv).resolve_left hr0
  have hdu := (ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp hu
  have hdv := (ZMod.intCast_zmod_eq_zero_iff_dvd v p).mp hv'
  have := Int.dvd_gcd hdu hdv
  rw [huv] at this
  exact (Fact.out : p.Prime).not_dvd_one this

/-- Removing a common gcd from the two coordinates shows that this norm has
an even prime valuation, including cases where one coordinate is zero. -/
theorem even_valuation_norm (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3)
    (n W s : ℤ) (hn : IsSquare (n : ZMod p)) (hn0 : (n : ZMod p) ≠ 0)
    (hN : W ^ 2 + n * s ^ 2 ≠ 0) :
    Even ((primeValuation p (W ^ 2 + n * s ^ 2)).toNat) := by
  have hg : 0 < Int.gcd W s := by
    apply Nat.pos_of_ne_zero
    intro hz
    obtain ⟨hW, hs⟩ := Int.gcd_eq_zero_iff.mp hz
    exact hN (by simp [hW, hs])
  obtain ⟨u, v, huv, hW, hs⟩ := Int.exists_gcd_one hg
  have hprimitive := prime_not_dvd_primitive_norm p hp4 n u v hn hn0 huv
  have he : W ^ 2 + n * s ^ 2 =
      (Int.gcd W s : ℤ) ^ 2 * (u ^ 2 + n * v ^ 2) := by
    calc
      _ = (u * (Int.gcd W s : ℤ)) ^ 2 + n * (v * (Int.gcd W s : ℤ)) ^ 2 :=
        congrArg₂ (fun a b : ℤ => a ^ 2 + n * b ^ 2) hW hs
      _ = _ := by ring
  change Even ((emultiplicity (p : ℤ) _).toNat)
  rw [he, emultiplicity_mul (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)),
    emultiplicity_eq_zero.mpr hprimitive, add_zero,
    emultiplicity_pow (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))]
  have hfinite := (Ch01.valuationFactorizationBridge p (Fact.out : p.Prime)
    (Int.gcd W s : ℤ) (by exact_mod_cast hg.ne')).1
  change emultiplicity (p : ℤ) (Int.gcd W s : ℤ) = _ at hfinite
  rw [hfinite, ← ENat.natCast_mul]
  exact even_two_mul _

/-- In the squarefree branch, a common prime divisor of `n` and `S`
forces the coefficient to be a square modulo that prime. -/
theorem coefficient_isSquare_of_prime_dvd (p : ℕ) [Fact p.Prime]
    (n b X W s S : ℤ) (hn : Squarefree n) (hpn : (p : ℤ) ∣ n)
    (hpS : (p : ℤ) ∣ S) (hX : X ^ 2 + S = n)
    (hW : b * S = W ^ 2 + n * s ^ 2) :
    IsSquare (b : ZMod p) := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hdX2 : (p : ℤ) ∣ X ^ 2 := by
    have : X ^ 2 = n - S := by linear_combination hX
    rw [this]
    exact dvd_sub hpn hpS
  have hdX : (p : ℤ) ∣ X := hp.dvd_of_dvd_pow hdX2
  have hdW2 : (p : ℤ) ∣ W ^ 2 := by
    have : W ^ 2 = b * S - n * s ^ 2 := by linear_combination -hW
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right hpS b) (dvd_mul_of_dvd_left hpn _)
  have hdW : (p : ℤ) ∣ W := hp.dvd_of_dvd_pow hdW2
  have hd : (p : ℤ) ^ 2 ∣ n * (b - s ^ 2) := by
    have he : n * (b - s ^ 2) = b * X ^ 2 + W ^ 2 := by
      linear_combination -b * hX + hW
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdX 2) b)
      (pow_dvd_pow_of_dvd hdW 2)
  have hds : (p : ℤ) ∣ b - s ^ 2 := by
    simpa using hn.pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hp hd
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hds
  push_cast at he
  refine ⟨(s : ZMod p), ?_⟩
  linear_combination he

/-- Recognition from the integral output data of the three-dimensional lattice. -/
theorem threeSquaresRecognition : ThreeSquaresRecognition := by
  intro n ℓ q hn hsf hℓ hq hqodd hnq
  dsimp only
  intro hcop hres X W s S hS hSn hX hW
  by_cases hS0 : S = 0
  · exact ⟨0, 0, by simp [hS0]⟩
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
  apply (twoSquaresCriterion S hSpos).mpr
  intro p hp hp4
  let : Fact p.Prime := ⟨hp⟩
  by_cases hpS : (p : ℤ) ∣ S
  · have hp2 : p ≠ 2 := by intro he; subst p; norm_num at hp4
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    by_cases hpn : p ∣ n
    · have hbn := hres p hp hpodd hpn
      have hsquare := coefficient_isSquare_of_prime_dvd p (n : ℤ)
        (2 ^ ℓ * q : ℕ) X W s S (Int.squarefree_natCast.mpr hsf)
        (by exact_mod_cast hpn) hpS hX hW
      obtain ⟨u, hu⟩ := hsquare
      obtain ⟨v, hv⟩ := hbn.1
      have he : u ^ 2 + v ^ 2 = 0 := by
        rw [pow_two, pow_two, ← hu, ← hv]
        simp
      have hz := eq_zero_of_sq_add_sq_eq_zero p hp4 u v he
      apply False.elim
      apply hbn.2
      rw [hv, hz.2, mul_zero]
    · have hpn0 : ((n : ℤ) : ZMod p) ≠ 0 := by
        intro hz
        have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) p).mp hz
        exact hpn (by exact_mod_cast hd)
      have hnSquare : IsSquare ((n : ℤ) : ZMod p) := by
        have hSp := (ZMod.intCast_zmod_eq_zero_iff_dvd S p).mpr hpS
        have hx := congrArg (fun a : ℤ => (a : ZMod p)) hX
        push_cast at hx
        rw [hSp, add_zero] at hx
        exact ⟨(X : ZMod p), by simpa [pow_two] using hx.symm⟩
      have hpq : p < q := by
        have hple : (p : ℤ) ≤ S := Int.le_of_dvd hSpos hpS
        have hqgt : (n : ℤ) < (q : ℤ) := by exact_mod_cast hnq
        exact_mod_cast lt_of_le_of_lt (hple.trans hSn) hqgt
      have hpb : ¬ p ∣ 2 ^ ℓ * q := by
        intro hd
        rcases hp.dvd_mul.mp hd with hd | hd
        · have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow hd
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd2)
        · have he := (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
          omega
      have hpbInt : ¬ (p : ℤ) ∣ ((2 ^ ℓ * q : ℕ) : ℤ) := by
        intro hd
        exact hpb (by exact_mod_cast hd)
      have hprod : ((2 ^ ℓ * q : ℕ) : ℤ) * S ≠ 0 := by
        apply mul_ne_zero _ hS0
        exact_mod_cast (mul_ne_zero (pow_ne_zero ℓ (by decide : (2 : ℕ) ≠ 0)) hq.ne_zero)
      have hEven := even_valuation_norm p hp4 (n : ℤ) W s hnSquare hpn0
        (by rw [← hW]; exact hprod)
      rw [← hW, primeValuation,
        emultiplicity_mul (Nat.prime_iff_prime_int.mp hp),
        emultiplicity_eq_zero.mpr hpbInt, zero_add] at hEven
      exact hEven
  · rw [primeValuation, emultiplicity_eq_zero.mpr hpS]
    exact Even.zero

end P203.Ch04
