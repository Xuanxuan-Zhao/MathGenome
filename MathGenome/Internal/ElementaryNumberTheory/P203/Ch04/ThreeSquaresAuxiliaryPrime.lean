import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.ThreeSquaresAuxiliaryPrime
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.CompatibleCRT
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.JacobiRules
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch04.DirichletPrimes
import Mathlib.Tactic.Ring

namespace P203.Ch04
open P203Specs.Ch04

/-- The decomposition and the five rows of the source's sign table. -/
theorem auxiliary_cases (n : ℕ) (hn : ThreeSquaresResidue n) :
    ∃ k m ell c : ℕ, Odd m ∧ n = 2 ^ k * m ∧
      AuxiliaryCase n k m ell c := by
  rcases hn with h | h | h | h | h
  · exact ⟨0, n, 0, 1, Nat.odd_iff.mpr (by omega), by simp,
      Or.inl ⟨h, rfl, by omega, rfl, rfl⟩⟩
  · refine ⟨1, n / 2, 0, 1, Nat.odd_iff.mpr (by omega), ?_, Or.inr (Or.inl ?_)⟩
    · simp only [pow_one]; omega
    · exact ⟨h, rfl, by omega, rfl, rfl⟩
  · exact ⟨0, n, 1, 1, Nat.odd_iff.mpr (by omega), by simp,
      Or.inr (Or.inr (Or.inl ⟨h, rfl, h, rfl, rfl⟩))⟩
  · exact ⟨0, n, 0, 1, Nat.odd_iff.mpr (by omega), by simp,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl, by omega, rfl, rfl⟩)))⟩
  · refine ⟨1, n / 2, 0, 5, Nat.odd_iff.mpr (by omega), ?_,
      Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    · simp only [pow_one]; omega
    · exact ⟨h, rfl, by omega, rfl, rfl⟩

/-- A multiplicative inverse modulo m gives a Bézout identity. -/
theorem coprime_of_mul_modEq_one (a t m : ℤ) (h : t * a ≡ 1 [ZMOD m]) :
    IsCoprime a m := by
  obtain ⟨z, hz⟩ := h.dvd
  exact ⟨t, z, by linear_combination -hz⟩

/-- A reduced class modulo 8m with the stronger choice -2^ell*a = 1 modulo m.
The construction includes m=1. -/
theorem auxiliary_reduced_class (m ell c : ℕ) (hm : Odd m) (hc : c = 1 ∨ c = 5) :
    ∃ a : ℤ, Int.gcd a ((8 * m : ℕ) : ℤ) = 1 ∧
      a ≡ (c : ℤ) [ZMOD 8] ∧ -(2 : ℤ) ^ ell * a ≡ 1 [ZMOD (m : ℤ)] := by
  have hmZ : Odd (m : ℤ) := by exact_mod_cast hm
  have h2 : IsCoprime (2 : ℤ) m := hmZ.isCoprime_two.symm
  have h8 : IsCoprime (8 : ℤ) m := by
    convert (h2.pow_left (m := 3)) using 1; norm_num
  obtain ⟨r, s, hrs⟩ := h2.pow_left (m := ell)
  have hr : -(2 : ℤ) ^ ell * (-r) ≡ 1 [ZMOD (m : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨s, by linear_combination -hrs⟩
  obtain ⟨a, ha8, ham⟩ := P203.Ch01.compatibleCRT_pair 8 m c (-r) (by
    rw [Int.isCoprime_iff_gcd_eq_one.mp h8]
    simp)
  have ha8' : a ≡ (c : ℤ) [ZMOD 8] := (Int.modEq_iff_dvd.mpr ha8).symm
  have ham' : a ≡ -r [ZMOD (m : ℤ)] := (Int.modEq_iff_dvd.mpr ham).symm
  have haodd := (ham'.mul_left (-(2 : ℤ) ^ ell)).trans hr
  have ha2 : a ≡ 1 [ZMOD 2] := by
    apply (ha8'.of_dvd (by norm_num : (2 : ℤ) ∣ 8)).trans
    rcases hc with rfl | rfl <;> decide
  have hca2 : IsCoprime a 2 := coprime_of_mul_modEq_one a 1 2 (by simpa using ha2)
  have hca8 : IsCoprime a 8 := by
    convert (hca2.pow_right (n := 3)) using 1; norm_num
  have hcam := coprime_of_mul_modEq_one a (-(2 : ℤ) ^ ell) m haodd
  refine ⟨a, ?_, ha8', haodd⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    Int.isCoprime_iff_gcd_eq_one.mp (hca8.mul_right hcam)

/-- Dirichlet chooses the prime in that reduced class, above n. -/
theorem auxiliary_prime_in_class (n m ell c : ℕ) (hm : Odd m) (hc : c = 1 ∨ c = 5) :
    ∃ (a : ℤ) (q : ℕ), Int.gcd a ((8 * m : ℕ) : ℤ) = 1 ∧
      a ≡ (c : ℤ) [ZMOD 8] ∧ -(2 : ℤ) ^ ell * a ≡ 1 [ZMOD (m : ℤ)] ∧
      q.Prime ∧ n < q ∧ (q : ℤ) ≡ a [ZMOD ((8 * m : ℕ) : ℤ)] ∧
      q % 8 = c % 8 ∧ -(2 : ℤ) ^ ell * q ≡ 1 [ZMOD (m : ℤ)] := by
  obtain ⟨a, ha, ha8, ham⟩ := auxiliary_reduced_class m ell c hm hc
  obtain ⟨q, _, hq, hqn, hqa⟩ := dirichletPrimes (8 * m) (by have := hm.pos; omega)
    a ha (n : ℝ)
  have hqa' : (q : ℤ) ≡ a [ZMOD ((8 * m : ℕ) : ℤ)] :=
    (Int.modEq_iff_dvd.mpr hqa).symm
  have hq8 := (hqa'.of_dvd (by exact_mod_cast (dvd_mul_right 8 m))).trans ha8
  have hqm := hqa'.of_dvd (show (m : ℤ) ∣ ((8 * m : ℕ) : ℤ) by exact_mod_cast (dvd_mul_left m 8))
  refine ⟨a, q, ha, ha8, ham, hq, by exact_mod_cast hqn, hqa', ?_, ?_⟩
  · exact_mod_cast hq8
  · exact (hqm.mul_left (-(2 : ℤ) ^ ell)).trans ham

/-- The inverse notation in the source agrees with the integer congruence. -/
theorem auxiliaryInverseCongruence : AuxiliaryInverseCongruence := by
  intro n b v hb
  obtain ⟨r, s, hrs⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hb
  have hu : IsUnit (b : ZMod n) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨(r : ZMod n), ?_⟩
    have h := congrArg (fun x : ℤ => (x : ZMod n)) hrs
    simpa [mul_comm] using h
  have hi := ZMod.inv_mul_of_unit (b : ZMod n) hu
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  constructor
  · intro h
    have hh := congrArg (fun x : ZMod n => (b : ZMod n)⁻¹ * x) h
    simpa only [← mul_assoc, hi, one_mul, mul_neg_one] using hh
  · intro h
    rw [h, mul_neg, ZMod.mul_inv_of_unit (b : ZMod n) hu]

/-- The complete five-case sign calculation, using the standard quadratic
characters. In particular the Jacobi side also applies when m=1. -/
theorem auxiliary_signs (n k m ell c q : ℕ) (hm : Odd m)
    (hc : AuxiliaryCase n k m ell c) (hq8 : q % 8 = c) :
    q % 4 = 1 ∧
    jacobiSym (-((2 : ℤ) ^ k)) q = (-1 : ℤ) ^ (k * ((m - 1) / 2)) ∧
    jacobiSym (-((2 : ℤ) ^ ell)) m = (-1 : ℤ) ^ (k * ((m - 1) / 2)) := by
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  have hs : (-1 : ℤ) ^ (k * ((m - 1) / 2)) = (ZMod.χ₄ m) ^ k := by
    rw [Nat.mul_comm k, pow_mul, P203.Ch02.odd_half_eq m hm2,
      ← ZMod.χ₄_eq_neg_one_pow hm2]
  rw [hs]
  rcases hc with ⟨hn, rfl, hm4, rfl, rfl⟩ | ⟨hn, rfl, hm4, rfl, rfl⟩ |
    ⟨hn, rfl, hm8, rfl, rfl⟩ | ⟨hn, rfl, hm4, rfl, rfl⟩ |
    ⟨hn, rfl, hm4, rfl, rfl⟩
  all_goals
    have hq2 : q % 2 = 1 := by omega
    have hq4 : q % 4 = 1 := by omega
    have hqo : Odd q := Nat.odd_iff.mpr hq2
    refine ⟨hq4, ?_, ?_⟩
    all_goals simp only [pow_zero, pow_one]
    all_goals first
      | rw [jacobiSym.at_neg_one hqo]
      | rw [jacobiSym.at_neg_two hqo]
      | rw [jacobiSym.at_neg_one hm]
      | rw [jacobiSym.at_neg_two hm]
    all_goals simp only [ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₈'_nat_eq_if_mod_eight]
    all_goals simp_all only [Nat.one_ne_zero, ite_false, ite_true, or_true, true_or]
    all_goals norm_num

/-- Reciprocity converts the chosen class into a square modulo q. -/
theorem auxiliary_reciprocity (n k m ell q : ℕ) (hm : Odd m)
    (hn : n = 2 ^ k * m) (hq4 : q % 4 = 1)
    (hclass : -(2 : ℤ) ^ ell * q ≡ 1 [ZMOD (m : ℤ)])
    (hs : jacobiSym (-((2 : ℤ) ^ k)) q = jacobiSym (-((2 : ℤ) ^ ell)) m) :
    jacobiSym (-(n : ℤ)) q = 1 := by
  have hprod : jacobiSym (-((2 : ℤ) ^ ell)) m * jacobiSym (q : ℤ) m = 1 := by
    rw [← jacobiSym.mul_left, jacobiSym.mod_left' hclass, jacobiSym.one_left]
  have hrec : jacobiSym (m : ℤ) q = jacobiSym (q : ℤ) m :=
    jacobiSym.quadratic_reciprocity_one_mod_four' hm hq4
  rw [hn, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    neg_mul_eq_neg_mul, jacobiSym.mul_left, hs, hrec]
  exact hprod

/-- With the stronger residue choice, b0 is -1 modulo all of n. -/
theorem auxiliary_b0_mod (n k m ell q : ℕ) (hm : Odd m) (hk : k ≤ 1)
    (hn : n = 2 ^ k * m) (he : k = 1 → ell = 0) (hq2 : q % 2 = 1)
    (hclass : -(2 : ℤ) ^ ell * q ≡ 1 [ZMOD (m : ℤ)]) :
    (2 : ℤ) ^ ell * q ≡ -1 [ZMOD (n : ℤ)] := by
  have hqm : (2 : ℤ) ^ ell * q ≡ -1 [ZMOD (m : ℤ)] := by
    simpa only [neg_mul, neg_neg] using hclass.neg
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · simpa [hn] using hqm
  · have hell : ell = 0 := he rfl
    subst ell
    simp only [pow_zero, one_mul] at hqm ⊢
    have hq : (q : ℤ) ≡ -1 [ZMOD 2] := by
      change (q : ℤ) % 2 = (-1 : ℤ) % 2
      norm_num
      exact_mod_cast hq2
    have hmZ : Odd (m : ℤ) := by exact_mod_cast hm
    apply Int.modEq_iff_dvd.mpr
    have hd := hmZ.isCoprime_two.symm.mul_dvd hq.dvd hqm.dvd
    simpa [hn] using hd

/-- The root modulo q lifts to the modulus 4^ell*q required by the lattice. -/
theorem auxiliary_root (n ell q : ℕ) [Fact q.Prime]
    (hq2 : q % 2 = 1) (he : ell = 0 ∨ ell = 1 ∧ n % 4 = 3)
    (hs : jacobiSym (-(n : ℤ)) q = 1) :
    ∃ u : ℤ, u ^ 2 ≡ -(n : ℤ) [ZMOD ((4 : ℤ) ^ ell * q)] := by
  obtain ⟨x, hx⟩ := (P203.Ch02.square_congruence_iff q (-(n : ℤ))).mpr
    (ZMod.isSquare_of_jacobiSym_eq_one hs)
  rcases he with rfl | ⟨rfl, hn4⟩
  · exact ⟨x, by simpa using hx⟩
  · have hqZ : Odd (q : ℤ) := by exact_mod_cast (Nat.odd_iff.mpr hq2)
    have h4q : IsCoprime (4 : ℤ) q := by
      convert (hqZ.isCoprime_two.symm.pow_left (m := 2)) using 1; norm_num
    obtain ⟨u, hu4, huq⟩ := P203.Ch01.compatibleCRT_pair 4 q 1 x (by
      rw [Int.isCoprime_iff_gcd_eq_one.mp h4q]; simp)
    have hu4' : u ≡ 1 [ZMOD 4] := (Int.modEq_iff_dvd.mpr hu4).symm
    have huq' : u ≡ x [ZMOD (q : ℤ)] := (Int.modEq_iff_dvd.mpr huq).symm
    have hn4' : (1 : ℤ) ≡ -(n : ℤ) [ZMOD 4] := by
      change (1 : ℤ) % 4 = (-(n : ℤ)) % 4
      have hn4Z : (n : ℤ) % 4 = 3 := by exact_mod_cast hn4
      omega
    have h4 : u ^ 2 ≡ -(n : ℤ) [ZMOD 4] :=
      (by simpa using hu4'.pow 2 : u ^ 2 ≡ 1 [ZMOD 4]).trans hn4'
    have hq : u ^ 2 ≡ -(n : ℤ) [ZMOD (q : ℤ)] := (huq'.pow 2).trans hx
    refine ⟨u, Int.modEq_iff_dvd.mpr ?_⟩
    simpa only [pow_one] using h4q.mul_dvd h4.dvd hq.dvd

/-- Arithmetic consequences of the five rows used in assembling the witnesses. -/
theorem auxiliary_case_properties (n k m ell c : ℕ) (hc : AuxiliaryCase n k m ell c) :
    k ≤ 1 ∧ ell = (if n % 8 = 3 then 1 else 0) ∧
    c = (if n % 8 = 6 then 5 else 1) ∧ (c = 1 ∨ c = 5) ∧
    (k = 1 → ell = 0) ∧ (ell = 0 ∨ ell = 1 ∧ n % 4 = 3) := by
  rcases hc with ⟨hn, rfl, hm, rfl, rfl⟩ | ⟨hn, rfl, hm, rfl, rfl⟩ |
    ⟨hn, rfl, hm, rfl, rfl⟩ | ⟨hn, rfl, hm, rfl, rfl⟩ |
    ⟨hn, rfl, hm, rfl, rfl⟩
  all_goals simp_all
  all_goals omega

/-- All required auxiliary data for the Ankeny proof. The stronger CRT choice
makes v=1 work; squarefreeness is therefore not needed for this construction. -/
theorem threeSquaresAuxiliaryPrime : ThreeSquaresAuxiliaryPrime := by
  intro n _hsf _hn hres
  obtain ⟨k, m, ell, c, hm, hnm, hc⟩ := auxiliary_cases n hres
  obtain ⟨hk, hell, hcval, hc15, he, hroot⟩ := auxiliary_case_properties n k m ell c hc
  obtain ⟨a, q, ha, ha8, ham, hq, hnq, hqa, hq8, hqm⟩ :=
    auxiliary_prime_in_class n m ell c hm hc15
  have hc8 : c % 8 = c := by rcases hc15 with rfl | rfl <;> decide
  rw [hc8] at hq8
  obtain ⟨hq4, hsq, hsm⟩ := auxiliary_signs n k m ell c q hm hc hq8
  have hq2 : q % 2 = 1 := by omega
  have hrec := auxiliary_reciprocity n k m ell q hm hnm hq4 hqm (hsq.trans hsm.symm)
  have hb := auxiliary_b0_mod n k m ell q hm hk hnm he hq2 hqm
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨u, hu⟩ := auxiliary_root n ell q hq2 hroot hrec
  have hbcp : Int.gcd ((2 : ℤ) ^ ell * q) n = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    apply coprime_of_mul_modEq_one _ (-1) _
    simpa only [neg_one_mul, neg_neg] using hb.neg
  refine ⟨k, m, ell, q, a, u, 1, {
    k_le := hk
    odd_m := hm
    decomposition := hnm
    ell_eq := hell
    prime := hq
    gt := hnq
    residue := hq8.trans hcval
    reduced_class := ha
    prime_class := hqa
    class_eight := ?_
    class_odd := ham
    local_squares := ?_
    mod_four := hq4
    sign_q := ?_
    sign_m := hsm
    reciprocity := ?_
    coprime := hbcp
    root_u := hu
    root_v := ?_
  }⟩
  · simpa only [hcval, Nat.cast_ite, Nat.cast_ofNat, Nat.cast_one] using ha8
  · intro p hp _ hpm
    have hloc : -((2 : ℤ) ^ ell * q) ≡ 1 [ZMOD (p : ℤ)] := by
      simpa only [neg_mul] using hqm.of_dvd (show (p : ℤ) ∣ (m : ℤ) by exact_mod_cast hpm)
    refine ⟨?_, 1, by simpa only [one_pow] using hloc.symm⟩
    intro hd
    have hp1 : (p : ℤ) ∣ 1 := by
      convert dvd_add hd hloc.dvd using 1; ring
    exact hp.not_dvd_one (by exact_mod_cast hp1)
  · change P203.Ch02.legendreSymbol _ q = _
    rw [P203.Ch02.symbol_eq_mathlib, jacobiSym.legendreSym.to_jacobiSym]
    exact hsq
  · change P203.Ch02.legendreSymbol _ q = _
    rw [P203.Ch02.symbol_eq_mathlib, jacobiSym.legendreSym.to_jacobiSym]
    exact hrec
  · simpa only [one_pow, mul_one] using hb

end P203.Ch04
