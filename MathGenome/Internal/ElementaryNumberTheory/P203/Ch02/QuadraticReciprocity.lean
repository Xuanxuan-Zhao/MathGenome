import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.QuadraticReciprocity
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.LegendreGauss
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace P203.Ch02

/-- For odd natural numbers, the two customary half exponents agree. -/
theorem odd_half_eq (n : ℕ) (hn : n % 2 = 1) : (n - 1) / 2 = n / 2 := by
  omega

/-- The mod-eight character is the sign with the source's quotient exponent. -/
theorem chi_eight_eq_source_sign (n : ℕ) (hn : n % 2 = 1) :
    ZMod.χ₈ n = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  have hs : 1 ≤ n ^ 2 := by
    have : 1 ≤ n := by omega
    nlinarith
  have hsq : n ^ 2 % 16 = (n % 16) ^ 2 % 16 := Nat.pow_mod n 2 16
  have hres : n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨
      n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by omega
  rw [ZMod.χ₈_nat_eq_if_mod_eight, neg_one_pow_eq_pow_mod_two]
  rcases hres with h | h | h | h | h | h | h | h
  all_goals
    have hm8 : n % 8 = (n % 16) % 8 := by omega
    have he : (n ^ 2 - 1) / 8 % 2 = ((n % 16) ^ 2 - 1) / 8 % 2 := by
      rw [h] at hsq ⊢
      norm_num at hsq ⊢
      omega
    norm_num [hn, hm8, h, he]

/-- The source's quadratic reciprocity law, without mod-four restrictions. -/
theorem quadratic_reciprocity : P203Specs.Ch02.QuadraticReciprocity := by
  intro p q _ _ hp hq hpq
  change legendreSymbol (q : ℤ) p * legendreSymbol (p : ℤ) q = _
  rw [symbol_eq_mathlib, symbol_eq_mathlib,
    odd_half_eq p ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp),
    odd_half_eq q ((Fact.out : q.Prime).mod_two_eq_one_iff_ne_two.mpr hq)]
  simpa only [mul_comm] using legendreSym.quadratic_reciprocity hp hq hpq

/-- The first supplement for every odd prime. -/
theorem supplement_neg_one : P203Specs.Ch02.SupplementNegOne := by
  intro p _ hp
  change legendreSymbol (-1) p = _
  have ho := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp
  rw [symbol_eq_mathlib, legendreSym.at_neg_one hp,
    ZMod.χ₄_eq_neg_one_pow ho, odd_half_eq p ho]

/-- The second supplement for every odd prime. -/
theorem supplement_two : P203Specs.Ch02.SupplementTwo := by
  intro p _ hp
  change legendreSymbol 2 p = _
  rw [symbol_eq_mathlib, legendreSym.at_two hp]
  exact chi_eight_eq_source_sign p
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp)

end P203.Ch02
