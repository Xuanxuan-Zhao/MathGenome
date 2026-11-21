import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.FactorialValuations
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.FactorizationValuations
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.ModEq

/-!
Legendre's formula and its binomial consequences, `paper.tex`, Theorem 1.5.

The factorial proof transfers Mathlib's multiplicity formula through the
integer/natural multiplicity bridge. For positive `n`, `n < p^b` is equivalent
to Mathlib's cutoff `log p n < b`; `n = 0` is proved directly, even for `b = 0`.
The binomial proof applies finite valuation additivity to
`n! = choose n k * k! * (n-k)!` and subtracts the two factorial sums in `ℤ`.
The floor difference lies between zero and one by the two division inequalities
for `k + (n-k)`. Quotients vanish whenever their denominator exceeds `n`.
-/
namespace P203.Ch01
open P203Specs.Ch01

/-- Connect Mathlib's natural multiplicity with the canonical integer valuation. -/
theorem primeValuation_natCast (p n : ℕ) :
    primeValuation p (n : ℤ) = emultiplicity p n := by
  exact Int.natCast_emultiplicity p n

theorem factorialValuationFormula : FactorialValuationFormula := by
  intro p hp n b hb
  refine ⟨(valuationFactorizationBridge p hp _ (by exact_mod_cast Nat.factorial_ne_zero n)).2, ?_⟩
  by_cases hn : n = 0
  · subst n
    simp [Nat.factorial_zero, (valuationZeroAndUnits p hp).2.1]
  · rw [primeValuation_natCast, hp.emultiplicity_factorial
      ((Nat.log_lt_iff_lt_pow hp.one_lt hn).mpr hb)]
    rfl

theorem binomialFloorDifferenceZeroOrOne : BinomialFloorDifferenceZeroOrOne := by
  intro p hp n k hk j
  have hsum : k + (n - k) = n := Nat.add_sub_of_le hk
  have hlo := Nat.div_add_div_le_add_div (x := k) (y := n - k) (z := p ^ j)
  have hhi := Nat.add_div_le_div_add_div_add_one k (n - k) (p ^ j)
  rw [hsum] at hlo hhi
  unfold binomialFloorDifference
  omega

theorem valuationSumCutoff : ValuationSumCutoff := by
  intro p hp n
  refine ⟨⟨Nat.log p n + 1, Nat.lt_pow_succ_log_self hp.one_lt n⟩, ?_⟩
  intro j hj
  refine ⟨Nat.div_eq_of_lt hj, ?_⟩
  intro k hk
  simp [binomialFloorDifference, Nat.div_eq_of_lt hj,
    Nat.div_eq_of_lt (lt_of_le_of_lt hk hj),
    Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.sub_le n k) hj)]

theorem binomialValuationFormula : BinomialValuationFormula := by
  intro p hp n k hk b hb
  have hc : (n.choose k : ℤ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hk
  have hf : (k.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hg : ((n - k).factorial : ℤ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  refine ⟨(valuationFactorizationBridge p hp _ hc).2, ?_⟩
  have hid : (n.factorial : ℤ) =
      (n.choose k : ℤ) * (k.factorial : ℤ) * ((n - k).factorial : ℤ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk).symm
  have hmul := (finiteValuationArithmetic
    ((n.choose k : ℤ) * (k.factorial : ℤ)) ((n - k).factorial : ℤ)
    (mul_ne_zero hc hf) hg).1 p hp
  rw [← hid, (finiteValuationArithmetic _ _ hc hf).1 p hp] at hmul
  rw [(factorialValuationFormula p hp n b hb).2,
    (factorialValuationFormula p hp k b (lt_of_le_of_lt hk hb)).2,
    (factorialValuationFormula p hp (n - k) b
      (lt_of_le_of_lt (Nat.sub_le n k) hb)).2] at hmul
  have hcast := congrArg (fun a : ℕ => (a : ℤ)) hmul
  simp only [Nat.cast_add] at hcast
  simp only [binomialFloorDifference, Finset.sum_sub_distrib, ← Nat.cast_sum]
  omega

end P203.Ch01
