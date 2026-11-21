import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Bertrand
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

namespace P203.Ch03

/-- For `n ≥ 2`, the upper endpoint in the natural-number version of
Bertrand's postulate cannot be prime. -/
theorem exists_prime_between_nat (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p < 2 * n := by
  obtain ⟨p, hp, hnp, hpn⟩ :=
    Nat.exists_prime_lt_and_le_two_mul n (by omega)
  refine ⟨p, hp, hnp, lt_of_le_of_ne hpn ?_⟩
  intro heq
  have hcomp : ¬ Nat.Prime (2 * n) :=
    Nat.not_prime_mul (by decide) (by omega)
  exact hcomp (heq ▸ hp)

/-- Theorem 3.12 (`nt:C10`, paper.tex): for every real `x > 1`,
there is a prime strictly between `x` and `2 * x`. -/
theorem bertrand : P203Specs.Ch03.bertrand := by
  intro x hx
  by_cases hx2 : x < 2
  · exact ⟨2, Nat.prime_two, by simpa using hx2, by norm_num; linarith⟩
  · have hx2' : (2 : ℝ) ≤ x := le_of_not_gt hx2
    have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx2'
    obtain ⟨p, hp, hnp, hpn⟩ := exists_prime_between_nat ⌊x⌋₊ hn
    refine ⟨p, hp, ?_, ?_⟩
    · have hsucc : (⌊x⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
        exact_mod_cast hnp
      exact (Nat.lt_floor_add_one x).trans_le hsucc
    · have hupper : (p : ℝ) < 2 * (⌊x⌋₊ : ℝ) := by
        exact_mod_cast hpn
      have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      linarith

end P203.Ch03
