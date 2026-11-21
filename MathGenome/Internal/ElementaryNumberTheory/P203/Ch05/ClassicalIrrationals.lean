import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.ClassicalIrrationals
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Finset

namespace P203.Ch05

private lemma factorial_sum_integral (n : ℕ) :
    (n.factorial : ℝ) * (∑ i ∈ range (n + 1), (1 : ℝ) / i.factorial) =
      ((∑ i ∈ range (n + 1), n.factorial / i.factorial : ℕ) : ℝ) := by
  rw [mul_sum, Nat.cast_sum]
  apply sum_congr rfl
  intro i hi
  rw [Nat.cast_div (Nat.factorial_dvd_factorial (by simpa using mem_range.mp hi))
    (by positivity : (i.factorial : ℝ) ≠ 0)]
  ring

private lemma factorial_remainder_pos (n : ℕ) :
    0 < Real.exp 1 - ∑ i ∈ range (n + 1), (1 : ℝ) / i.factorial := by
  have h := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) (n + 2)
  simp only [one_pow] at h
  rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ] at h
  have : (0 : ℝ) < 1 / (n + 1).factorial := by positivity
  linarith

private lemma factorial_remainder_lt_one (n : ℕ) (hn : 2 ≤ n) :
    (n.factorial : ℝ) *
      (Real.exp 1 - ∑ i ∈ range (n + 1), (1 : ℝ) / i.factorial) < 1 := by
  have h := Real.exp_bound' (x := 1) (by norm_num) (by norm_num)
    (n := n + 1) (by omega)
  simp only [one_pow, one_mul] at h
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    (n.factorial : ℝ) *
        (Real.exp 1 - ∑ i ∈ range (n + 1), (1 : ℝ) / i.factorial) ≤
        (n.factorial : ℝ) *
          ((((n + 1 : ℕ) : ℝ) + 1) / ((n + 1).factorial * (n + 1))) := by
      apply mul_le_mul_of_nonneg_left _ hf.le
      apply sub_le_iff_le_add'.mpr
      simpa only [Nat.cast_add, Nat.cast_one] using h
    _ = ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    _ < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)

/-- The exponential at 1 is irrational, by the integer factorial remainder. -/
theorem irrational_exp_one : Irrational (Real.exp 1) := by
  rintro ⟨q, hq⟩
  let n := max q.den 2
  have hn : 2 ≤ n := le_max_right _ _
  have hd : q.den ∣ n.factorial := Nat.dvd_factorial q.pos (le_max_left _ _)
  obtain ⟨k, hk⟩ := hd
  have he : (n.factorial : ℝ) * Real.exp 1 = ((k : ℤ) * q.num : ℤ) := by
    rw [← hq, Rat.cast_def, hk]
    push_cast
    field_simp
  let z : ℤ := (k : ℤ) * q.num -
    (∑ i ∈ range (n + 1), n.factorial / i.factorial : ℕ)
  have hz : (z : ℝ) = (n.factorial : ℝ) *
      (Real.exp 1 - ∑ i ∈ range (n + 1), (1 : ℝ) / i.factorial) := by
    dsimp [z]
    push_cast
    rw [mul_sub, he, factorial_sum_integral]
    push_cast
    rfl
  have hz0 : (0 : ℝ) < z := by
    rw [hz]
    exact mul_pos (by positivity) (factorial_remainder_pos n)
  have hz1 : (z : ℝ) < 1 := by
    rw [hz]
    exact factorial_remainder_lt_one n hn
  have : (0 : ℤ) < z ∧ z < 1 := by exact_mod_cast And.intro hz0 hz1
  omega

/-- Both classical irrationality statements of Theorem 5.3. -/
theorem classical_irrationals : P203Specs.Ch05.ClassicalIrrationals :=
  ⟨irrational_exp_one, irrational_pi⟩

end P203.Ch05
