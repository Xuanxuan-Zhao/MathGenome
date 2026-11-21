import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.ThreeSquaresReduction
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace P203.Ch04
open P203Specs.Ch04

theorem threeSquaresZero : ThreeSquaresZero := by
  exact ⟨0, 0, 0, by norm_num⟩

theorem threeSquaresOne : ThreeSquaresOne := by
  exact ⟨1, 0, 0, by norm_num⟩

private theorem sq_mod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  have h₀ := Int.emod_nonneg x (by norm_num : (4 : ℤ) ≠ 0)
  have h₁ := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 4)
  have h₂ : x % 2 = (x % 4) % 2 := by omega
  rw [h₂, pow_two, Int.mul_emod]
  interval_cases h : x % 4 <;> norm_num [h]

private theorem sq_mod_eight (x : ℤ) :
    x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h₀ := Int.emod_nonneg x (by norm_num : (8 : ℤ) ≠ 0)
  have h₁ := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 8)
  rw [pow_two, Int.mul_emod]
  interval_cases h : x % 8 <;> norm_num [h]

theorem evenCoordinates : EvenCoordinates := by
  intro x y z h
  have hx := sq_mod_four x
  have hy := sq_mod_four y
  have hz := sq_mod_four z
  have hs := Int.emod_eq_zero_of_dvd h
  exact ⟨Int.dvd_of_emod_eq_zero (by omega),
    Int.dvd_of_emod_eq_zero (by omega), Int.dvd_of_emod_eq_zero (by omega)⟩

theorem modEightObstruction : ModEightObstruction := by
  intro x y z
  have hx := sq_mod_eight x
  have hy := sq_mod_eight y
  have hz := sq_mod_eight z
  omega

theorem squareScaling : SquareScaling := by
  intro d n ⟨x, y, z, h⟩
  refine ⟨d * x, d * y, d * z, ?_⟩
  push_cast
  rw [h]
  ring

theorem fourDescent : FourDescent := by
  intro n
  constructor
  · rintro ⟨x, y, z, h⟩
    have hd : (4 : ℤ) ∣ x ^ 2 + y ^ 2 + z ^ 2 := by
      rw [← h]
      exact ⟨n, by push_cast; ring⟩
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩ := evenCoordinates x y z hd
    refine ⟨u, v, w, ?_⟩
    push_cast at h
    rw [hu, hv, hw] at h
    nlinarith [h]
  · intro h
    simpa using squareScaling 2 n h

theorem forbiddenObstruction : ForbiddenObstruction := by
  rintro n ⟨a, b, rfl⟩
  induction a with
  | zero =>
    rintro ⟨x, y, z, h⟩
    have hm := modEightObstruction x y z
    norm_num at h
    omega
  | succ a ih =>
    rw [pow_succ]
    have he : 4 ^ a * 4 * (8 * b + 7) = 4 * (4 ^ a * (8 * b + 7)) := by ring
    rw [he, fourDescent]
    exact ih

/-- Removing one factor of four from the forbidden form. -/
theorem forbidden_four_mul (n : ℕ) : Forbidden (4 * n) ↔ Forbidden n := by
  constructor
  · rintro ⟨a, b, h⟩
    cases a with
    | zero => simp only [pow_zero, one_mul] at h; omega
    | succ a =>
      refine ⟨a, b, ?_⟩
      rw [pow_succ] at h
      nlinarith only [h]
  · rintro ⟨a, b, h⟩
    refine ⟨a + 1, b, ?_⟩
    rw [h, pow_succ]
    ring

/-- An odd natural square is one modulo eight. -/
theorem odd_square_mod_eight (d : ℕ) (hd : d % 2 = 1) : d ^ 2 % 8 = 1 := by
  have hlt := Nat.mod_lt d (by decide : 0 < 8)
  have hmod : d % 8 % 2 = 1 := by omega
  rw [pow_two, Nat.mul_mod]
  interval_cases d % 8 <;> norm_num at *

private theorem forbidden_of_mod_eight (n : ℕ) (h : n % 8 = 7) : Forbidden n := by
  exact ⟨0, n / 8, by simp only [pow_zero, one_mul]; omega⟩

private theorem forbidden_cancel_odd_square (d : ℕ) (hd : d % 2 = 1)
    (a : ℕ) : ∀ n b : ℕ, d ^ 2 * n = 4 ^ a * (8 * b + 7) → Forbidden n := by
  have hs := odd_square_mod_eight d hd
  have hs₄ : d ^ 2 % 4 = 1 := by omega
  induction a with
  | zero =>
    intro n b h
    apply forbidden_of_mod_eight
    have hm := congrArg (fun t : ℕ => t % 8) h
    simpa [Nat.mul_mod, hs] using hm
  | succ a ih =>
    intro n b h
    have hn : n % 4 = 0 := by
      have hm := congrArg (fun t : ℕ => t % 4) h
      rw [pow_succ 4 a] at hm
      simpa [Nat.mul_mod, hs₄] using hm
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hn
    have he : d ^ 2 * k = 4 ^ a * (8 * b + 7) := by
      rw [hk, pow_succ 4 a] at h
      nlinarith only [h]
    rw [hk, forbidden_four_mul]
    exact ih k b he

private theorem forbidden_odd_square_mul (d n : ℕ) (hd : d % 2 = 1) :
    Forbidden (d ^ 2 * n) ↔ Forbidden n := by
  constructor
  · rintro ⟨a, b, h⟩
    exact forbidden_cancel_odd_square d hd a n b h
  · rintro ⟨a, b, h⟩
    have hs := odd_square_mod_eight d hd
    have hm : (d ^ 2 * (8 * b + 7)) % 8 = 7 := by
      simp [Nat.mul_mod, hs]
    have he : d ^ 2 * (8 * b + 7) = 8 * (d ^ 2 * (8 * b + 7) / 8) + 7 := by omega
    refine ⟨a, d ^ 2 * (8 * b + 7) / 8, ?_⟩
    rw [h]
    calc
      d ^ 2 * (4 ^ a * (8 * b + 7)) = 4 ^ a * (d ^ 2 * (8 * b + 7)) := by ring
      _ = _ := congrArg (fun t => 4 ^ a * t) he

theorem forbiddenSquareScaling : ForbiddenSquareScaling := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro n hd
    by_cases he : d % 2 = 0
    · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero he
      have hkpos : 0 < k := by omega
      have hklt : k < d := by omega
      have heq : d ^ 2 * n = 4 * (k ^ 2 * n) := by rw [hk]; ring
      rw [heq, forbidden_four_mul]
      exact ih k hklt n hkpos
    · exact forbidden_odd_square_mul d n (by omega)

theorem squarefreeReduction : SquarefreeReduction := by
  intro n hn
  obtain ⟨n₀, d, hn₀, hd, he, hs⟩ := Nat.sq_mul_squarefree_of_pos hn
  refine ⟨d, n₀, hd, hn₀, hs, he.symm, ?_, ?_⟩
  · rw [← he]
    exact forbiddenSquareScaling d n₀ hd
  · intro h
    rw [← he]
    exact squareScaling d n₀ h

private theorem forbidden_mod_eight_or_four_dvd (n : ℕ) (h : Forbidden n) :
    n % 8 = 7 ∨ 4 ∣ n := by
  obtain ⟨a, b, rfl⟩ := h
  cases a with
  | zero => simp
  | succ a =>
    right
    refine ⟨4 ^ a * (8 * b + 7), ?_⟩
    rw [pow_succ]
    ring

theorem squarefreeResidues : SquarefreeResidues := by
  intro n hs
  have hn : ¬4 ∣ n := by
    exact (Nat.squarefree_iff_prime_squarefree.mp hs) 2 Nat.prime_two
  have hr : n % 8 ≠ 0 ∧ n % 8 ≠ 4 := by
    constructor <;> intro h <;> apply hn <;> apply Nat.dvd_of_mod_eq_zero <;> omega
  constructor
  · intro hf
    have h7 : n % 8 ≠ 7 := fun h => hf (forbidden_of_mod_eight n h)
    omega
  · intro h hf
    rcases forbidden_mod_eight_or_four_dvd n hf with h7 | h4
    · omega
    · exact hn h4

end P203.Ch04
