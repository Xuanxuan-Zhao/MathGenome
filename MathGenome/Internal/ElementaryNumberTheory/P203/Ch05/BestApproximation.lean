import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.BestApproximation
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.Convergents
import Mathlib.Tactic.LinearCombination

namespace P203

/-- Consecutive integer columns of determinant ±1 span every integer pair. -/
private theorem unimodular_coordinates (p₀ q₀ p₁ q₁ p q : ℤ)
    (h : p₀ * q₁ - p₁ * q₀ = 1 ∨ p₀ * q₁ - p₁ * q₀ = -1) :
    ∃ u v : ℤ, p = u * p₀ + v * p₁ ∧ q = u * q₀ + v * q₁ := by
  rcases h with h | h
  · refine ⟨p * q₁ - p₁ * q, p₀ * q - p * q₀, ?_, ?_⟩
    · linear_combination -p * h
    · linear_combination -q * h
  · refine ⟨-(p * q₁ - p₁ * q), -(p₀ * q - p * q₀), ?_, ?_⟩
    · linear_combination p * h
    · linear_combination q * h

/-- Opposite coefficient signs turn opposite errors into a sum of magnitudes. -/
private theorem abs_opposite_errors (u v e f : ℝ) (huv : u * v < 0) (hef : e * f < 0) :
    |u * e + v * f| = |u| * |e| + |v| * |f| := by
  have h : 0 < (u * e) * (v * f) := by
    convert mul_pos_of_neg_of_neg huv hef using 1; ring
  have ha : |u * e + v * f| = |u * e| + |v * f| := by
    rcases mul_pos_iff.mp h with ⟨hue, hvf⟩ | ⟨hue, hvf⟩
    · rw [abs_of_pos hue, abs_of_pos hvf, abs_of_pos (add_pos hue hvf)]
    · rw [abs_of_neg hue, abs_of_neg hvf, abs_of_neg (add_neg hue hvf)]
      ring
  simpa only [abs_mul] using ha

/-- The basis argument, including the strict inequality away from the first column. -/
private theorem basis_best_approximation (x : ℝ) (p₀ q₀ p₁ q₁ p q : ℤ)
    (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq : 0 < q) (hqq : q < q₁)
    (hdet : p₀ * q₁ - p₁ * q₀ = 1 ∨ p₀ * q₁ - p₁ * q₀ = -1)
    (herr : ((q₀ : ℝ) * x - p₀) * ((q₁ : ℝ) * x - p₁) < 0) :
    |(q₀ : ℝ) * x - p₀| ≤ |(q : ℝ) * x - p| ∧
      (|(q : ℝ) * x - p| = |(q₀ : ℝ) * x - p₀| → (p, q) = (p₀, q₀)) := by
  obtain ⟨u, v, hp, hqeq⟩ := unimodular_coordinates p₀ q₀ p₁ q₁ p q hdet
  let e : ℝ := (q₀ : ℝ) * x - p₀
  let f : ℝ := (q₁ : ℝ) * x - p₁
  have he : 0 < |e| := abs_pos.mpr (by intro h; change e * f < 0 at herr; rw [h, zero_mul] at herr; linarith)
  have hf : 0 < |f| := abs_pos.mpr (by intro h; change e * f < 0 at herr; rw [h, mul_zero] at herr; linarith)
  have herr_eq : (q : ℝ) * x - p = (u : ℝ) * e + (v : ℝ) * f := by
    rw [hp, hqeq]
    push_cast
    dsimp [e, f]
    ring
  rw [herr_eq]
  change |e| ≤ _ ∧ (_ = |e| → _)
  by_cases hv : v = 0
  · have hu : 1 ≤ u := by
      rw [hv, zero_mul, add_zero] at hqeq
      have : 0 < u := by
        by_contra! hu
        have := mul_nonpos_of_nonpos_of_nonneg hu hq₀.le
        omega
      omega
    have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have habs : |(u : ℝ) * e + (v : ℝ) * f| = (u : ℝ) * |e| := by
      simp [hv, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u)]
    rw [habs]
    refine ⟨by nlinarith, ?_⟩
    intro heq
    have hu1 : u = 1 := by
      have : (u : ℝ) = 1 := by nlinarith
      exact_mod_cast this
    simp_all
  · have huv : u * v < 0 := by
      rcases lt_or_gt_of_ne hv with hvneg | hvpos
      · have hu : 0 < u := by
          by_contra! hu
          have h₁ := mul_nonpos_of_nonpos_of_nonneg hu hq₀.le
          have h₂ := mul_neg_of_neg_of_pos hvneg hq₁
          omega
        exact mul_neg_of_pos_of_neg hu hvneg
      · have hu : u < 0 := by
          by_contra! hu
          have h₁ := mul_nonneg hu hq₀.le
          have h₂ : q₁ ≤ v * q₁ := by nlinarith
          omega
        exact mul_neg_of_neg_of_pos hu hvpos
    have huabs : (1 : ℝ) ≤ |(u : ℝ)| := by
      have hu0 : u ≠ 0 := by intro h; simp [h] at huv
      exact_mod_cast (show (1 : ℤ) ≤ |u| by
        rcases lt_or_gt_of_ne hu0 with h | h
        · rw [abs_of_neg h]; omega
        · rw [abs_of_pos h]; omega)
    have hvabs : 0 < |(v : ℝ)| := abs_pos.mpr (by exact_mod_cast hv)
    have hstrict : |e| < |(u : ℝ) * e + (v : ℝ) * f| := by
      rw [abs_opposite_errors _ _ _ _ (by exact_mod_cast huv) herr]
      nlinarith [mul_pos hvabs hf]
    exact ⟨hstrict.le, fun h => False.elim (ne_of_gt hstrict h)⟩

private theorem irrational_digit_present (x : ℝ) (hx : Irrational x) (n : ℕ) :
    P203Specs.partialQuotient x n ≠ none := by
  obtain ⟨α, hα⟩ := irrational_completeQuotient_defined x hx n
  rw [algorithm_digits, hα]
  simp

private theorem consecutive_errors_opposite (x : ℝ) (hx : Irrational x) (n : ℕ) :
    ((P203Specs.convergentDenominator x n : ℝ) * x -
      P203Specs.convergentNumerator x n) *
    ((P203Specs.convergentDenominator x (n + 1 : ℕ) : ℝ) * x -
      P203Specs.convergentNumerator x (n + 1 : ℕ)) < 0 := by
  obtain ⟨α, _, hA, _, _, he⟩ := convergent_exact_tail x hx n
  obtain ⟨β, _, hB, _, _, hf⟩ := convergent_exact_tail x hx (n + 1)
  rw [he, hf, pow_succ]
  rcases neg_one_pow_eq_or ℝ n with h | h
  · rw [h]
    norm_num only [one_mul]
    exact mul_neg_of_pos_of_neg (div_pos zero_lt_one hA)
      (div_neg_of_neg_of_pos (by norm_num) hB)
  · rw [h]
    norm_num only [neg_mul, one_mul, neg_neg]
    exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by norm_num) hA)
      (div_pos zero_lt_one hB)

private theorem best_approximation_full (x : ℝ) (hx : Irrational x) (n : ℕ)
    (p q : ℤ) (hq : 0 < q) (hqq : q < P203Specs.convergentDenominator x (n + 1 : ℕ)) :
    |(P203Specs.convergentDenominator x n : ℝ) * x -
        P203Specs.convergentNumerator x n| ≤ |(q : ℝ) * x - p| ∧
    (|(q : ℝ) * x - p| = |(P203Specs.convergentDenominator x n : ℝ) * x -
        P203Specs.convergentNumerator x n| →
      (p, q) = (P203Specs.convergentNumerator x n, P203Specs.convergentDenominator x n)) := by
  apply basis_best_approximation x
    (P203Specs.convergentNumerator x n) (P203Specs.convergentDenominator x n)
    (P203Specs.convergentNumerator x (n + 1 : ℕ))
    (P203Specs.convergentDenominator x (n + 1 : ℕ)) p q
    (convergent_denominator_pos x n) (convergent_denominator_pos x (n + 1)) hq hqq
  · have hd := convergent_determinant x (n + 1) (irrational_digit_present x hx (n + 1))
    rw [show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by omega] at hd
    rcases neg_one_pow_eq_or ℤ (n + 1 + 1) with h | h
    · right; rw [h] at hd; linarith
    · left; rw [h] at hd; linarith
  · exact consecutive_errors_opposite x hx n

/-- Every integer pair in the source denominator range has at least the
scaled numerator error of the nth convergent. -/
theorem best_approximation_second_kind : P203Specs.BestApproximationSecondKind := by
  intro x hx n p q hq hqq
  exact (best_approximation_full x hx n p q hq hqq).1

/-- Equality in that range identifies the actual integer numerator and denominator. -/
theorem best_approximation_equality : P203Specs.BestApproximationEquality := by
  intro x hx n p q hq hqq heq
  exact (best_approximation_full x hx n p q hq hqq).2 heq

end P203
