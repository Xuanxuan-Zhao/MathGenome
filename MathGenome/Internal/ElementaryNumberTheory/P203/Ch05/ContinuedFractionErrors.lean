import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.ContinuedFractionErrors
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.Convergents
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace P203
open P203Specs Filter
open scoped Topology

private theorem irrational_digit_exists (x : ℝ) (hx : Irrational x) (n : ℕ) :
    ∃ a : ℤ, P203Specs.partialQuotient x n = some a := by
  obtain ⟨α, hα⟩ := irrational_completeQuotient_defined x hx n
  exact ⟨⌊α⌋, by rw [algorithm_digits, hα]; rfl⟩

/-- Divide the exact linear error by the positive denominator. -/
private theorem abs_fractional_error (p q D x : ℝ) (n : ℕ)
    (hq : 0 < q) (hD : 0 < D) (he : q * x - p = (-1 : ℝ) ^ n / D) :
    |x - p / q| = 1 / (q * D) := by
  have h : x - p / q = (q * x - p) / q := by
    field_simp
  rw [h, he, div_div, abs_div, abs_pow]
  rw [abs_neg, abs_one, one_pow, abs_of_pos (mul_pos hD hq), mul_comm D q]

theorem convergent_error_bounds : ConvergentErrorBounds := by
  intro x hx n
  obtain ⟨α, hα, hD, _, _, he⟩ := convergent_exact_tail x hx n
  obtain ⟨β, hβ⟩ := irrational_completeQuotient_defined x hx (n + 1 + 1)
  have hnonint : α ≠ (⌊α⌋ : ℝ) := by
    intro h
    have ht := (algorithm_stopping x α (n + 1) hα).mpr h
    rw [hβ] at ht
    contradiction
  have hlo : (⌊α⌋ : ℝ) < α := lt_of_le_of_ne (Int.floor_le α) (Ne.symm hnonint)
  have hhi : α < (⌊α⌋ : ℝ) + 1 := Int.lt_floor_add_one α
  have ha : P203Specs.partialQuotient x (n + 1) = some ⌊α⌋ := by
    rw [algorithm_digits, hα]
    rfl
  have hr := (convergent_recurrences x (n + 1) ⌊α⌋ ha).2
  have hprev : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
  have hprevprev : ((n + 1 : ℕ) : ℤ) - 2 = (n : ℤ) - 1 := by omega
  rw [hprev, hprevprev] at hr
  have hrR : (P203Specs.convergentDenominator x (n + 1 : ℕ) : ℝ) =
      (⌊α⌋ : ℝ) * (P203Specs.convergentDenominator x n : ℝ) +
        (P203Specs.convergentDenominator x ((n : ℤ) - 1) : ℝ) := by
    exact_mod_cast hr
  have hq : (0 : ℝ) < P203Specs.convergentDenominator x n := by
    exact_mod_cast convergent_denominator_pos x n
  have hqn : (0 : ℝ) < P203Specs.convergentDenominator x (n + 1 : ℕ) := by
    exact_mod_cast convergent_denominator_pos x (n + 1)
  have hlow : (P203Specs.convergentDenominator x (n + 1 : ℕ) : ℝ) <
      (P203Specs.convergentDenominator x n : ℝ) * α +
        (P203Specs.convergentDenominator x ((n : ℤ) - 1) : ℝ) := by
    nlinarith [mul_lt_mul_of_pos_left hlo hq]
  have hupp : (P203Specs.convergentDenominator x n : ℝ) * α +
      (P203Specs.convergentDenominator x ((n : ℤ) - 1) : ℝ) <
      (P203Specs.convergentDenominator x (n + 1 : ℕ) : ℝ) +
        (P203Specs.convergentDenominator x n : ℝ) := by
    nlinarith [mul_lt_mul_of_pos_left hhi hq]
  rw [abs_fractional_error _ _ _ _ n hq hD he]
  constructor
  · exact one_div_lt_one_div_of_lt (mul_pos hq hD) (mul_lt_mul_of_pos_left hupp hq)
  · exact one_div_lt_one_div_of_lt (mul_pos hq hqn) (mul_lt_mul_of_pos_left hlow hq)

/-- A linear lower bound suffices for divergence; the possible equality
`q₀=q₁=1` causes no difficulty. -/
theorem index_le_convergent_denominator (x : ℝ) (hx : Irrational x) (n : ℕ) :
    (n : ℤ) ≤ P203Specs.convergentDenominator x n := by
  induction n with
  | zero => exact le_of_lt (convergent_denominator_pos x 0)
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      have hp := convergent_denominator_pos x 1
      norm_num only [Nat.cast_one] at hp
      change (1 : ℤ) ≤ P203Specs.convergentDenominator x 1
      omega
    · obtain ⟨a, ha⟩ := irrational_digit_exists x hx (n + 1)
      have hg := convergent_denominator_growth.2.2 x n (by omega)
        (by rw [ha]; exact Option.some_ne_none a)
      have : (n : ℤ) + 1 ≤ P203Specs.convergentDenominator x ((n : ℤ) + 1) := by omega
      simpa only [Nat.cast_add, Nat.cast_one] using this

theorem convergent_denominators_tendToInfinity : ConvergentDenominatorsTendToInfinity := by
  intro x hx
  exact tendsto_atTop_mono (index_le_convergent_denominator x hx)
    tendsto_natCast_atTop_atTop

theorem convergent_convergence : ConvergentConvergence := by
  intro x _
  have hfun : (fun n : ℕ => (P203Specs.convergentNumerator x n : ℝ) /
      (P203Specs.convergentDenominator x n : ℝ)) = (GenContFract.of x).convs := by
    funext n
    exact (convergent_mathlib_bridge x n).2.2.1
  rw [hfun]
  exact GenContFract.of_convergence x

/-- The canonical recurrences depend only on the digits, including the head. -/
theorem integerContinuants_eq_of_digits_eq (x y : ℝ)
    (h : ∀ n : ℕ, P203Specs.partialQuotient x n = P203Specs.partialQuotient y n)
    (n : ℕ) : P203Specs.integerContinuants x n = P203Specs.integerContinuants y n := by
  have hh : ⌊x⌋ = ⌊y⌋ := by
    have h0 := h 0
    rw [(algorithm_initial x).2, (algorithm_initial y).2] at h0
    exact Option.some.inj h0
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp only [P203Specs.integerContinuants, hh]
  | more n ih ih' =>
    simp only [P203Specs.integerContinuants, h (n + 1), ih, ih']

theorem infinite_digit_uniqueness : InfiniteDigitUniqueness := by
  intro x y hx hy h
  have hc : P203Specs.integerContinuants x = P203Specs.integerContinuants y :=
    funext (integerContinuants_eq_of_digits_eq x y h)
  have hfun : (fun n : ℕ => (P203Specs.convergentNumerator x n : ℝ) /
      (P203Specs.convergentDenominator x n : ℝ)) =
      (fun n : ℕ => (P203Specs.convergentNumerator y n : ℝ) /
      (P203Specs.convergentDenominator y n : ℝ)) := by
    simp only [P203Specs.convergentNumerator, P203Specs.convergentDenominator, hc]
  have hlim := convergent_convergence x hx
  rw [hfun] at hlim
  exact tendsto_nhds_unique hlim (convergent_convergence y hy)

end P203
