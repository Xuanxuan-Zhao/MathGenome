import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.RadixModel
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Underflow
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NumAnalysis206.Rounding

/-- The smallest normal is the last point on the minimum-exponent grid. -/
theorem amin_eq_grid_endpoint (P : RadixFormat) :
    amin P = ((P.β ^ (P.p - 1) : ℤ) : ℝ) * (P.β : ℝ) ^ P.emin := by
  have hb : (0 : ℝ) < P.β := by exact_mod_cast (lt_of_lt_of_le (by norm_num) P.radix_ge_two)
  have hp : (P.p : ℤ) - 1 = ((P.p - 1 : ℕ) : ℤ) := by
    have := P.precision_pos
    omega
  simp only [amin, Specs.aminValue, hp, zpow_add₀ hb.ne', zpow_natCast, Int.cast_pow]

/-- Every signed minimum-exponent grid point up to the smallest normal is
representable when gradual underflow is enabled. -/
theorem underflow_grid_mem (P : RadixFormat) (hg : P.gradual = true) (m : ℤ)
    (hm : |m| ≤ P.β ^ (P.p - 1)) :
    (m : ℝ) * (P.β : ℝ) ^ P.emin ∈ F P := by
  have hb : (0 : ℤ) < P.β := by linarith [P.radix_ge_two]
  have hn : (0 : ℤ) < P.β ^ (P.p - 1) := pow_pos hb _
  have hnlt : P.β ^ (P.p - 1) < P.β ^ P.p := by
    have he : P.p = (P.p - 1) + 1 := by
      have := P.precision_pos
      omega
    have heq : P.β ^ P.p = P.β ^ (P.p - 1) * P.β := by
      conv_lhs => rw [he, pow_succ]
    rw [heq]
    nlinarith [P.radix_ge_two]
  by_cases hz : m = 0
  · subst m
    simp
  have hmpos : 1 ≤ |m| := by
    have := abs_pos.mpr hz
    omega
  have hsign : (m : ℝ) * (P.β : ℝ) ^ P.emin =
      ((|m| : ℤ) : ℝ) * (P.β : ℝ) ^ P.emin ∨
      (m : ℝ) * (P.β : ℝ) ^ P.emin =
      -(((|m| : ℤ) : ℝ) * (P.β : ℝ) ^ P.emin) := by
    rcases le_total 0 m with h | h
    · left
      rw [abs_of_nonneg h]
    · right
      rw [abs_of_nonpos h, Int.cast_neg]
      ring
  rw [mem_F]
  by_cases htop : |m| = P.β ^ (P.p - 1)
  · exact Or.inr (Or.inl ⟨|m|, P.emin, htop.ge, htop.trans_lt hnlt,
      le_rfl, P.exponent_order, hsign⟩)
  · exact Or.inr (Or.inr ⟨hg, |m|, hmpos, lt_of_le_of_ne hm htop, hsign⟩)

/-- Gradual underflow gives a half-grid-spacing absolute error bound near zero.
The integer rounding used for the comparison point can have any tie rule. -/
theorem gradual_underflow_bound (P : RadixFormat) (hg : P.gradual = true)
    (x : ℝ) (hx : |x| ≤ amin P) :
    |fl P x - x| ≤ (P.β : ℝ) ^ P.emin / 2 := by
  let s : ℝ := (P.β : ℝ) ^ P.emin
  let N : ℤ := P.β ^ (P.p - 1)
  have hb : (0 : ℝ) < P.β := by exact_mod_cast (lt_of_lt_of_le (by norm_num) P.radix_ge_two)
  have hs : 0 < s := zpow_pos hb _
  have hx' : |x| ≤ (N : ℝ) * s := by
    simpa only [amin_eq_grid_endpoint, N, s] using hx
  have hscaled : |x / s| ≤ (N : ℝ) := by
    rw [abs_div, abs_of_pos hs]
    exact (div_le_iff₀ hs).mpr hx'
  have hmono : Monotone (round : ℝ → ℤ) := by
    intro a b hab
    rw [round_eq, round_eq]
    exact Int.floor_mono (by linarith)
  let m : ℤ := round (x / s)
  have hm : |m| ≤ N := by
    apply abs_le.mpr
    constructor
    · have hh := hmono (abs_le.mp hscaled).1
      simpa only [round_intCast, ← Int.cast_neg, m] using hh
    · have hh := hmono (abs_le.mp hscaled).2
      simpa only [round_intCast, m] using hh
  have hmem : (m : ℝ) * s ∈ F P := underflow_grid_mem P hg m hm
  have hdist : |(m : ℝ) * s - x| ≤ s / 2 := by
    have hround : |(m : ℝ) - x / s| ≤ (1 : ℝ) / 2 := by
      simpa only [abs_sub_comm, m] using (abs_sub_round (x / s))
    calc
      |(m : ℝ) * s - x| = |((m : ℝ) - x / s) * s| := by
        congr 1
        rw [sub_mul, div_mul_cancel₀ _ hs.ne']
      _ = |(m : ℝ) - x / s| * s := by rw [abs_mul, abs_of_pos hs]
      _ ≤ (1 / 2) * s := mul_le_mul_of_nonneg_right hround hs.le
      _ = s / 2 := by ring
  exact (fl_minimizes P x ((m : ℝ) * s) hmem).trans hdist

end NumAnalysis206.Rounding
