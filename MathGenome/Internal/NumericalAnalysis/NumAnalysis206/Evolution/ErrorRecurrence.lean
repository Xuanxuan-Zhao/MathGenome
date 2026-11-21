import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.ErrorRecurrence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open scoped Topology
open Filter Finset

namespace NumAnalysis206.Evolution

/-- Iteration of a scalar affine inequality on a finite horizon. -/
theorem weightedPropagation : Specs.NumAnalysis206.Evolution.WeightedPropagation := by
  intro T h L e τ hT hh hL he hτ hrec n hn
  have ha : 0 ≤ 1 + L * h := by positivity
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev : (n : ℝ) * h ≤ T := by
      calc
        (n : ℝ) * h ≤ ((n + 1 : ℕ) : ℝ) * h :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hh.le
        _ ≤ T := hn
    have hi := ih hprev
    calc
      e (n + 1) ≤ (1 + L * h) * e n + h * τ n := hrec n hn
      _ ≤ (1 + L * h) * ((1 + L * h) ^ n * e 0 +
          ∑ j ∈ range n, h * (1 + L * h) ^ (n - 1 - j) * τ j) + h * τ n :=
        add_le_add (mul_le_mul_of_nonneg_left hi ha) le_rfl
      _ = (1 + L * h) ^ (n + 1) * e 0 +
          ∑ j ∈ range (n + 1), h * (1 + L * h) ^ (n + 1 - 1 - j) * τ j := by
        rw [sum_range_succ, mul_add, mul_sum]
        have hs : (∑ j ∈ range n, (1 + L * h) *
            (h * (1 + L * h) ^ (n - 1 - j) * τ j)) =
            ∑ j ∈ range n, h * (1 + L * h) ^ (n + 1 - 1 - j) * τ j := by
          apply sum_congr rfl
          intro j hj
          have hjn : j < n := mem_range.mp hj
          have hx : n + 1 - 1 - j = (n - 1 - j) + 1 := by omega
          rw [hx, pow_succ]
          ring
        rw [hs, pow_succ]
        simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
        ring

/-- Every geometric propagation multiplier stays below the horizon exponential. -/
lemma growthFactor_le_exp {T h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (n : ℕ) (hn : (n : ℝ) * h ≤ T) :
    (1 + L * h) ^ n ≤ Real.exp (L * T) := by
  have ha : 0 ≤ 1 + L * h := by positivity
  calc
    (1 + L * h) ^ n ≤ (Real.exp (L * h)) ^ n := by
      apply pow_le_pow_left₀ ha
      linarith [Real.add_one_le_exp (L * h)]
    _ = Real.exp ((n : ℝ) * (L * h)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (L * T) := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hn hL])

/-- Uniform local defects give the source's explicit exponential bound. -/
theorem uniformPropagation : Specs.NumAnalysis206.Evolution.UniformPropagation := by
  intro T h L τ e hT hh hL hτ he hrec n hn
  have hw := weightedPropagation T h L e (fun _ => τ) hT hh hL he (fun _ => hτ) hrec n hn
  have hi := mul_le_mul_of_nonneg_right (growthFactor_le_exp hh hL n hn) (he 0)
  have hs : (∑ j ∈ range n, h * (1 + L * h) ^ (n - 1 - j) * τ) ≤
      T * Real.exp (L * T) * τ := by
    calc
      (∑ j ∈ range n, h * (1 + L * h) ^ (n - 1 - j) * τ) ≤
          ∑ j ∈ range n, h * Real.exp (L * T) * τ := by
        apply sum_le_sum
        intro j hj
        have htime : ((n - 1 - j : ℕ) : ℝ) * h ≤ T := by
          calc
            _ ≤ (n : ℝ) * h := mul_le_mul_of_nonneg_right
              (by exact_mod_cast (show n - 1 - j ≤ n by omega)) hh.le
            _ ≤ T := hn
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (growthFactor_le_exp hh hL _ htime) hh.le) hτ
      _ = ((n : ℝ) * h) * (Real.exp (L * T) * τ) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring
      _ ≤ T * (Real.exp (L * T) * τ) := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = T * Real.exp (L * T) * τ := by ring
  exact hw.trans (add_le_add hi hs)

/-- A natural index is in the finite range exactly when its mesh time is admissible. -/
lemma meshIndex_iff {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (n : ℕ) :
    n ∈ range (⌊T / h⌋₊ + 1) ↔ (n : ℝ) * h ≤ T := by
  rw [mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (div_nonneg hT hh.le), le_div_iff₀ hh]

/-- The finite supremum is attained, and its indices are exactly the admissible mesh times. -/
theorem meshMaximumCharacterization :
    Specs.NumAnalysis206.Evolution.MeshMaximumCharacterization := by
  intro T h e hT hh
  constructor
  · obtain ⟨n, hn, heq⟩ := exists_mem_eq_sup'
      (show (range (⌊T / h⌋₊ + 1)).Nonempty from
        ⟨0, mem_range.mpr (Nat.zero_lt_succ _)⟩) e
    exact ⟨n, (meshIndex_iff hT.le hh n).mp hn, heq.symm⟩
  · rintro v ⟨n, hn, rfl⟩
    exact le_sup' e ((meshIndex_iff hT.le hh n).mpr hn)

/-- The quantitative estimate is uniform over all mesh times on the horizon. -/
theorem meshMaximumBound : Specs.NumAnalysis206.Evolution.MeshMaximumBound := by
  intro T h L τ e hT hh hL hτ he hrec
  unfold meshErrorMax
  apply sup'_le
  intro n hn
  exact uniformPropagation T h L τ e hT hh hL hτ he hrec n
    ((meshIndex_iff hT.le hh n).mp hn)

/-- Vanishing initial errors and uniform local defects imply mesh-uniform convergence. -/
theorem meshMaximumConvergence :
    Specs.NumAnalysis206.Evolution.MeshMaximumConvergence := by
  intro T L e τ hT hL he hτ hrec he0 hτ0
  have hnonneg : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ meshErrorMax T h (e h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hz : (0 : ℝ) * h ≤ T := by simpa using hT.le
    exact (he h hh 0).trans
      ((meshMaximumCharacterization T h (e h) hT hh).2 ⟨0, by simpa using hz, rfl⟩)
  have hbound : ∀ᶠ h in 𝓝[>] (0 : ℝ), meshErrorMax T h (e h) ≤
      Real.exp (L * T) * e h 0 + T * Real.exp (L * T) * τ h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact meshMaximumBound T h L (τ h) (e h) hT hh hL (hτ h hh) (he h hh) (hrec h hh)
  have hlim : Tendsto (fun h => Real.exp (L * T) * e h 0 +
      T * Real.exp (L * T) * τ h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (he0.const_mul (Real.exp (L * T))).add
      (hτ0.const_mul (T * Real.exp (L * T)))
  exact squeeze_zero' hnonneg hbound hlim

end NumAnalysis206.Evolution
