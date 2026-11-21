import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.KroneckerLemma
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Finset
open scoped Topology BigOperators

namespace ProbabilityFoundations.Ch08

/-- Weighted averages of a null sequence, with possibly zero weight increments. -/
private theorem weighted_null (b u : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (hm : Monotone b) (hdiverge : Tendsto b atTop atTop)
    (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n ↦ (∑ k ∈ range n, (b (k + 1) - b k) * u k) / b n)
      atTop (𝓝 0) := by
  let S := fun n ↦ ∑ k ∈ range n, (b (k + 1) - b k) * u k
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu (ε / 2) (by positivity)
  have huN (n : ℕ) (hn : N ≤ n) : |u n| ≤ ε / 2 := by
    simpa [Real.dist_eq] using (hN n hn).le
  have hbound (n : ℕ) (hn : N ≤ n) :
      |S n| ≤ |S N| + (ε / 2) * (b n - b N) := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hd : 0 ≤ b (n + 1) - b n := sub_nonneg.mpr (hm (Nat.le_succ n))
      have hterm : |(b (n + 1) - b n) * u n| ≤ (b (n + 1) - b n) * (ε / 2) := by
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left (huN n hn) hd
      have htri := abs_add_le (S n) ((b (n + 1) - b n) * u n)
      have hS : S (n + 1) = S n + (b (n + 1) - b n) * u n := sum_range_succ _ _
      rw [hS]
      nlinarith
  have hz : Tendsto (fun n ↦ |S N| / b n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hdiverge
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hz (ε / 2) (by positivity)
  refine ⟨max N M, fun n hn ↦ ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M ≤ n := le_trans (le_max_right _ _) hn
  have hsmall : |S N| / b n < ε / 2 := by
    have := hM n hnM
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg (abs_nonneg _) (hb n).le)] using this
  have hest : |S n| / b n ≤ |S N| / b n + ε / 2 := by
    apply (div_le_iff₀ (hb n)).mpr
    have h := hbound n hnN
    have hp := hb N
    nlinarith [div_mul_cancel₀ (|S N|) (ne_of_gt (hb n))]
  change dist (S n / b n) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (hb n)]
  linarith

/-- Kronecker's lemma, allowing conditional convergence and nonstrict weights. -/
theorem kroneckerLemma : Specs.KroneckerLemma := by
  intro a b hb hm hdiverge hseries
  obtain ⟨c, hc⟩ := hseries
  let A : ℕ → ℝ := fun k ↦ a (k + 1)
  let B : ℕ → ℝ := fun k ↦ b (k + 1)
  let C : ℕ → ℝ := fun n ↦ ∑ k ∈ range n, A k / B k
  have hB (n : ℕ) : 0 < B n := hb (n + 1) (by omega)
  have hBm : Monotone B := fun i j hij ↦ hm (by simp) (by simp) (by omega)
  have hBt : Tendsto B atTop atTop := hdiverge.comp (tendsto_add_atTop_nat 1)
  have hC : Tendsto C atTop (𝓝 c) := hc
  have hu : Tendsto (fun k ↦ C (k + 1) - c) atTop (𝓝 0) := by
    simpa using (hC.comp (tendsto_add_atTop_nat 1)).sub (tendsto_const_nhds (x := c))
  have hw := weighted_null B (fun k ↦ C (k + 1) - c) hB hBm hBt hu
  have hz : Tendsto (fun n ↦ c * B 0 / B n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hBt
  have hlimit := (hu.sub hw).add hz
  have hparts (n : ℕ) :
      (∑ k ∈ range (n + 1), A k) / B n =
        (C (n + 1) - c) -
          (∑ k ∈ range n, (B (k + 1) - B k) * (C (k + 1) - c)) / B n +
          c * B 0 / B n := by
    have hp := sum_range_by_parts B (fun k ↦ A k / B k) (n + 1)
    simp only [Nat.add_sub_cancel, smul_eq_mul] at hp
    have hcancel : (∑ k ∈ range (n + 1), B k * (A k / B k)) =
        ∑ k ∈ range (n + 1), A k := by
      apply sum_congr rfl
      intro k hk
      field_simp [ne_of_gt (hB k)]
    rw [hcancel] at hp
    change (∑ k ∈ range (n + 1), A k) =
      B n * C (n + 1) - ∑ k ∈ range n, (B (k + 1) - B k) * C (k + 1) at hp
    have hs : (∑ k ∈ range n, (B (k + 1) - B k) * (C (k + 1) - c)) =
        (∑ k ∈ range n, (B (k + 1) - B k) * C (k + 1)) - (B n - B 0) * c := by
      simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, sum_range_sub]
    rw [hs, hp]
    field_simp [ne_of_gt (hB n)]
    ring
  have hshift : Tendsto (fun n : ℕ ↦ (b (n + 1))⁻¹ *
      ∑ k ∈ range (n + 1), a (k + 1)) atTop (𝓝 0) := by
    convert hlimit using 1
    · funext n
      simpa [A, B, div_eq_mul_inv, mul_comm] using hparts n
    · norm_num
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

end ProbabilityFoundations.Ch08
