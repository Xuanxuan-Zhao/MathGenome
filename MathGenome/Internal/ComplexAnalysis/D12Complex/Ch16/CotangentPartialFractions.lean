import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.CotangentPartialFractions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace D12Complex.CotangentPartialFractions

/-- Combining the two simple fractions keeps each positive/negative pair
inside a single summand. No unpaired bilateral summation is used. -/
lemma paired_term_eq_cotTerm {z : ℂ} (hz : z ∈ Complex.integerComplement) (n : ℕ) :
    2 * z / (z ^ 2 - ((n : ℂ) + 1) ^ 2) = cotTerm z n := by
  rw [cotTerm_identity hz n]
  ring

theorem cotangent_paired_hasSum :
    Specs.D12Complex.Ch16.CotangentPartialFractions.cotangent_paired_hasSum_type := by
  intro z hz
  simp_rw [paired_term_eq_cotTerm hz]
  convert (summable_cotTerm hz).hasSum using 1
  exact cot_series_rep' hz

theorem cotangent_partial_fractions :
    Specs.D12Complex.Ch16.CotangentPartialFractions.cotangent_partial_fractions_type := by
  intro z hz
  have h := (cotangent_paired_hasSum z hz).tsum_eq
  linear_combination -h

/-- A uniform inverse-square bound on a disk, for all sufficiently late
paired terms. It is independent of the distance to the integer poles. -/
lemma norm_paired_term_le {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R)
    {n : ℕ} (hn : 2 * R ≤ (n : ℝ) + 1) :
    ‖2 * z / (z ^ 2 - ((n : ℂ) + 1) ^ 2)‖ ≤
      8 * R / ((n : ℝ) + 1) ^ 2 := by
  have ht : 0 < (n : ℝ) + 1 := by positivity
  have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  have hs : ‖z‖ ^ 2 ≤ R ^ 2 := by gcongr
  have hs' : R ^ 2 ≤ (((n : ℝ) + 1) / 2) ^ 2 := by
    gcongr
    linarith
  have hden : ((n : ℝ) + 1) ^ 2 / 2 ≤
      ‖z ^ 2 - ((n : ℂ) + 1) ^ 2‖ := by
    have hrev := norm_sub_norm_le (((n : ℂ) + 1) ^ 2) (z ^ 2)
    rw [norm_sub_rev] at hrev
    simp only [norm_pow, hnorm] at hrev
    nlinarith
  have hdpos : 0 < ‖z ^ 2 - ((n : ℂ) + 1) ^ 2‖ :=
    lt_of_lt_of_le (by positivity) hden
  rw [norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ hdpos).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ 8 * R by positivity)]

lemma summableLocallyUniformlyOn_paired_terms :
    SummableLocallyUniformlyOn
      (fun (n : ℕ) (z : ℂ) => 2 * z / (z ^ 2 - ((n : ℂ) + 1) ^ 2))
      Complex.integerComplement := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    Complex.isOpen_compl_range_intCast
  intro K _hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
  let B : ℝ := max 0 R
  have hB : 0 ≤ B := le_max_left _ _
  refine ⟨fun n : ℕ => 8 * B / ((n : ℝ) + 1) ^ 2, ?_, ?_⟩
  · have hp := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    have hp' := (summable_nat_add_iff 1).mpr hp
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using hp'.mul_left (8 * B)
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * B)] with n hn
    intro z hz
    apply norm_paired_term_le hB ?_ (by linarith)
    have hzR := hR hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hzR
    exact hzR.trans (le_max_right _ _)

theorem cotangent_paired_locally_uniform :
    Specs.D12Complex.Ch16.CotangentPartialFractions.cotangent_paired_locally_uniform_type := by
  apply summableLocallyUniformlyOn_paired_terms.hasSumLocallyUniformlyOn.congr_right
  intro z hz
  exact (cotangent_paired_hasSum z hz).tsum_eq

theorem cotangent_paired_partial_sums :
    Specs.D12Complex.Ch16.CotangentPartialFractions.cotangent_paired_partial_sums_type := by
  exact cotangent_paired_locally_uniform.tendstoLocallyUniformlyOn_finsetRange

end D12Complex.CotangentPartialFractions
