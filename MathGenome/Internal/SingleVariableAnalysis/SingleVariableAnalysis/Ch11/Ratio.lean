import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Geometric
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Comparison
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Limsup
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Ratio

/-!
# Ratio test for ordinary scalar series

K03.11.ratio, paper.tex:1019–1027. The tail limsup and liminf are the
upstream extended-real bounds, with no global boundedness hypothesis.
The convergence proof compares magnitudes with a geometric series after
an arbitrary finite prefix. Divergence uses the necessary term limit,
so it excludes conditional ordinary convergence as well.
Comparison is a declared transitive dependency through Absolute; it supplies
the already proved harmonic and reciprocal-square behavior for the examples.
-/
namespace SingleVariableAnalysis

open scoped Topology

/-- A strict upper bound on the extended limsup bounds a tail by some 0 < q < 1. -/
theorem ratio_tail_upper_bound (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (h : sequenceLimsup r < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ SequenceEventually (fun n => r n ≤ q) := by
  obtain ⟨N, hN⟩ := iInf_lt_iff.mp h
  obtain ⟨q, hq, hq1⟩ := EReal.exists_between_coe_real hN
  have hle : ∀ n ≥ N, (r n : EReal) ≤ tailSupremum r N :=
    fun n hn => le_iSup_of_le n (le_iSup_of_le hn le_rfl)
  have hq0 : 0 < q := EReal.coe_lt_coe_iff.mp
    ((EReal.coe_le_coe (hr N)).trans_lt ((hle N le_rfl).trans_lt hq))
  refine ⟨q, hq0, ?_, N, fun n hn => ?_⟩
  · exact EReal.coe_lt_coe_iff.mp (by simpa using hq1)
  · exact EReal.coe_le_coe_iff.mp ((hle n hn).trans hq.le)

/-- A strict lower bound on the extended liminf gives the required tail bound. -/
theorem ratio_tail_lower_bound (r : ℕ → ℝ) (h : 1 < sequenceLiminf r) :
    SequenceEventually (fun n => 1 ≤ r n) := by
  obtain ⟨N, hN⟩ := lt_iSup_iff.mp h
  refine ⟨N, fun n hn => ?_⟩
  have hh := hN.trans_le (iInf_le_of_le n (iInf_le_of_le hn le_rfl))
  exact (EReal.coe_lt_coe_iff.mp (by simpa using hh)).le

/-- An eventual contraction of a nonnegative sequence gives an ordinary sum. -/
theorem nonnegative_series_of_eventual_contraction (b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (h : SequenceEventually (fun n => b (n+1) ≤ q * b n)) :
    RealSeriesConverges b := by
  obtain ⟨N, hN⟩ := h
  let C := b N / q^N
  have hgeom : ∀ n ≥ N, b n ≤ C * q^n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      dsimp [C]
      rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos hq0 N))]
    | succ n hn ih =>
      calc
        b (n+1) ≤ q * b n := hN n hn
        _ ≤ q * (C * q^n) := mul_le_mul_of_nonneg_left ih hq0.le
        _ = C * q^(n+1) := by rw [pow_succ]; ring
  apply real_series_comparison b (fun n => q^n) C
    ⟨0, fun n _ => hb n⟩ ⟨0, fun n _ => pow_nonneg hq0.le n⟩ ⟨N, hgeom⟩
  exact ⟨_, real_geometric_series_hasSum q (by rwa [abs_of_pos hq0])⟩

/-- A positive nondecreasing tail cannot have finite limit zero. -/
theorem not_zero_limit_of_eventual_growth (b : ℕ → ℝ)
    (hb : SequenceEventually (fun n => 0 < b n))
    (hg : SequenceEventually (fun n => b n ≤ b (n+1))) :
    ¬ RealSequenceConverges b 0 := by
  obtain ⟨N, hN⟩ := hb
  obtain ⟨M, hM⟩ := hg
  let K := max N M
  have hK : 0 < b K := hN K (le_max_left _ _)
  have hlower : ∀ n ≥ K, b K ≤ b n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact ih.trans (hM n ((le_max_right _ _).trans hn))
  intro hc
  obtain ⟨L, hL⟩ := hc (b K) hK
  have hh := hL (max L K) (le_max_left _ _)
  have hlo := hlower (max L K) (le_max_right _ _)
  have hpos := hK.trans_le hlo
  have hh' : b (max L K) < b K := by
    simpa only [sub_zero, abs_of_pos hpos] using hh
  exact not_lt_of_ge hlo hh'

theorem real_ratio_test (a : ℕ → ℝ)
    (ha : SequenceEventually (fun n => a n ≠ 0))
    (h : sequenceLimsup (fun n => |a (n+1) / a n|) < 1) :
    RealSeriesAbsolutelyConverges a ∧ RealSeriesConverges a := by
  obtain ⟨q, hq0, hq1, N, hN⟩ := ratio_tail_upper_bound _ (fun n => abs_nonneg _) h
  obtain ⟨M, hM⟩ := ha
  have habs : RealSeriesAbsolutelyConverges a := by
    apply nonnegative_series_of_eventual_contraction _ (fun n => abs_nonneg _) q hq0 hq1
    refine ⟨max N M, fun n hn => ?_⟩
    have hh := hN n ((le_max_left _ _).trans hn)
    dsimp only at hh
    rw [abs_div] at hh
    exact (div_le_iff₀ (abs_pos.mpr (hM n ((le_max_right _ _).trans hn)))).mp hh
  exact ⟨habs, real_absolute_converges a habs⟩

theorem complex_ratio_test (a : ℕ → ℂ)
    (ha : SequenceEventually (fun n => a n ≠ 0))
    (h : sequenceLimsup (fun n => ‖a (n+1) / a n‖) < 1) :
    ComplexSeriesAbsolutelyConverges a ∧ ComplexSeriesConverges a := by
  obtain ⟨q, hq0, hq1, N, hN⟩ := ratio_tail_upper_bound _ (fun n => norm_nonneg _) h
  obtain ⟨M, hM⟩ := ha
  have habs : ComplexSeriesAbsolutelyConverges a := by
    apply nonnegative_series_of_eventual_contraction _ (fun n => norm_nonneg _) q hq0 hq1
    refine ⟨max N M, fun n hn => ?_⟩
    have hh := hN n ((le_max_left _ _).trans hn)
    dsimp only at hh
    rw [norm_div] at hh
    exact (div_le_iff₀ (norm_pos_iff.mpr (hM n ((le_max_right _ _).trans hn)))).mp hh
  exact ⟨habs, complex_absolute_converges a habs⟩

theorem real_ratio_divergence (a : ℕ → ℝ)
    (ha : SequenceEventually (fun n => a n ≠ 0))
    (h : SequenceEventually (fun n => 1 ≤ |a (n+1) / a n|)) :
    RealSeriesDiverges a := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := h
  intro hc
  apply not_zero_limit_of_eventual_growth (fun n => |a n|)
    ⟨N, fun n hn => abs_pos.mpr (hN n hn)⟩ ?_
    (by simpa only [abs_zero] using real_abs a 0 (real_series_term_limit a hc))
  refine ⟨max N M, fun n hn => ?_⟩
  have hh := hM n ((le_max_right _ _).trans hn)
  dsimp only at hh
  rw [abs_div, le_div_iff₀ (abs_pos.mpr (hN n ((le_max_left _ _).trans hn))), one_mul] at hh
  exact hh

theorem complex_ratio_divergence (a : ℕ → ℂ)
    (ha : SequenceEventually (fun n => a n ≠ 0))
    (h : SequenceEventually (fun n => 1 ≤ ‖a (n+1) / a n‖)) :
    ComplexSeriesDiverges a := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := h
  intro hc
  apply not_zero_limit_of_eventual_growth (fun n => ‖a n‖)
    ⟨N, fun n hn => norm_pos_iff.mpr (hN n hn)⟩ ?_
    (by simpa only [norm_zero] using complex_norm a 0 (complex_series_term_limit a hc))
  refine ⟨max N M, fun n hn => ?_⟩
  have hh := hM n ((le_max_right _ _).trans hn)
  dsimp only at hh
  rw [norm_div, le_div_iff₀ (norm_pos_iff.mpr (hN n ((le_max_left _ _).trans hn))), one_mul] at hh
  exact hh

theorem real_liminf_ratio_divergence (a : ℕ → ℝ)
    (ha : SequenceEventually (fun n => a n ≠ 0))
    (h : 1 < sequenceLiminf (fun n => |a (n+1) / a n|)) :
    RealSeriesDiverges a :=
  real_ratio_divergence a ha (ratio_tail_lower_bound _ h)

theorem complex_liminf_ratio_divergence (a : ℕ → ℂ)
    (ha : SequenceEventually (fun n => a n ≠ 0))
    (h : 1 < sequenceLiminf (fun n => ‖a (n+1) / a n‖)) :
    ComplexSeriesDiverges a :=
  complex_ratio_divergence a ha (ratio_tail_lower_bound _ h)

/-- The harmonic and reciprocal-square series have ratio limit one and different behavior. -/
theorem ratio_limit_one_examples :
    (∀ n : ℕ, 1 / ((n : ℝ)+1) ≠ 0 ∧ 1 / ((n : ℝ)+1)^2 ≠ 0) ∧
    RealSequenceConverges
      (fun n : ℕ => |(1 / (((n+1 : ℕ) : ℝ)+1)) / (1 / ((n : ℝ)+1))|) 1 ∧
    RealSequenceConverges
      (fun n : ℕ => |(1 / (((n+1 : ℕ) : ℝ)+1)^2) / (1 / ((n : ℝ)+1)^2)|) 1 ∧
    RealSeriesDiverges (fun n : ℕ => 1 / ((n : ℝ)+1)) ∧
    RealSeriesAbsolutelyConverges (fun n : ℕ => 1 / ((n : ℝ)+1)^2) := by
  have hbase : Filter.Tendsto (fun n : ℕ => ((n : ℝ)+1) / ((n : ℝ)+2))
      Filter.atTop (𝓝 (1 : ℝ)) := by
    have hi := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
    have ht : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (((n+1 : ℕ) : ℝ)+1))
        Filter.atTop (𝓝 (1 - 0 : ℝ)) := tendsto_const_nhds.sub hi
    convert ht using 1
    · funext n
      simp only [Nat.cast_add, Nat.cast_one]
      have hn : (n : ℝ)+2 ≠ 0 := by positivity
      have he : (n : ℝ)+1+1 = (n : ℝ)+2 := by ring
      rw [he]
      field_simp
      ring
    · norm_num
  have heq (n : ℕ) :
      |(1 / (((n+1 : ℕ) : ℝ)+1)) / (1 / ((n : ℝ)+1))| =
        ((n : ℝ)+1) / ((n : ℝ)+2) := by
    rw [abs_of_pos (by positivity)]
    push_cast
    have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
    have hn2 : (n : ℝ)+1+1 ≠ 0 := by positivity
    have hn3 : (n : ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring
  have heq2 (n : ℕ) :
      |(1 / (((n+1 : ℕ) : ℝ)+1)^2) / (1 / ((n : ℝ)+1)^2)| =
        (((n : ℝ)+1) / ((n : ℝ)+2))^2 := by
    rw [abs_of_pos (by positivity)]
    push_cast
    have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
    have hn2 : (n : ℝ)+1+1 ≠ 0 := by positivity
    have hn3 : (n : ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring
  refine ⟨fun n => ⟨by positivity, by positivity⟩, ?_, ?_,
    comparison_harmonic_diverges, ?_⟩
  · exact (realSequenceConverges_iff _ _).mpr (hbase.congr fun n => (heq n).symm)
  · apply (realSequenceConverges_iff _ _).mpr
    simpa only [one_pow] using (hbase.pow 2).congr (fun n => (heq2 n).symm)
  · change RealSeriesConverges (fun n : ℕ => |1 / ((n : ℝ)+1)^2|)
    convert comparison_reciprocal_square_converges using 1
    funext n
    rw [abs_of_pos (by positivity)]

end SingleVariableAnalysis
