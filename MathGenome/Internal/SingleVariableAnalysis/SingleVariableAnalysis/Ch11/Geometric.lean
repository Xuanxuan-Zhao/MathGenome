import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Necessary
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.StandardLimits
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Geometric
import Mathlib.Algebra.Ring.GeomSum

/-!
# Geometric series for real and complex ratios

K03.11.geometric_p, paper.tex:1011–1020 (geometric-series assertion).
The inclusive partial sums are those of the upstream ordinary series interface.
For ratios of modulus less than one, finite geometric algebra and the upstream
geometric decay theorem give their limit. For all other ratios, every term has
modulus at least one, contradicting the upstream necessary term limit.

The finite identity below is Mathlib's `geom_sum_mul_neg` divided by the
nonzero scalar `1 - q`. The analytic inputs are the upstream geometric decay
and term test; this argument uses no real-power or transcendental prerequisite.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology

/-- Finite geometric algebra in the form used for the partial-sum limit. -/
theorem geometric_sum_range {K : Type*} [Field K] (q : K) (hq : q ≠ 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, q ^ j) = (1 - q ^ n) / (1 - q) := by
  exact (eq_div_iff (sub_ne_zero.mpr (Ne.symm hq))).mpr (geom_sum_mul_neg q n)

theorem real_geometric_series_hasSum (q : ℝ) (hq : |q| < 1) :
    RealSeriesHasSum (fun n => q ^ n) (1 / (1 - q)) := by
  have hne : q ≠ 1 := by
    intro h
    simp only [h, abs_one, lt_self_iff_false] at hq
  have hd := (realSequenceConverges_iff _ _).mp (real_geometric_decay q hq)
  have ht : Filter.Tendsto (fun N : ℕ => (1 - q ^ (N + 1)) / (1 - q))
      Filter.atTop (𝓝 ((1 - 0) / (1 - q))) :=
    (tendsto_const_nhds.sub hd).div_const (1 - q)
  apply (realSequenceConverges_iff _ _).mpr
  change Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range (N + 1), q ^ j)
    Filter.atTop (𝓝 (1 / (1 - q)))
  simpa only [sub_zero] using ht.congr
    (fun N => (geometric_sum_range q hne (N + 1)).symm)

theorem real_geometric_series_diverges (q : ℝ) (hq : 1 ≤ |q|) :
    RealSeriesDiverges (fun n => q ^ n) := by
  intro hc
  obtain ⟨N, hN⟩ := real_series_term_limit (fun n => q ^ n) hc 1 zero_lt_one
  have hsmall : |q| ^ N < 1 := by
    simpa only [sub_zero, abs_pow] using hN N le_rfl
  exact (not_lt_of_ge (one_le_pow₀ hq)) hsmall

theorem real_geometric_series_converges_iff (q : ℝ) :
    RealSeriesConverges (fun n => q ^ n) ↔ |q| < 1 := by
  constructor
  · intro hc
    by_contra h
    exact real_geometric_series_diverges q (le_of_not_gt h) hc
  · intro hq
    exact ⟨_, real_geometric_series_hasSum q hq⟩

theorem complex_geometric_series_hasSum (q : ℂ) (hq : ‖q‖ < 1) :
    ComplexSeriesHasSum (fun n => q ^ n) (1 / (1 - q)) := by
  have hne : q ≠ 1 := by
    intro h
    simp only [h, norm_one, lt_self_iff_false] at hq
  have hd := (complexSequenceConverges_iff _ _).mp (complex_geometric_decay q hq)
  have ht : Filter.Tendsto (fun N : ℕ => (1 - q ^ (N + 1)) / (1 - q))
      Filter.atTop (𝓝 ((1 - 0) / (1 - q))) :=
    (tendsto_const_nhds.sub hd).div_const (1 - q)
  apply (complexSequenceConverges_iff _ _).mpr
  change Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range (N + 1), q ^ j)
    Filter.atTop (𝓝 (1 / (1 - q)))
  simpa only [sub_zero] using ht.congr
    (fun N => (geometric_sum_range q hne (N + 1)).symm)

theorem complex_geometric_series_diverges (q : ℂ) (hq : 1 ≤ ‖q‖) :
    ComplexSeriesDiverges (fun n => q ^ n) := by
  intro hc
  obtain ⟨N, hN⟩ := complex_series_term_limit (fun n => q ^ n) hc 1 zero_lt_one
  have hsmall : ‖q‖ ^ N < 1 := by
    simpa only [sub_zero, norm_pow] using hN N le_rfl
  exact (not_lt_of_ge (one_le_pow₀ hq)) hsmall

theorem complex_geometric_series_converges_iff (q : ℂ) :
    ComplexSeriesConverges (fun n => q ^ n) ↔ ‖q‖ < 1 := by
  constructor
  · intro hc
    by_contra h
    exact complex_geometric_series_diverges q (le_of_not_gt h) hc
  · intro hq
    exact ⟨_, complex_geometric_series_hasSum q hq⟩

end SingleVariableAnalysis
