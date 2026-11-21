import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Geometric
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Cesaro
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.AbelNotConverse

/-!
# Abel summability alone has no converse

K03.13.abel_not_converse, paper.tex:1509–1513.
For aₙ = (-1)^n, substitute q = -x in the upstream geometric-series
formula. The resulting sum function is 1/(1+x), continuous at x = 1
and with value 1/2 there. Uniqueness of ordinary series sums identifies
any representative of the power-series sum on [0,1) with this function.
The upstream Cesàro example gives the ordinary divergence; the exact
partial sums and |n aₙ| = n show explicitly why ordinary convergence and
Tauber's coefficient hypothesis both fail.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology

theorem real_alternating_power_series (x : ℝ) (hx : 0 ≤ x) (h1 : x < 1) :
    RealSeriesHasSum (fun n => (-1 : ℝ)^n * x^n) (1 / (1 + x)) := by
  have hq : |(-x)| < 1 := by simpa only [abs_neg, abs_of_nonneg hx] using h1
  have hterms : (fun n : ℕ => (-x)^n) = (fun n => (-1 : ℝ)^n * x^n) := by
    funext n
    exact neg_pow x n
  have h := real_geometric_series_hasSum (-x) hq
  rw [hterms, sub_neg_eq_add] at h
  exact h

theorem real_alternating_abel_limit (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 ≤ x → x < 1 →
      RealSeriesHasSum (fun n => (-1 : ℝ)^n * x^n) (f x)) :
    Filter.Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (1/2 : ℝ)) := by
  have hc : ContinuousAt (fun x : ℝ => 1 / (1 + x)) 1 :=
    continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)
  have ht : Filter.Tendsto (fun x : ℝ => 1 / (1 + x))
      (𝓝[<] (1 : ℝ)) (𝓝 (1/2 : ℝ)) := by
    convert hc.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ)) using 1; norm_num
  apply ht.congr'
  filter_upwards [Ico_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
  exact real_series_sum_unique _ _ _ (real_alternating_power_series x hx.1 hx.2)
    (hf x hx.1 hx.2)

theorem real_abel_counterexample_partial_sums (N : ℕ) :
    realPartialSum (fun n => (-1 : ℝ)^n) (2*N) = 1 ∧
    realPartialSum (fun n => (-1 : ℝ)^n) (2*N+1) = 0 := by
  constructor
  · rw [real_alternating_series_partialSum, Even.neg_one_pow ⟨N, by omega⟩]
    norm_num
  · rw [real_alternating_series_partialSum, Odd.neg_one_pow ⟨N, rfl⟩]
    norm_num

theorem real_abel_counterexample_diverges :
    RealSeriesDiverges (fun n => (-1 : ℝ)^n) :=
  real_alternating_series_diverges

theorem real_alternating_tauber_fails :
    ¬ RealSequenceConverges (fun n => (n : ℝ) * (-1 : ℝ)^n) 0 := by
  intro h
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  have habs (n : ℕ) : |(n : ℝ) * (-1 : ℝ)^n| = (n : ℝ) := by
    simp [abs_mul, abs_pow]
  have hs : ((N + 1 : ℕ) : ℝ) < 1 := by
    simpa only [sub_zero, habs] using hN (N + 1) (Nat.le_succ N)
  simp only [Nat.cast_add, Nat.cast_one] at hs
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

theorem complex_alternating_power_series (x : ℝ) (hx : 0 ≤ x) (h1 : x < 1) :
    ComplexSeriesHasSum (fun n => (-1 : ℂ)^n * (x : ℂ)^n)
      (1 / (1 + (x : ℂ))) := by
  have hq : ‖(-(x : ℂ))‖ < 1 := by
    simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] using h1
  have hterms : (fun n : ℕ => (-(x : ℂ))^n) =
      (fun n => (-1 : ℂ)^n * (x : ℂ)^n) := by
    funext n
    exact neg_pow (x : ℂ) n
  have h := complex_geometric_series_hasSum (-(x : ℂ)) hq
  rw [hterms, sub_neg_eq_add] at h
  exact h

theorem complex_alternating_abel_limit (f : ℝ → ℂ)
    (hf : ∀ x : ℝ, 0 ≤ x → x < 1 →
      ComplexSeriesHasSum (fun n => (-1 : ℂ)^n * (x : ℂ)^n) (f x)) :
    Filter.Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (1/2 : ℂ)) := by
  have hc : ContinuousAt (fun x : ℝ => 1 / (1 + (x : ℂ))) 1 :=
    continuousAt_const.div
      (continuousAt_const.add Complex.continuous_ofReal.continuousAt) (by norm_num)
  have ht : Filter.Tendsto (fun x : ℝ => 1 / (1 + (x : ℂ)))
      (𝓝[<] (1 : ℝ)) (𝓝 (1/2 : ℂ)) := by
    convert hc.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ)) using 1; norm_num
  apply ht.congr'
  filter_upwards [Ico_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
  exact complex_series_sum_unique _ _ _ (complex_alternating_power_series x hx.1 hx.2)
    (hf x hx.1 hx.2)

theorem complex_abel_counterexample_partial_sums (N : ℕ) :
    complexPartialSum (fun n => (-1 : ℂ)^n) (2*N) = 1 ∧
    complexPartialSum (fun n => (-1 : ℂ)^n) (2*N+1) = 0 := by
  constructor
  · change (∑ j ∈ Finset.range (2*N+1), (-1 : ℂ)^j) = 1
    rw [geometric_sum_range _ (by norm_num), Odd.neg_one_pow ⟨N, rfl⟩]
    norm_num
  · change (∑ j ∈ Finset.range (2*N+1+1), (-1 : ℂ)^j) = 0
    rw [geometric_sum_range _ (by norm_num), Even.neg_one_pow ⟨N+1, by omega⟩]
    norm_num

theorem complex_abel_counterexample_diverges :
    ComplexSeriesDiverges (fun n => (-1 : ℂ)^n) :=
  complex_alternating_series_diverges

theorem complex_alternating_tauber_fails :
    ¬ ComplexSequenceConverges (fun n => (n : ℂ) * (-1 : ℂ)^n) 0 := by
  intro h
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  have hnorm (n : ℕ) : ‖(n : ℂ) * (-1 : ℂ)^n‖ = (n : ℝ) := by
    simp [norm_pow]
  have hs : ((N + 1 : ℕ) : ℝ) < 1 := by
    simpa only [sub_zero, hnorm] using hN (N + 1) (Nat.le_succ N)
  simp only [Nat.cast_add, Nat.cast_one] at hs
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

end SingleVariableAnalysis
