import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Necessary
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Comparison
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.MTest

/-!
# Weierstrass' majorant test

`K03.12.m_test`, paper.tex:1277–1285, for both canonical scalar fields.
The triangle inequality bounds every inclusive finite tail by a tail of M.
The numerical Cauchy criterion supplies a common threshold, independent of
the point. Scalar completeness enters through the upstream uniform Cauchy
criteria, and numerical comparison gives pointwise absolute convergence.
Every argument works on an empty domain as well.
-/

namespace SingleVariableAnalysis

open scoped BigOperators

universe u v

private theorem uniform_partial_sums_cauchy_of_majorant
    {E : Type u} {K : Type v} [NormedAddCommGroup K]
    (u : ℕ → E → K) (M : ℕ → ℝ)
    (hb : ∀ n x, ‖u n x‖ ≤ M n) (hM : RealSeriesConverges M) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x,
      ‖(∑ i ∈ Finset.range (n + 1), u i x) -
        ∑ i ∈ Finset.range (m + 1), u i x‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := (real_series_cauchy_criterion M).mp hM ε hε
  have hlt : ∀ m ≥ N, ∀ n, m < n → ∀ x,
      ‖(∑ i ∈ Finset.range (n + 1), u i x) -
        ∑ i ∈ Finset.range (m + 1), u i x‖ < ε := by
    intro m hm n hmn x
    rw [← sum_Icc_eq_sub_sum_range (fun i => u i x) (Nat.succ_le_of_lt hmn)]
    calc
      ‖∑ i ∈ Finset.Icc (m + 1) n, u i x‖ ≤
          ∑ i ∈ Finset.Icc (m + 1) n, ‖u i x‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.Icc (m + 1) n, M i :=
        Finset.sum_le_sum (fun i _ => hb i x)
      _ ≤ |∑ i ∈ Finset.Icc (m + 1) n, M i| := le_abs_self _
      _ < ε := hN (m + 1) (hm.trans (Nat.le_succ m)) n (Nat.succ_le_of_lt hmn)
  refine ⟨N, ?_⟩
  intro m hm n hn x
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · exact hlt m hm n hmn x
  · subst n
    simpa using hε
  · rw [norm_sub_rev]
    exact hlt n hn m hmn x

theorem real_m_test {E : Type u} (u : ℕ → E → ℝ) (M : ℕ → ℝ)
    (_hM0 : ∀ n, 0 ≤ M n) (hb : ∀ n x, |u n x| ≤ M n)
    (hM : RealSeriesConverges M) :
    (∃ f : E → ℝ, RealUniformConverges
      (fun N x => realPartialSum (fun n => u n x) N) f) ∧
    (∃ g : E → ℝ, RealUniformConverges
      (fun N x => realPartialSum (fun n => |u n x|) N) g) ∧
    ∀ x, RealSeriesConverges (fun n => |u n x|) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (real_uniform_cauchy_criterion _).mpr
    simpa only [realPartialSum, Real.norm_eq_abs] using
      uniform_partial_sums_cauchy_of_majorant u M
        (by simpa only [Real.norm_eq_abs] using hb) hM
  · apply (real_uniform_cauchy_criterion _).mpr
    simpa only [realPartialSum, Real.norm_eq_abs] using
      uniform_partial_sums_cauchy_of_majorant (fun n x => |u n x|) M
        (by simpa only [Real.norm_eq_abs, abs_abs] using hb) hM
  · intro x
    exact real_series_comparison_of_nonnegative _ M (fun n => abs_nonneg _)
      (fun n => hb n x) hM

theorem complex_m_test {E : Type u} (u : ℕ → E → ℂ) (M : ℕ → ℝ)
    (_hM0 : ∀ n, 0 ≤ M n) (hb : ∀ n x, ‖u n x‖ ≤ M n)
    (hM : RealSeriesConverges M) :
    (∃ f : E → ℂ, ComplexUniformConverges
      (fun N x => complexPartialSum (fun n => u n x) N) f) ∧
    (∃ g : E → ℝ, RealUniformConverges
      (fun N x => realPartialSum (fun n => ‖u n x‖) N) g) ∧
    ∀ x, RealSeriesConverges (fun n => ‖u n x‖) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (complex_uniform_cauchy_criterion _).mpr
    exact uniform_partial_sums_cauchy_of_majorant u M hb hM
  · apply (real_uniform_cauchy_criterion _).mpr
    simpa only [realPartialSum, Real.norm_eq_abs] using
      uniform_partial_sums_cauchy_of_majorant (fun n x => ‖u n x‖) M
        (by simpa only [norm_norm] using hb) hM
  · intro x
    exact real_series_comparison_of_nonnegative _ M (fun n => norm_nonneg _)
      (fun n => hb n x) hM

end SingleVariableAnalysis
