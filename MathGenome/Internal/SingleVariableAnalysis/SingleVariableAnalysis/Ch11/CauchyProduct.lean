import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.CauchyProduct
import Mathlib.Algebra.Order.CauSeq.BigOperators
import Mathlib.Topology.MetricSpace.CauSeqFilter
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Cauchy products and Mertens' theorem

K03.11.cauchy_product, paper.tex:1111–1124, for both canonical scalar fields.
Mathlib's `cauchy_product` bounds the difference between rectangular and
triangular finite sums using absolute Cauchy convergence of the first factor
and ordinary Cauchy convergence of the second. Combining that zero error
with convergence of the rectangular products proves Mertens without imposing
absolute convergence on the second factor.

For the separate absolute-convergence assertion, nonnegative ordinary sums
are identified with Mathlib summability, and the normed-ring convolution
bound is used. All conclusions are converted back to the upstream ordinary
inclusive partial-sum predicates.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology
open Filter

/-- Coefficient of total degree n in the real Cauchy product. -/
noncomputable def realCauchyProduct (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- Coefficient of total degree n in the complex Cauchy product. -/
noncomputable def complexCauchyProduct (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- Mertens' finite-sum limit argument, before choosing the scalar field.
The ordinary limit of the second factor is sufficient. -/
theorem mertens_tendsto {K : Type*} [NormedField K] (a b : ℕ → K) (A B : K)
    (ha : ∃ S : ℝ, Tendsto (fun N => ∑ k ∈ Finset.range N, ‖a k‖) atTop (𝓝 S))
    (hA : Tendsto (fun N => ∑ k ∈ Finset.range N, a k) atTop (𝓝 A))
    (hB : Tendsto (fun N => ∑ k ∈ Finset.range N, b k) atTop (𝓝 B)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) atTop (𝓝 (A * B)) := by
  obtain ⟨S, hS⟩ := ha
  have hca : IsCauSeq abs (fun N => ∑ k ∈ Finset.range N, ‖a k‖) := by
    simpa only [show (norm : ℝ → ℝ) = abs from funext Real.norm_eq_abs] using
      hS.cauchySeq.isCauSeq
  have hcb : IsCauSeq norm (fun N => ∑ k ∈ Finset.range N, b k) :=
    hB.cauchySeq.isCauSeq
  have hz : Tendsto (fun N =>
      (∑ k ∈ Finset.range N, a k) * (∑ k ∈ Finset.range N, b k) -
        ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n + 1), a k * b (n - k))
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    simpa only [dist_eq_norm, sub_zero] using (_root_.cauchy_product hca hcb ε hε)
  simpa only [sub_sub_cancel, sub_zero] using (hA.mul hB).sub hz

private theorem real_hasSum_range (a : ℕ → ℝ) (S : ℝ)
    (h : RealSeriesHasSum a S) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, a k) atTop (𝓝 S) :=
  (tendsto_add_atTop_iff_nat 1).mp ((realSequenceConverges_iff _ _).mp h)

private theorem complex_hasSum_range (a : ℕ → ℂ) (S : ℂ)
    (h : ComplexSeriesHasSum a S) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, a k) atTop (𝓝 S) :=
  (tendsto_add_atTop_iff_nat 1).mp ((complexSequenceConverges_iff _ _).mp h)

/-- Real Mertens theorem: the second series may be conditional. -/
theorem real_mertens (a b : ℕ → ℝ) (A B : ℝ)
    (ha : RealSeriesAbsolutelyConverges a) (hA : RealSeriesHasSum a A)
    (hB : RealSeriesHasSum b B) : RealSeriesHasSum (realCauchyProduct a b) (A * B) := by
  obtain ⟨S, hS⟩ := ha
  have habs : ∃ S : ℝ, Tendsto (fun N => ∑ k ∈ Finset.range N, ‖a k‖) atTop (𝓝 S) :=
    ⟨S, by simpa only [Real.norm_eq_abs] using real_hasSum_range _ _ hS⟩
  exact (realSequenceConverges_iff _ _).mpr
    ((tendsto_add_atTop_iff_nat 1).mpr
      (mertens_tendsto a b A B habs (real_hasSum_range _ _ hA) (real_hasSum_range _ _ hB)))

/-- Complex Mertens theorem with ordinary convergence of the second series. -/
theorem complex_mertens (a b : ℕ → ℂ) (A B : ℂ)
    (ha : ComplexSeriesAbsolutelyConverges a) (hA : ComplexSeriesHasSum a A)
    (hB : ComplexSeriesHasSum b B) :
    ComplexSeriesHasSum (complexCauchyProduct a b) (A * B) := by
  obtain ⟨S, hS⟩ := ha
  exact (complexSequenceConverges_iff _ _).mpr
    ((tendsto_add_atTop_iff_nat 1).mpr
      (mertens_tendsto a b A B ⟨S, real_hasSum_range _ _ hS⟩
        (complex_hasSum_range _ _ hA) (complex_hasSum_range _ _ hB)))

private theorem summable_of_real_nonnegative_series (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (h : RealSeriesConverges a) : Summable a := by
  obtain ⟨S, hS⟩ := h
  exact ((hasSum_iff_tendsto_nat_of_nonneg ha S).mpr (real_hasSum_range _ _ hS)).summable

private theorem real_series_of_summable (a : ℕ → ℝ) (h : Summable a) :
    RealSeriesConverges a := by
  refine ⟨∑' n, a n, (realSequenceConverges_iff _ _).mpr ?_⟩
  exact (tendsto_add_atTop_iff_nat 1).mpr h.hasSum.tendsto_sum_nat

/-- Two absolutely convergent real factors have an absolutely convergent product. -/
theorem real_cauchyProduct_absolute (a b : ℕ → ℝ)
    (ha : RealSeriesAbsolutelyConverges a) (hb : RealSeriesAbsolutelyConverges b) :
    RealSeriesAbsolutelyConverges (realCauchyProduct a b) := by
  have hna : Summable (fun n => ‖a n‖) := by
    simpa only [Real.norm_eq_abs] using
      summable_of_real_nonnegative_series (fun n => |a n|) (fun n => abs_nonneg _) ha
  have hnb : Summable (fun n => ‖b n‖) := by
    simpa only [Real.norm_eq_abs] using
      summable_of_real_nonnegative_series (fun n => |b n|) (fun n => abs_nonneg _) hb
  apply real_series_of_summable
  simpa only [realCauchyProduct, Real.norm_eq_abs] using
    summable_norm_sum_mul_range_of_summable_norm hna hnb

/-- Two absolutely convergent complex factors have an absolutely convergent product. -/
theorem complex_cauchyProduct_absolute (a b : ℕ → ℂ)
    (ha : ComplexSeriesAbsolutelyConverges a) (hb : ComplexSeriesAbsolutelyConverges b) :
    ComplexSeriesAbsolutelyConverges (complexCauchyProduct a b) := by
  have hna := summable_of_real_nonnegative_series (fun n => ‖a n‖) (fun n => norm_nonneg _) ha
  have hnb := summable_of_real_nonnegative_series (fun n => ‖b n‖) (fun n => norm_nonneg _) hb
  exact real_series_of_summable _ (summable_norm_sum_mul_range_of_summable_norm hna hnb)

end SingleVariableAnalysis
