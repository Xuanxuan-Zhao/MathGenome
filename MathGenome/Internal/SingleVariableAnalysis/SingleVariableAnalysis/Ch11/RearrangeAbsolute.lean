import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Subsequence
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.RearrangeAbsolute
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Grouping and absolutely convergent rearrangements

For K03.11.rearrange_absolute, all hypotheses and conclusions use ordinary
ordered series. Grouping is proved by a finite telescoping identity and a
cofinal subsequence of partial sums, so conditional convergence is allowed.
For rearrangements, we first bridge ordinary convergence of the nonnegative
norm series to Mathlib's HasSum. Only under that established hypothesis do
we bridge the scalar series to HasSum and apply bijective reindexing.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology

/-- Removing the initial empty partial sum does not change a finite limit. -/
theorem tendsto_sum_range_iff_inclusive {A : Type*} [AddCommMonoid A]
    [TopologicalSpace A] (a : ℕ → A) (S : A) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, a n) Filter.atTop (𝓝 S) ↔
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), a n) Filter.atTop (𝓝 S) :=
  (Filter.tendsto_add_atTop_iff_nat 1).symm

/-- Consecutive blocks telescope exactly, before taking any limit. -/
theorem sum_consecutive_blocks {A : Type*} [AddCommMonoid A]
    (a : ℕ → A) (k : ℕ → ℕ) (hk : StrictMono k) (h0 : k 0 = 0) (N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ n ∈ Finset.Ico (k j) (k (j + 1)), a n) =
      ∑ n ∈ Finset.range (k N), a n := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive a (Nat.zero_le _) (hk.monotone (Nat.le_succ N)),
      ← Finset.range_eq_Ico]

theorem real_series_grouping (a : ℕ → ℝ) (S : ℝ)
    (ha : RealSeriesHasSum a S) (k : ℕ → ℕ) (hk : StrictMono k) (h0 : k 0 = 0) :
    RealSeriesHasSum (fun j => ∑ n ∈ Finset.Ico (k j) (k (j + 1)), a n) S := by
  apply (realSequenceConverges_iff _ _).mpr
  have ht := (tendsto_sum_range_iff_inclusive a S).mpr
    ((realSequenceConverges_iff _ _).mp ha)
  have h := ht.comp (hk.tendsto_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  change Filter.Tendsto (fun N => ∑ j ∈ Finset.range (N + 1),
    ∑ n ∈ Finset.Ico (k j) (k (j + 1)), a n) Filter.atTop (𝓝 S)
  simpa only [Function.comp_def, sum_consecutive_blocks a k hk h0] using h

theorem complex_series_grouping (a : ℕ → ℂ) (S : ℂ)
    (ha : ComplexSeriesHasSum a S) (k : ℕ → ℕ) (hk : StrictMono k) (h0 : k 0 = 0) :
    ComplexSeriesHasSum (fun j => ∑ n ∈ Finset.Ico (k j) (k (j + 1)), a n) S := by
  apply (complexSequenceConverges_iff _ _).mpr
  have ht := (tendsto_sum_range_iff_inclusive a S).mpr
    ((complexSequenceConverges_iff _ _).mp ha)
  have h := ht.comp (hk.tendsto_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  change Filter.Tendsto (fun N => ∑ j ∈ Finset.range (N + 1),
    ∑ n ∈ Finset.Ico (k j) (k (j + 1)), a n) Filter.atTop (𝓝 S)
  simpa only [Function.comp_def, sum_consecutive_blocks a k hk h0] using h

/-- For nonnegative real terms ordinary convergence yields unconditional HasSum. -/
theorem real_nonnegative_hasSum_of_series (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (S : ℝ) (hS : RealSeriesHasSum a S) : HasSum a S := by
  apply (hasSum_iff_tendsto_nat_of_nonneg ha S).mpr
  exact (tendsto_sum_range_iff_inclusive a S).mpr
    ((realSequenceConverges_iff _ _).mp hS)

/-- A library HasSum always yields the ordinary real series sum. -/
theorem real_series_hasSum_of_hasSum (a : ℕ → ℝ) (S : ℝ) (h : HasSum a S) :
    RealSeriesHasSum a S := by
  apply (realSequenceConverges_iff _ _).mpr
  exact (tendsto_sum_range_iff_inclusive a S).mp h.tendsto_sum_nat

/-- A library HasSum always yields the ordinary complex series sum. -/
theorem complex_series_hasSum_of_hasSum (a : ℕ → ℂ) (S : ℂ) (h : HasSum a S) :
    ComplexSeriesHasSum a S := by
  apply (complexSequenceConverges_iff _ _).mpr
  exact (tendsto_sum_range_iff_inclusive a S).mp h.tendsto_sum_nat

theorem real_absolute_rearrangement (a : ℕ → ℝ) (S : ℝ)
    (ha : RealSeriesAbsolutelyConverges a) (hS : RealSeriesHasSum a S)
    (π : Equiv.Perm ℕ) :
    RealSeriesAbsolutelyConverges (a ∘ π) ∧ RealSeriesHasSum (a ∘ π) S := by
  obtain ⟨A, hA⟩ := ha
  have hm : HasSum (fun n => |a n|) A :=
    real_nonnegative_hasSum_of_series _ (fun n => abs_nonneg _) A hA
  have hn : Summable (fun n => ‖a n‖) := by simpa only [Real.norm_eq_abs] using hm.summable
  have hs : HasSum a S := (hasSum_iff_tendsto_nat_of_summable_norm hn).mpr
    ((tendsto_sum_range_iff_inclusive a S).mpr ((realSequenceConverges_iff _ _).mp hS))
  exact ⟨⟨A, real_series_hasSum_of_hasSum _ A (π.hasSum_iff.mpr hm)⟩,
    real_series_hasSum_of_hasSum _ S (π.hasSum_iff.mpr hs)⟩

theorem complex_absolute_rearrangement (a : ℕ → ℂ) (S : ℂ)
    (ha : ComplexSeriesAbsolutelyConverges a) (hS : ComplexSeriesHasSum a S)
    (π : Equiv.Perm ℕ) :
    ComplexSeriesAbsolutelyConverges (a ∘ π) ∧ ComplexSeriesHasSum (a ∘ π) S := by
  obtain ⟨A, hA⟩ := ha
  have hm : HasSum (fun n => ‖a n‖) A :=
    real_nonnegative_hasSum_of_series _ (fun n => norm_nonneg _) A hA
  have hs : HasSum a S := (hasSum_iff_tendsto_nat_of_summable_norm hm.summable).mpr
    ((tendsto_sum_range_iff_inclusive a S).mpr ((complexSequenceConverges_iff _ _).mp hS))
  exact ⟨⟨A, real_series_hasSum_of_hasSum _ A (π.hasSum_iff.mpr hm)⟩,
    complex_series_hasSum_of_hasSum _ S (π.hasSum_iff.mpr hs)⟩

end SingleVariableAnalysis
