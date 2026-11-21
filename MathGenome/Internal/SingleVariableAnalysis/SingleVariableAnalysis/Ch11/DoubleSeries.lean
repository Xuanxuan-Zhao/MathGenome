import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.DoubleSeries

/-!
# Double series and summation order

K03.11.double_series (paper.tex:1130–1137). The ENNReal product and
reindexing formulas include infinite nonnegative sums. In the scalar case
we derive summability of the norm family from the finite extended sum,
then use the complete-group product-sum theorems. Explicit bridges turn
these sums into ordinary inclusive partial-sum limits. The signed example
is handled separately through its finitely supported rows and columns.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology ENNReal

/-- The finite-subset, iterated, and enumerated extended sums all agree. -/
theorem nonnegative_double_series (a : ℕ → ℕ → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    nonnegativeExtendedSum (fun p : ℕ × ℕ => a p.1 p.2) =
      (⨆ F : Finset (ℕ × ℕ), ENNReal.ofReal (∑ p ∈ F, a p.1 p.2)) ∧
    (∑' i, nonnegativeExtendedSum (a i)) =
      nonnegativeExtendedSum (fun p : ℕ × ℕ => a p.1 p.2) ∧
    (∑' j, nonnegativeExtendedSum (fun i => a i j)) =
      nonnegativeExtendedSum (fun p : ℕ × ℕ => a p.1 p.2) ∧
    ∀ e : ℕ ≃ (ℕ × ℕ),
      nonnegativeExtendedSum (fun n => a (e n).1 (e n).2) =
        nonnegativeExtendedSum (fun p : ℕ × ℕ => a p.1 p.2) := by
  refine ⟨nonnegative_extendedSum_finite_subsets _ (fun p => ha p.1 p.2), ?_, ?_, ?_⟩
  · exact ENNReal.tsum_prod.symm
  · exact ENNReal.tsum_comm.trans ENNReal.tsum_prod.symm
  · intro e
    exact nonnegative_extendedSum_reindex _ (fun p => ha p.1 p.2) e

/-- Unconditional summation implies the source's ordinary real series sum. -/
theorem real_series_hasSum_of_hasSum {a : ℕ → ℝ} {S : ℝ} (h : HasSum a S) :
    RealSeriesHasSum a S := by
  apply (realSequenceConverges_iff _ _).mpr
  change Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), a n) Filter.atTop (𝓝 S)
  exact h.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)

/-- The same bridge for real-variable sequences of complex scalars. -/
theorem complex_series_hasSum_of_hasSum {a : ℕ → ℂ} {S : ℂ} (h : HasSum a S) :
    ComplexSeriesHasSum a S := by
  apply (complexSequenceConverges_iff _ _).mpr
  change Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), a n) Filter.atTop (𝓝 S)
  exact h.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)

/-- Finiteness of the extended sum of norms is precisely norm summability. -/
theorem summable_norm_of_finite_extended_sum {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} (a : ι → E)
    (h : nonnegativeExtendedSum (fun i => ‖a i‖) < ∞) :
    Summable (fun i => ‖a i‖) := by
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  simpa only [nonnegativeExtendedSum, ofReal_norm] using ne_of_lt h

/-- Summing each row preserves absolute summability of the outer family. -/
theorem summable_norm_rows {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (a : ℕ → ℕ → E) (h : Summable (fun p : ℕ × ℕ => ‖a p.1 p.2‖)) :
    Summable (fun i => ‖∑' j, a i j‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => norm_tsum_le_tsum_norm (h.prod_factor i)) h.prod

/-- All real scalar sums under exactly the finite absolute-double-sum hypothesis. -/
theorem real_absolute_double_series (a : ℕ → ℕ → ℝ)
    (ha : nonnegativeExtendedSum (fun p : ℕ × ℕ => |a p.1 p.2|) < ∞) :
    let S := ∑' p : ℕ × ℕ, a p.1 p.2
    HasSum (fun p : ℕ × ℕ => a p.1 p.2) S ∧
    (∀ i, RealSeriesAbsolutelyConverges (a i) ∧
      RealSeriesHasSum (a i) (∑' j, a i j)) ∧
    (∀ j, RealSeriesAbsolutelyConverges (fun i => a i j) ∧
      RealSeriesHasSum (fun i => a i j) (∑' i, a i j)) ∧
    RealSeriesAbsolutelyConverges (fun i => ∑' j, a i j) ∧
    RealSeriesHasSum (fun i => ∑' j, a i j) S ∧
    RealSeriesAbsolutelyConverges (fun j => ∑' i, a i j) ∧
    RealSeriesHasSum (fun j => ∑' i, a i j) S ∧
    ∀ e : ℕ ≃ (ℕ × ℕ),
      RealSeriesAbsolutelyConverges (fun n => a (e n).1 (e n).2) ∧
      RealSeriesHasSum (fun n => a (e n).1 (e n).2) S := by
  have hn : Summable (fun p : ℕ × ℕ => ‖a p.1 p.2‖) :=
    summable_norm_of_finite_extended_sum _ (by simpa only [Real.norm_eq_abs] using ha)
  have hs := hn.of_norm
  have hrn := summable_norm_rows a hn
  have hcn := summable_norm_rows (fun j i => a i j) hn.prod_symm
  dsimp only
  refine ⟨hs.hasSum, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, real_series_hasSum_of_hasSum (hs.prod_factor i).hasSum⟩
    exact ⟨_, real_series_hasSum_of_hasSum (by simpa only [Real.norm_eq_abs] using
      (hn.prod_factor i).hasSum)⟩
  · intro j
    refine ⟨?_, real_series_hasSum_of_hasSum (hs.prod_symm.prod_factor j).hasSum⟩
    exact ⟨_, real_series_hasSum_of_hasSum (by simpa only [Real.norm_eq_abs, Prod.swap] using
      (hn.prod_symm.prod_factor j).hasSum)⟩
  · exact ⟨_, real_series_hasSum_of_hasSum (by simpa only [Real.norm_eq_abs] using
      hrn.hasSum)⟩
  · rw [hs.tsum_prod]
    exact real_series_hasSum_of_hasSum hs.prod.hasSum
  · exact ⟨_, real_series_hasSum_of_hasSum (by simpa only [Real.norm_eq_abs] using
      hcn.hasSum)⟩
  · rw [hs.tsum_prod, ← hs.tsum_comm]
    exact real_series_hasSum_of_hasSum hs.prod_symm.prod.hasSum
  · intro e
    refine ⟨?_, real_series_hasSum_of_hasSum (e.hasSum_iff.mpr hs.hasSum)⟩
    exact ⟨_, real_series_hasSum_of_hasSum (by simpa only [Real.norm_eq_abs, Function.comp_def] using
      (hn.comp_injective e.injective).hasSum)⟩

/-- All complex scalar sums, with ordinary limits and the same finite hypothesis. -/
theorem complex_absolute_double_series (a : ℕ → ℕ → ℂ)
    (ha : nonnegativeExtendedSum (fun p : ℕ × ℕ => ‖a p.1 p.2‖) < ∞) :
    let S := ∑' p : ℕ × ℕ, a p.1 p.2
    HasSum (fun p : ℕ × ℕ => a p.1 p.2) S ∧
    (∀ i, ComplexSeriesAbsolutelyConverges (a i) ∧
      ComplexSeriesHasSum (a i) (∑' j, a i j)) ∧
    (∀ j, ComplexSeriesAbsolutelyConverges (fun i => a i j) ∧
      ComplexSeriesHasSum (fun i => a i j) (∑' i, a i j)) ∧
    ComplexSeriesAbsolutelyConverges (fun i => ∑' j, a i j) ∧
    ComplexSeriesHasSum (fun i => ∑' j, a i j) S ∧
    ComplexSeriesAbsolutelyConverges (fun j => ∑' i, a i j) ∧
    ComplexSeriesHasSum (fun j => ∑' i, a i j) S ∧
    ∀ e : ℕ ≃ (ℕ × ℕ),
      ComplexSeriesAbsolutelyConverges (fun n => a (e n).1 (e n).2) ∧
      ComplexSeriesHasSum (fun n => a (e n).1 (e n).2) S := by
  have hn := summable_norm_of_finite_extended_sum _ ha
  have hs := hn.of_norm
  have hrn := summable_norm_rows a hn
  have hcn := summable_norm_rows (fun j i => a i j) hn.prod_symm
  dsimp only
  refine ⟨hs.hasSum, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨⟨_, real_series_hasSum_of_hasSum (hn.prod_factor i).hasSum⟩,
      complex_series_hasSum_of_hasSum (hs.prod_factor i).hasSum⟩
  · intro j
    exact ⟨⟨_, real_series_hasSum_of_hasSum (hn.prod_symm.prod_factor j).hasSum⟩,
      complex_series_hasSum_of_hasSum (hs.prod_symm.prod_factor j).hasSum⟩
  · exact ⟨_, real_series_hasSum_of_hasSum hrn.hasSum⟩
  · rw [hs.tsum_prod]
    exact complex_series_hasSum_of_hasSum hs.prod.hasSum
  · exact ⟨_, real_series_hasSum_of_hasSum hcn.hasSum⟩
  · rw [hs.tsum_prod, ← hs.tsum_comm]
    exact complex_series_hasSum_of_hasSum hs.prod_symm.prod.hasSum
  · intro e
    exact ⟨⟨_, real_series_hasSum_of_hasSum (hn.comp_injective e.injective).hasSum⟩,
      complex_series_hasSum_of_hasSum (e.hasSum_iff.mpr hs.hasSum)⟩

/-- The source counterexample: a diagonal 1 and a superdiagonal -1. -/
def doubleSeriesOrderExample (i j : ℕ) : ℝ :=
  if j = i then 1 else if j = i + 1 then -1 else 0

/-- The row contains precisely two nonzero terms, which cancel. -/
theorem doubleSeries_order_example_rows (i : ℕ) :
    RealSeriesHasSum (doubleSeriesOrderExample i) 0 := by
  apply real_series_hasSum_of_hasSum
  have h := (hasSum_ite_eq i (1 : ℝ)).sub (hasSum_ite_eq (i + 1) (1 : ℝ))
  have he : (fun j => (if j = i then (1 : ℝ) else 0) -
      (if j = i + 1 then 1 else 0)) = doubleSeriesOrderExample i := by
    funext j
    by_cases hji : j = i
    · simp [doubleSeriesOrderExample, hji]
    · by_cases hnext : j = i + 1 <;> simp [doubleSeriesOrderExample, hji, hnext]
  simpa only [he, sub_self] using h

/-- The first column sums to 1; every later column sums to zero. -/
theorem doubleSeries_order_example_columns (j : ℕ) :
    RealSeriesHasSum (fun i => doubleSeriesOrderExample i j)
      (if j = 0 then 1 else 0) := by
  apply real_series_hasSum_of_hasSum
  cases j with
  | zero =>
    convert hasSum_ite_eq 0 (1 : ℝ) using 1
    · funext i
      simp [doubleSeriesOrderExample, eq_comm]
    · norm_num
  | succ j =>
    have h := (hasSum_ite_eq (j + 1) (1 : ℝ)).sub (hasSum_ite_eq j (1 : ℝ))
    have he : (fun i => (if i = j + 1 then (1 : ℝ) else 0) -
        (if i = j then 1 else 0)) = (fun i => doubleSeriesOrderExample i (j + 1)) := by
      funext i
      by_cases hij : i = j + 1
      · simp [doubleSeriesOrderExample, hij]
      · by_cases hne : i = j
        · subst i
          simp [doubleSeriesOrderExample]
        · simp [doubleSeriesOrderExample, hij, hne, Ne.symm hij, Ne.symm hne]
    simpa only [he, sub_self, Nat.succ_ne_zero, ite_false] using h

/-- The two genuine iterated ordinary series have the distinct sums 0 and 1. -/
theorem doubleSeries_order_example_iterated :
    (∀ i, RealSeriesHasSum (doubleSeriesOrderExample i) 0) ∧
    (∀ j, RealSeriesHasSum (fun i => doubleSeriesOrderExample i j)
      (if j = 0 then 1 else 0)) ∧
    RealSeriesHasSum (fun _ : ℕ => (0 : ℝ)) 0 ∧
    RealSeriesHasSum (fun j : ℕ => if j = 0 then (1 : ℝ) else 0) 1 ∧
    (0 : ℝ) ≠ 1 := by
  exact ⟨doubleSeries_order_example_rows, doubleSeries_order_example_columns,
    real_series_hasSum_of_hasSum hasSum_zero,
    real_series_hasSum_of_hasSum (hasSum_ite_eq 0 (1 : ℝ)), zero_ne_one⟩

/-- Already the diagonal magnitudes have infinite sum. -/
theorem doubleSeries_order_example_not_absolute :
    nonnegativeExtendedSum (fun p : ℕ × ℕ => |doubleSeriesOrderExample p.1 p.2|) = ∞ := by
  have hi : Function.Injective (fun n : ℕ => (n, n)) :=
    fun _ _ h => congrArg Prod.fst h
  have h := ENNReal.tsum_comp_le_tsum_of_injective hi
    (fun p : ℕ × ℕ => ENNReal.ofReal |doubleSeriesOrderExample p.1 p.2|)
  have hdiag : (∑' n : ℕ, ENNReal.ofReal |doubleSeriesOrderExample n n|) = ∞ := by
    simp [doubleSeriesOrderExample]
  exact top_unique (hdiag ▸ h)

end SingleVariableAnalysis
