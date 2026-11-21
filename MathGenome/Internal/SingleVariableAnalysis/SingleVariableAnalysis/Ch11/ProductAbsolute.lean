import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Absolute
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.ProductAbsolute
import Mathlib.Tactic.Linarith

/-!
# Absolutely convergent complex products

K03.11.product_absolute, paper.tex:1150–1165. The two finite bounds apply
also to empty sets, and in particular to every consecutive finite tail.
An induction proves the scaled error bound `(1 - T) * error ≤ sum`.
On tails of magnitude below one half it bounds the error by twice the sum.
The upstream ordinary-series Cauchy criterion then makes partial products
Cauchy, and the upstream complex completeness theorem supplies their limit.
The lower estimate and the fixed nonzero prefix keep this limit nonzero.
No logarithm, exponential, or infinite-product library theorem is used.
-/
namespace SingleVariableAnalysis
open scoped BigOperators Topology

private theorem product_error_scaled (u : ℕ → ℂ) (s : Finset ℕ) (T : ℝ)
    (hT : T < 1) (hs : (∑ j ∈ s, ‖u j‖) ≤ T) :
    (1 - T) * ‖(∏ j ∈ s, (1 + u j)) - 1‖ ≤ ∑ j ∈ s, ‖u j‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha] at hs ⊢
    rw [Finset.prod_insert ha]
    have hsum : 0 ≤ ∑ j ∈ s, ‖u j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hst : (∑ j ∈ s, ‖u j‖) ≤ T := by linarith [norm_nonneg (u a)]
    have hi := ih hst
    have herr : ‖(1 + u a) * (∏ j ∈ s, (1 + u j)) - 1‖ ≤
        (1 + ‖u a‖) * ‖(∏ j ∈ s, (1 + u j)) - 1‖ + ‖u a‖ := by
      calc
        _ = ‖(1 + u a) * ((∏ j ∈ s, (1 + u j)) - 1) + u a‖ := by congr 1; ring
        _ ≤ ‖(1 + u a) * ((∏ j ∈ s, (1 + u j)) - 1)‖ + ‖u a‖ := norm_add_le _ _
        _ = ‖1 + u a‖ * ‖(∏ j ∈ s, (1 + u j)) - 1‖ + ‖u a‖ := by rw [norm_mul]
        _ ≤ _ := by gcongr; simpa using norm_add_le (1 : ℂ) (u a)
    have hx := mul_le_mul_of_nonneg_left herr (by linarith : 0 ≤ 1 - T)
    have hy := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 + ‖u a‖)
    have hz := mul_nonneg (norm_nonneg (u a)) (sub_nonneg.mpr hst)
    nlinarith

theorem complex_finite_product_upper (u : ℕ → ℂ) (s : Finset ℕ)
    (hs : (∑ j ∈ s, ‖u j‖) < 1) :
    ‖(∏ j ∈ s, (1 + u j)) - 1‖ ≤
      (∑ j ∈ s, ‖u j‖) / (1 - ∑ j ∈ s, ‖u j‖) := by
  apply (le_div_iff₀ (sub_pos.mpr hs)).mpr
  simpa [mul_comm] using product_error_scaled u s _ hs le_rfl

theorem complex_finite_product_lower (u : ℕ → ℂ) (s : Finset ℕ)
    (hs : (∑ j ∈ s, ‖u j‖) < 1) :
    1 - (∑ j ∈ s, ‖u j‖) ≤ ‖∏ j ∈ s, (1 + u j)‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha] at hs ⊢
    rw [Finset.prod_insert ha, norm_mul]
    have hsum : 0 ≤ ∑ j ∈ s, ‖u j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hst : (∑ j ∈ s, ‖u j‖) < 1 := by linarith [norm_nonneg (u a)]
    have hi := ih hst
    have hnorm : 1 - ‖u a‖ ≤ ‖1 + u a‖ := by
      have := norm_sub_le (1 + u a) (u a)
      simp only [add_sub_cancel_right, norm_one] at this
      linarith
    have hmul := mul_le_mul hnorm hi (by linarith : 0 ≤ 1 - ∑ j ∈ s, ‖u j‖)
      (norm_nonneg (1 + u a))
    nlinarith [mul_nonneg (norm_nonneg (u a)) hsum]

private theorem product_error_le_twice (u : ℕ → ℂ) (s : Finset ℕ)
    (hs : (∑ j ∈ s, ‖u j‖) < 1 / 2) :
    ‖(∏ j ∈ s, (1 + u j)) - 1‖ ≤ 2 * ∑ j ∈ s, ‖u j‖ := by
  have h := product_error_scaled u s _ (by linarith : (∑ j ∈ s, ‖u j‖) < 1) le_rfl
  have hn := norm_nonneg ((∏ j ∈ s, (1 + u j)) - 1)
  nlinarith

private theorem magnitude_tails_small (u : ℕ → ℂ)
    (hu : ComplexSeriesAbsolutelyConverges u) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ p ≥ K, ∀ q ≥ p, (∑ j ∈ Finset.Ico p q, ‖u j‖) < δ := by
  obtain ⟨K, hK⟩ := (real_series_cauchy_criterion (fun n => ‖u n‖)).mp hu δ hδ
  refine ⟨K, fun p hp q hpq => ?_⟩
  calc
    _ ≤ ∑ j ∈ Finset.Icc p q, ‖u j‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by intro j hj; exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hj).1, (Finset.mem_Ico.mp hj).2.le⟩)
        (fun _ _ _ => norm_nonneg _)
    _ ≤ |∑ j ∈ Finset.Icc p q, ‖u j‖| := le_abs_self _
    _ < δ := hK p hp q hpq

theorem complex_absolute_product_converges (u : ℕ → ℂ)
    (hu : ComplexSeriesAbsolutelyConverges u) (hne : ∀ n, 1 + u n ≠ 0) :
    ∃ L : ℂ, L ≠ 0 ∧ ComplexSequenceConverges
      (fun N => ∏ n ∈ Finset.range (N + 1), (1 + u n)) L := by
  classical
  let P : ℕ → ℂ := fun n => ∏ j ∈ Finset.range n, (1 + u j)
  obtain ⟨K, hK⟩ := magnitude_tails_small u hu (1 / 2) (by norm_num)
  have hsplit (m n : ℕ) (hmn : m ≤ n) :
      P n = P m * ∏ j ∈ Finset.Ico m n, (1 + u j) :=
    (Finset.prod_range_mul_prod_Ico (fun j => 1 + u j) hmn).symm
  have hbound (n : ℕ) (hn : K ≤ n) : ‖P n‖ ≤ 2 * ‖P K‖ := by
    have ht := hK K le_rfl n hn
    have he := product_error_le_twice u (Finset.Ico K n) ht
    have hb : ‖∏ j ∈ Finset.Ico K n, (1 + u j)‖ ≤ 2 := by
      have hh := norm_add_le ((∏ j ∈ Finset.Ico K n, (1 + u j)) - 1) (1 : ℂ)
      simp only [sub_add_cancel, norm_one] at hh
      linarith
    rw [hsplit K n hn, norm_mul]
    nlinarith [norm_nonneg (P K)]
  have hc : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
      ∀ m ≥ M, ∀ n ≥ M, ‖P n - P m‖ < ε := by
    intro ε hε
    let B : ℝ := 2 * ‖P K‖ + 1
    have hB : 0 < B := by dsimp [B]; positivity
    obtain ⟨J, hJ⟩ := magnitude_tails_small u hu (min (1 / 2) (ε / (2 * B)))
      (lt_min (by norm_num) (div_pos hε (by positivity)))
    have hord (m n : ℕ) (hm : max K J ≤ m) (hmn : m ≤ n) : ‖P n - P m‖ < ε := by
      have ht := hJ m ((le_max_right K J).trans hm) n hmn
      have ht₁ := lt_of_lt_of_le ht (min_le_left _ _)
      have ht₂ := lt_of_lt_of_le ht (min_le_right _ _)
      have he := product_error_le_twice u (Finset.Ico m n) ht₁
      have hp := hbound m ((le_max_left K J).trans hm)
      have heq : P n - P m = P m * ((∏ j ∈ Finset.Ico m n, (1 + u j)) - 1) := by
        rw [hsplit m n hmn]; ring
      rw [heq, norm_mul]
      have hsmall : (2 * B) * (∑ j ∈ Finset.Ico m n, ‖u j‖) < ε := by
        have hh := (lt_div_iff₀ (by positivity : 0 < 2 * B)).mp ht₂
        nlinarith
      have hb : ‖P m‖ ≤ B := by dsimp [B]; linarith
      have ht0 : 0 ≤ ∑ j ∈ Finset.Ico m n, ‖u j‖ :=
        Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      calc
        _ ≤ B * (2 * ∑ j ∈ Finset.Ico m n, ‖u j‖) :=
          mul_le_mul hb he (norm_nonneg _) hB.le
        _ < ε := by nlinarith
    refine ⟨max K J, fun m hm n hn => ?_⟩
    rcases le_total m n with hmn | hnm
    · exact hord m n hm hmn
    · rw [norm_sub_rev]; exact hord n m hn hnm
  obtain ⟨L, hL⟩ := (complex_cauchy_criterion P).mpr hc
  have hPK : P K ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hne j)
  have hlower (n : ℕ) (hn : K ≤ n) : ‖P K‖ / 2 ≤ ‖P n‖ := by
    have ht := hK K le_rfl n hn
    have he := complex_finite_product_lower u (Finset.Ico K n) (by linarith)
    rw [hsplit K n hn, norm_mul]
    nlinarith [norm_nonneg (P K)]
  have hLn : ‖P K‖ / 2 ≤ ‖L‖ := by
    apply ge_of_tendsto (((complexSequenceConverges_iff _ _).mp hL).norm)
    exact Filter.eventually_atTop.mpr ⟨K, hlower⟩
  refine ⟨L, ?_, ?_⟩
  · intro hz
    rw [hz, norm_zero] at hLn
    have := norm_pos_iff.mpr hPK
    linarith
  · apply (complexSequenceConverges_iff _ _).mpr
    exact ((complexSequenceConverges_iff _ _).mp hL).comp (Filter.tendsto_add_atTop_nat 1)

end SingleVariableAnalysis
