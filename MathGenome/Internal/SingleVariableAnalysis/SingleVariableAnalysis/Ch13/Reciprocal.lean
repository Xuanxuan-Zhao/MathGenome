import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Composition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Products
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Uniqueness
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Reciprocal

/-! A geometric-series construction with an explicit absolute majorant. The
coefficient recurrence will follow by multiplying actual convergent series and
using coefficient uniqueness, as in K03.13.composition. -/
noncomputable section
open scoped BigOperators ENNReal Topology
namespace SingleVariableAnalysis
namespace Reciprocal

/-- A radial absolute majorant controls each numerical series on its closed ball. -/
theorem monomial_summable {K : Type*} [RCLike K] (a : ℕ → K)
    {s : ℝ} (ha : Summable (fun n => ‖a n‖ * s^n))
    (h : K) (hh : ‖h‖ ≤ s) : Summable (fun n => ‖a n * h^n‖) := by
  apply ha.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  simp only [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hh _) (norm_nonneg _)

/-- Construct coefficients and prove numerical convergence before extracting any
formal recurrence. The witness is a finite geometric composition in each degree. -/
theorem local_reciprocal {K : Type*} [RCLike K] (a : ℕ → K)
    (h0 : a 0 ≠ 0) (s : ℝ) (hs : 0 < s)
    (ha : Summable (fun n => ‖a n‖ * s^n)) :
    ∃ (q : ℕ → K) (r : ℝ), 0 < r ∧ r ≤ s ∧
      Summable (fun n => ‖q n‖ * r^n) ∧
      ∀ h : K, ‖h‖ ≤ r → ∃ F : K, F ≠ 0 ∧
        HasSum (fun n => a n * h^n) F ∧
        HasSum (fun n => q n * h^n) F⁻¹ ∧
        Summable (fun n => ‖q n * h^n‖) := by
  let b : ℕ → K := fun n => -(a 0)⁻¹ * a n
  have hb : Summable (fun n => ‖b n‖ * s^n) := by
    simpa only [b, norm_mul, norm_neg, mul_assoc] using ha.mul_left ‖(a 0)⁻¹‖
  obtain ⟨r, hr, hrs, hU⟩ := Composition.exists_small_majorant b hs zero_lt_one hb
  have hbr := Composition.majorant_summable b hr.le hrs hb
  have hU0 := Composition.majorant_nonneg b hr.le
  have hA : Summable (fun m => ‖(1 : K)‖ * Composition.majorant b r ^ m) := by
    simpa only [norm_one, one_mul] using
      (summable_geometric_of_norm_lt_one (by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hU0] using hU))
  let q : ℕ → K := fun k => (a 0)⁻¹ * Composition.coefficient (fun _ => (1 : K)) b k
  have hqr : Summable (fun n => ‖q n‖ * r^n) := by
    have he := (Composition.evaluate (fun _ => (1 : K)) b hr.le hbr hA (r : K)
      (by simpa only [RCLike.norm_ofReal, abs_of_pos hr] using (le_refl r))).1
    have he' : Summable (fun n =>
        ‖Composition.coefficient (fun _ => (1 : K)) b n‖ * r^n) := by
      simpa only [norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_pos hr] using he
    simpa only [q, norm_mul, mul_assoc] using he'.mul_left ‖(a 0)⁻¹‖
  refine ⟨q, r, hr, hrs, hqr, ?_⟩
  intro h hh
  have hbh := monomial_summable (Composition.positivePart b) hbr h hh
  let v := ∑' j, Composition.positivePart b j * h^j
  have hv : ‖v‖ ≤ Composition.majorant b r := by
    apply (norm_tsum_le_tsum_norm hbh).trans
    apply hbh.tsum_le_tsum _ hbr
    intro j
    simp only [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hh _) (norm_nonneg _)
  have hv1 : ‖v‖ < 1 := hv.trans_lt hU
  have hne : 1-v ≠ 0 := by
    intro hz
    have : v = 1 := (sub_eq_zero.mp hz).symm
    simp only [this, norm_one, lt_self_iff_false] at hv1
  let F := a 0 * (1-v)
  have hF : HasSum (fun n => a n * h^n) F := by
    have he := (hasSum_ite_eq (0 : ℕ) (a 0)).sub
      (hbh.of_norm.hasSum.mul_left (a 0))
    convert he using 1
    · ext n
      by_cases hn : n = 0
      · simp [hn, Composition.positivePart]
      · simp only [ite_eq_right hn, Composition.positivePart_pos b hn, b]
        field_simp
        ring
    · dsimp only [F, v]
      ring
  have hq := (Composition.evaluate (fun _ => (1 : K)) b hr.le hbr hA h hh).2
  have hgeom := hasSum_geometric_of_norm_lt_one hv1
  have hq' : HasSum (fun n => q n * h^n) F⁻¹ := by
    have he := hq.mul_left (a 0)⁻¹
    simpa only [q, v, one_mul, hgeom.tsum_eq, F, mul_inv_rev, mul_assoc,
      mul_comm (1-v)⁻¹] using he
  exact ⟨F, mul_ne_zero h0 hne, hF, hq', monomial_summable q hqr h hh⟩

/-- Numerical Cauchy multiplication, with the common monomial factored out. -/
theorem product_hasSum {K : Type*} [RCLike K] (a q : ℕ → K) (h F G : K)
    (ha : Summable (fun n => ‖a n * h^n‖))
    (hq : Summable (fun n => ‖q n * h^n‖))
    (hF : HasSum (fun n => a n * h^n) F)
    (hG : HasSum (fun n => q n * h^n) G) :
    HasSum (fun n => (∑ j ∈ Finset.range (n+1), a j * q (n-j)) * h^n) (F*G) := by
  have he := hasSum_sum_range_mul_of_summable_norm ha hq
  simpa only [cauchyProduct_monomials, hF.tsum_eq, hG.tsum_eq] using he

theorem unit_hasSum {K : Type*} [RCLike K] (h : K) :
    HasSum (fun n : ℕ => (if n = 0 then (1 : K) else 0) * h^n) 1 := by
  convert hasSum_ite_eq (0 : ℕ) (1 : K) using 1
  ext n
  by_cases hn : n = 0 <;> simp [hn]

/-- Splitting degree k into the constant contribution and the positive indices
is exactly the recurrence in the manuscript (j+1 ranges from 1 through k). -/
theorem coefficients_of_product {K : Type*} [Field K] (a q : ℕ → K)
    (h0 : a 0 ≠ 0)
    (hp : ∀ n : ℕ, (∑ j ∈ Finset.range (n+1), a j * q (n-j)) =
      if n = 0 then 1 else 0) :
    q 0 = 1 / a 0 ∧ ∀ k : ℕ, 0 < k →
      q k = -(a 0)⁻¹ * ∑ j ∈ Finset.range k, a (j+1) * q (k-(j+1)) := by
  constructor
  · have hz : a 0 * q 0 = 1 := by simpa using hp 0
    apply (mul_left_cancel₀ h0)
    simpa [h0] using hz
  · intro k hk
    have he := hp k
    rw [ite_eq_right (Nat.ne_of_gt hk), Finset.sum_range_succ'] at he
    simp only [Nat.sub_zero] at he
    have hm : a 0 * q k = -(∑ j ∈ Finset.range k, a (j+1) * q (k-(j+1))) := by
      exact eq_neg_of_add_eq_zero_right he
    calc
      q k = (a 0)⁻¹ * (a 0 * q k) := by simp [h0]
      _ = _ := by rw [hm]; ring

end Reciprocal
open Reciprocal

/-- Real reciprocal series, with its canonical radius and ordered numerical sums. -/
theorem real_powerSeries_reciprocal :
    Specs.SingleVariableAnalysis.Ch13.Reciprocal.realReciprocal := by
  change ∀ (a : ℕ → ℝ) (c : ℝ), 0 < realPowerSeriesRadius a → a 0 ≠ 0 →
    ∃ (q : ℕ → ℝ) (r : ℝ), 0 < r ∧
      ENNReal.ofReal r < realPowerSeriesRadius a ∧
      ENNReal.ofReal r ≤ realPowerSeriesRadius q ∧
      q 0 = 1 / a 0 ∧
      (∀ k : ℕ, 0 < k → q k = -(a 0)⁻¹ *
        ∑ j ∈ Finset.range k, a (j+1) * q (k-(j+1))) ∧
      ∀ x : ℝ, |x-c| ≤ r → ∃ F : ℝ, F ≠ 0 ∧
        RealPowerSeriesHasSum a c x F ∧
        RealPowerSeriesHasSum q c x (1/F) ∧
        RealPowerSeriesAbsolutelyConverges q c x
  intro a c ha h0
  obtain ⟨s, hs, hsR⟩ := Recentering.positive_gap (le_refl 0) (by simpa using ha)
  have has := Recentering.real_majorant a s hs.le (by simpa using hsR)
  obtain ⟨q, r, hr, hrs, hqr, he⟩ := local_reciprocal a h0 s hs has
  let p : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n+1), a j * q (n-j)
  have hp : p = (fun n => if n = 0 then 1 else 0) := by
    apply real_powerSeries_coefficients_unique p (fun n => if n = 0 then 1 else 0) 0 (fun _ => 1)
    · refine ⟨r, hr, ?_⟩
      intro x hx
      have hxr : ‖x‖ ≤ r := by simpa only [sub_zero, Real.norm_eq_abs] using hx.le
      obtain ⟨F, hF0, hF, hq, hn⟩ := he x hxr
      have hm := product_hasSum a q x F F⁻¹
        (monomial_summable a has x (hxr.trans hrs)) hn hF hq
      rw [mul_inv_cancel₀ hF0] at hm
      change RealSeriesHasSum (fun n => p n * (x-0)^n) 1
      apply real_series_hasSum_of_hasSum
      simpa only [p, sub_zero] using hm
    · refine ⟨r, hr, ?_⟩
      intro x _
      change RealSeriesHasSum (fun n => (if n = 0 then (1 : ℝ) else 0) * (x-0)^n) 1
      apply real_series_hasSum_of_hasSum
      simpa only [sub_zero] using unit_hasSum x
  have hcoeff := coefficients_of_product a q h0 (fun n => congrFun hp n)
  refine ⟨q, r, hr, ?_, Composition.real_radius_lower_bound q r hr.le hqr,
    hcoeff.1, hcoeff.2, ?_⟩
  · exact (ENNReal.ofReal_le_ofReal hrs).trans_lt (by simpa using hsR)
  · intro x hx
    obtain ⟨F, hF0, hF, hq, hn⟩ := he (x-c) (by simpa only [Real.norm_eq_abs] using hx)
    refine ⟨F, hF0, real_series_hasSum_of_hasSum hF, ?_, ?_⟩
    · change RealSeriesHasSum (fun n => q n * (x-c)^n) (1/F)
      simpa only [one_div] using real_series_hasSum_of_hasSum hq
    · exact ⟨_, real_series_hasSum_of_hasSum hn.hasSum⟩

/-- The same construction works on a complex disk about the original real center. -/
theorem complex_powerSeries_reciprocal :
    Specs.SingleVariableAnalysis.Ch13.Reciprocal.complexReciprocal := by
  change ∀ (a : ℕ → ℂ) (c : ℝ), 0 < complexPowerSeriesRadius a → a 0 ≠ 0 →
    ∃ (q : ℕ → ℂ) (r : ℝ), 0 < r ∧
      ENNReal.ofReal r < complexPowerSeriesRadius a ∧
      ENNReal.ofReal r ≤ complexPowerSeriesRadius q ∧
      q 0 = 1 / a 0 ∧
      (∀ k : ℕ, 0 < k → q k = -(a 0)⁻¹ *
        ∑ j ∈ Finset.range k, a (j+1) * q (k-(j+1))) ∧
      ∀ z : ℂ, ‖z-(c : ℂ)‖ ≤ r → ∃ F : ℂ, F ≠ 0 ∧
        ComplexPowerSeriesHasSum a c z F ∧
        ComplexPowerSeriesHasSum q c z (1/F) ∧
        ComplexPowerSeriesAbsolutelyConverges q c z
  intro a c ha h0
  obtain ⟨s, hs, hsR⟩ := Recentering.positive_gap (le_refl 0) (by simpa using ha)
  have has := Recentering.complex_majorant a s hs.le (by simpa using hsR)
  obtain ⟨q, r, hr, hrs, hqr, he⟩ := local_reciprocal a h0 s hs has
  let p : ℕ → ℂ := fun n => ∑ j ∈ Finset.range (n+1), a j * q (n-j)
  have hp : p = (fun n => if n = 0 then 1 else 0) := by
    apply complex_powerSeries_coefficients_unique p (fun n => if n = 0 then 1 else 0) 0 (fun _ => 1)
    · refine ⟨r, hr, ?_⟩
      intro x hx
      have hxr : ‖(x : ℂ)‖ ≤ r := by
        simpa only [sub_zero, Complex.norm_real, Real.norm_eq_abs] using hx.le
      obtain ⟨F, hF0, hF, hq, hn⟩ := he (x : ℂ) hxr
      have hm := product_hasSum a q (x : ℂ) F F⁻¹
        (monomial_summable a has (x : ℂ) (hxr.trans hrs)) hn hF hq
      rw [mul_inv_cancel₀ hF0] at hm
      change ComplexSeriesHasSum (fun n => p n * ((x : ℂ)-0)^n) 1
      apply complex_series_hasSum_of_hasSum
      simpa only [p, sub_zero] using hm
    · refine ⟨r, hr, ?_⟩
      intro x _
      change ComplexSeriesHasSum (fun n => (if n = 0 then (1 : ℂ) else 0) * ((x : ℂ)-0)^n) 1
      apply complex_series_hasSum_of_hasSum
      simpa only [sub_zero] using unit_hasSum (x : ℂ)
  have hcoeff := coefficients_of_product a q h0 (fun n => congrFun hp n)
  refine ⟨q, r, hr, ?_, Composition.complex_radius_lower_bound q r hr.le hqr,
    hcoeff.1, hcoeff.2, ?_⟩
  · exact (ENNReal.ofReal_le_ofReal hrs).trans_lt (by simpa using hsR)
  · intro z hz
    obtain ⟨F, hF0, hF, hq, hn⟩ := he (z-(c : ℂ)) hz
    refine ⟨F, hF0, complex_series_hasSum_of_hasSum hF, ?_, ?_⟩
    · change ComplexSeriesHasSum (fun n => q n * (z-(c : ℂ))^n) (1/F)
      simpa only [one_div] using complex_series_hasSum_of_hasSum hq
    · exact ⟨_, real_series_hasSum_of_hasSum hn.hasSum⟩

end SingleVariableAnalysis
