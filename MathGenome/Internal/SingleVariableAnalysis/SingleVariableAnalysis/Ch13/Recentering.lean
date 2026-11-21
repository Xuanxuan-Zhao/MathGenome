import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Radius
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.DoubleSeries
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Recentering
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Recentering an absolutely convergent scalar power series

K03.13.composition, paper.tex:1422–1430. A finite binomial expansion and a
summable double majorant construct each coefficient and justify exchanging
rows and columns. The public results retain real centers and the accepted
ordinary partial-sum predicates for real and complex coefficients. Complex
increments are allowed for bounds. A positive auxiliary increment proves
coefficient convergence independently of the evaluation increment, so zero
increments and equal centers cause no division by zero.
-/

noncomputable section
namespace SingleVariableAnalysis
open scoped BigOperators ENNReal Topology

namespace Recentering
variable {K : Type*} [RCLike K]

def coefficient (a : ℕ → K) (w : K) (k : ℕ) : K :=
  ∑' n, (n.choose k : K) * a n * w^(n-k)

def term (a : ℕ → K) (w h : K) (n k : ℕ) : K :=
  (n.choose k : K) * a n * w^(n-k) * h^k

theorem term_zero (a : ℕ → K) (w h : K) (n k : ℕ) (hn : n < k) :
    term a w h n k = 0 := by
  simp [term, Nat.choose_eq_zero_of_lt hn]

theorem row_summable (a : ℕ → K) (w h : K) (n : ℕ) :
    Summable (term a w h n) := by
  apply summable_of_ne_finset_zero (s := Finset.range (n+1))
  intro k hk
  exact term_zero a w h n k (by simpa using hk)

theorem row_norm_summable (a : ℕ → K) (w h : K) (n : ℕ) :
    Summable (fun k => ‖term a w h n k‖) := by
  apply summable_of_ne_finset_zero (s := Finset.range (n+1))
  intro k hk
  rw [term_zero a w h n k (by simpa using hk), norm_zero]

theorem row_sum (a : ℕ → K) (w h : K) (n : ℕ) :
    ∑' k, term a w h n k = a n * (w+h)^n := by
  rw [tsum_eq_sum (s := Finset.range (n+1)) (fun k hk =>
    term_zero a w h n k (by simpa using hk))]
  rw [add_comm w h, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [term]
  ring

theorem term_norm (a : ℕ → K) (w h : K) (n k : ℕ) :
    ‖term a w h n k‖ = ‖a n‖ * (n.choose k : ℝ) * ‖w‖^(n-k) * ‖h‖^k := by
  simp only [term, norm_mul, norm_pow, RCLike.norm_natCast]
  ring

theorem row_majorant (a : ℕ → K) (w h : K) (n : ℕ) :
    ∑ k ∈ Finset.range (n+1),
      ‖a n‖ * (n.choose k : ℝ) * ‖w‖^(n-k) * ‖h‖^k =
      ‖a n‖ * (‖w‖+‖h‖)^n := by
  rw [add_comm ‖w‖ ‖h‖, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem row_norm_sum (a : ℕ → K) (w h : K) (n : ℕ) :
    ∑' k, ‖term a w h n k‖ = ‖a n‖ * (‖w‖+‖h‖)^n := by
  rw [tsum_eq_sum (s := Finset.range (n+1)) (fun k hk => by
    rw [term_zero a w h n k (by simpa using hk), norm_zero])]
  simp_rw [term_norm]
  exact row_majorant a w h n

theorem double_summable (a : ℕ → K) (w h : K)
    (hs : Summable (fun n => ‖a n‖ * (‖w‖+‖h‖)^n)) :
    Summable (fun p : ℕ × ℕ => ‖term a w h p.1 p.2‖) := by
  apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
  refine ⟨row_norm_summable a w h, ?_⟩
  simpa only [row_norm_sum] using hs

/-- Coefficients exist even when the later evaluation increment is zero:
use any positive auxiliary increment and divide its fixed kth power. -/
theorem coefficient_norm_summable (a : ℕ → K) (w : K) (r : ℝ) (hr : 0 < r)
    (hs : Summable (fun n => ‖a n‖ * (‖w‖+r)^n)) (k : ℕ) :
    Summable (fun n => ‖(n.choose k : K) * a n * w^(n-k)‖) := by
  have hn := double_summable a w (r : K) (by
    simpa only [RCLike.norm_ofReal, abs_of_pos hr] using hs)
  have hc := hn.prod_symm.prod_factor k
  apply (summable_mul_right_iff (pow_ne_zero k hr.ne')).mp
  simpa only [term, norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_pos hr, Prod.swap] using hc

/-- Removing the zero prefix gives precisely the n≥k coefficient formula. -/
theorem coefficient_tail_hasSum (a : ℕ → K) (w : K) (k : ℕ)
    (hc : Summable (fun n => ‖(n.choose k : K) * a n * w^(n-k)‖)) :
    HasSum (fun n => ((n+k).choose k : K) * a (n+k) * w^n) (coefficient a w k) := by
  have h := hc.of_norm.sum_add_tsum_nat_add k
  have hz : (∑ i ∈ Finset.range k, (i.choose k : K) * a i * w^(i-k)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]
  rw [hz, zero_add] at h
  have hs := ((summable_nat_add_iff k).mpr hc.of_norm).hasSum
  rw [h] at hs
  simpa only [Nat.add_sub_cancel, coefficient] using hs

/-- Binomial expansion followed by the absolutely justified exchange of rows
and columns. The norm assertion is the absolute convergence of the result. -/
theorem recenter (a : ℕ → K) (w h : K)
    (hs : Summable (fun n => ‖a n‖ * (‖w‖+‖h‖)^n)) :
    ∃ S : K, HasSum (fun n => a n * (w+h)^n) S ∧
      HasSum (fun k => coefficient a w k * h^k) S ∧
      Summable (fun k => ‖coefficient a w k * h^k‖) := by
  have hn := double_summable a w h hs
  have hd := hn.of_norm
  have hc (k : ℕ) : (∑' n, term a w h n k) = coefficient a w k * h^k := by
    exact tsum_mul_right
  refine ⟨∑' p : ℕ × ℕ, term a w h p.1 p.2, ?_, ?_, ?_⟩
  · rw [hd.tsum_prod]
    simpa only [row_sum] using hd.prod.hasSum
  · rw [hd.tsum_prod, ← Summable.tsum_comm (f := term a w h) hd]
    simpa only [hc, Prod.swap] using hd.prod_symm.prod.hasSum
  · have ht := summable_norm_rows (fun k n => term a w h n k) hn.prod_symm
    simpa only [hc, Prod.swap] using ht

/-- Ordinary convergence of a nonnegative series implies summability.
This bridge uses finiteness of the upstream extended sum, not a conditional
series interpretation of Summable. -/
theorem summable_of_nonnegative_converges (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (h : RealSeriesConverges f) : Summable f := by
  obtain ⟨S, hS⟩ := h
  have he := nonnegative_extendedSum_of_hasSum f hf S hS
  have hn := summable_norm_of_finite_extended_sum f (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _), he] using
      (ENNReal.ofReal_lt_top : ENNReal.ofReal S < ⊤))
  exact hn.of_norm

/-- A finite positive gap exists also for infinite original radius. -/
theorem positive_gap {t : ℝ} (_ht : 0 ≤ t) {R : ℝ≥0∞}
    (h : ENNReal.ofReal t < R) :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t+r) < R := by
  obtain ⟨s, hs, hts, hsR⟩ := ENNReal.lt_iff_exists_real_btwn.mp h
  have hts' : t < s := lt_of_not_ge (fun hst =>
    (not_le_of_gt hts) (ENNReal.ofReal_le_ofReal hst))
  refine ⟨s-t, sub_pos.mpr hts', ?_⟩
  simpa only [add_sub_cancel] using hsR

/-- Radius-to-majorant bridge for real coefficients. -/
theorem real_majorant (a : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h : ENNReal.ofReal t < realPowerSeriesRadius a) :
    Summable (fun n => ‖a n‖ * t^n) := by
  have hc := real_powerSeries_radius_absolute a 0 t (by
    simpa only [sub_zero, abs_of_nonneg ht] using h)
  apply summable_of_nonnegative_converges _ (fun n => by positivity)
  simpa only [RealPowerSeriesAbsolutelyConverges, realPowerSeriesTerm,
    abs_mul, abs_pow, sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] using hc

/-- Radius-to-majorant bridge for complex coefficients. -/
theorem complex_majorant (a : ℕ → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (h : ENNReal.ofReal t < complexPowerSeriesRadius a) :
    Summable (fun n => ‖a n‖ * t^n) := by
  have hc := complex_powerSeries_radius_absolute a 0 (t : ℂ) (by
    simpa only [Complex.ofReal_zero, sub_zero, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht] using h)
  apply summable_of_nonnegative_converges _ (fun n => by positivity)
  simpa only [ComplexPowerSeriesAbsolutelyConverges, complexPowerSeriesTerm,
    norm_mul, norm_pow, Complex.ofReal_zero, sub_zero, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht] using hc

end Recentering

/-- Binomial coefficient formula at the new real center. Terms below k are zero. -/
def realRecenteredCoefficient (a : ℕ → ℝ) (d b : ℝ) : ℕ → ℝ :=
  Recentering.coefficient a (b-d)

/-- Complex coefficients, retaining real centers. -/
def complexRecenteredCoefficient (a : ℕ → ℂ) (d b : ℝ) : ℕ → ℂ :=
  Recentering.coefficient a ((b-d : ℝ) : ℂ)

/-- Every real coefficient sum converges absolutely, including at b=d. -/
theorem real_recentered_coefficient_convergence (a : ℕ → ℝ) (d b : ℝ)
    (h : ENNReal.ofReal |b-d| < realPowerSeriesRadius a) (k : ℕ) :
    RealSeriesHasSum (fun n => ((n+k).choose k : ℝ) * a (n+k) * (b-d)^n)
      (realRecenteredCoefficient a d b k) ∧
    RealSeriesConverges (fun n => |((n+k).choose k : ℝ) * a (n+k) * (b-d)^n|) := by
  obtain ⟨r, hr, hR⟩ := Recentering.positive_gap (abs_nonneg _) h
  have hc := Recentering.coefficient_norm_summable a (b-d) r hr
    (by simpa only [Real.norm_eq_abs] using
      Recentering.real_majorant a (|b-d|+r) (by positivity) hR) k
  refine ⟨real_series_hasSum_of_hasSum (Recentering.coefficient_tail_hasSum a (b-d) k hc), ?_⟩
  have ht := (summable_nat_add_iff k).mpr hc
  have hts : Summable (fun n => |((n+k).choose k : ℝ) * a (n+k) * (b-d)^n|) := by
    simpa only [Nat.add_sub_cancel, Real.norm_eq_abs] using ht
  exact ⟨_, real_series_hasSum_of_hasSum hts.hasSum⟩

/-- Every complex coefficient sum converges absolutely. -/
theorem complex_recentered_coefficient_convergence (a : ℕ → ℂ) (d b : ℝ)
    (h : ENNReal.ofReal |b-d| < complexPowerSeriesRadius a) (k : ℕ) :
    ComplexSeriesHasSum (fun n => ((n+k).choose k : ℂ) * a (n+k) * ((b-d : ℝ) : ℂ)^n)
      (complexRecenteredCoefficient a d b k) ∧
    RealSeriesConverges (fun n => ‖((n+k).choose k : ℂ) * a (n+k) * ((b-d : ℝ) : ℂ)^n‖) := by
  obtain ⟨r, hr, hR⟩ := Recentering.positive_gap (abs_nonneg _) h
  have hc := Recentering.coefficient_norm_summable a ((b-d : ℝ) : ℂ) r hr
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using
      Recentering.complex_majorant a (|b-d|+r) (by positivity) hR) k
  refine ⟨complex_series_hasSum_of_hasSum
    (Recentering.coefficient_tail_hasSum a ((b-d : ℝ) : ℂ) k hc), ?_⟩
  have ht := (summable_nat_add_iff k).mpr hc
  have hts : Summable (fun n => ‖((n+k).choose k : ℂ) * a (n+k) * ((b-d : ℝ) : ℂ)^n‖) := by
    simpa only [Nat.add_sub_cancel] using ht
  exact ⟨_, real_series_hasSum_of_hasSum hts.hasSum⟩

/-- The source's decisive absolute double-series bound, for real coefficients. -/
theorem real_recentering_double_majorant (a : ℕ → ℝ) (d b h : ℝ)
    (hR : ENNReal.ofReal (|b-d|+|h|) < realPowerSeriesRadius a) :
    Summable (fun p : ℕ × ℕ => |(p.1.choose p.2 : ℝ) * a p.1 *
      (b-d)^(p.1-p.2) * h^p.2|) ∧
    (∑' n, ∑ k ∈ Finset.range (n+1),
      |a n| * (n.choose k : ℝ) * |b-d|^(n-k) * |h|^k) =
      ∑' n, |a n| * (|b-d|+|h|)^n := by
  constructor
  · have hm := Recentering.real_majorant a (|b-d|+|h|) (by positivity) hR
    simpa only [Recentering.term, Real.norm_eq_abs] using
      Recentering.double_summable a (b-d) h (by simpa only [Real.norm_eq_abs] using hm)
  · apply tsum_congr
    intro n
    simpa only [Real.norm_eq_abs] using Recentering.row_majorant a (b-d) h n

/-- The same majorant permits complex increments and complex coefficients. -/
theorem complex_recentering_double_majorant (a : ℕ → ℂ) (d b : ℝ) (h : ℂ)
    (hR : ENNReal.ofReal (|b-d|+‖h‖) < complexPowerSeriesRadius a) :
    Summable (fun p : ℕ × ℕ => ‖(p.1.choose p.2 : ℂ) * a p.1 *
      ((b-d : ℝ) : ℂ)^(p.1-p.2) * h^p.2‖) ∧
    (∑' n, ∑ k ∈ Finset.range (n+1),
      ‖a n‖ * (n.choose k : ℝ) * |b-d|^(n-k) * ‖h‖^k) =
      ∑' n, ‖a n‖ * (|b-d|+‖h‖)^n := by
  constructor
  · have hm := Recentering.complex_majorant a (|b-d|+‖h‖) (by positivity) hR
    exact Recentering.double_summable a ((b-d : ℝ) : ℂ) h
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hm)
  · apply tsum_congr
    intro n
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      Recentering.row_majorant a ((b-d : ℝ) : ℂ) h n

/-- The original and recentered real series have the same ordinary sum. -/
theorem real_powerSeries_recentering (a : ℕ → ℝ) (d b h : ℝ)
    (hR : ENNReal.ofReal (|b-d|+|h|) < realPowerSeriesRadius a) :
    ∃ S : ℝ, RealPowerSeriesHasSum a d (b+h) S ∧
      RealPowerSeriesHasSum (realRecenteredCoefficient a d b) b (b+h) S ∧
      RealPowerSeriesAbsolutelyConverges (realRecenteredCoefficient a d b) b (b+h) := by
  have hm := Recentering.real_majorant a (|b-d|+|h|) (by positivity) hR
  obtain ⟨S, ho, hn, ha⟩ := Recentering.recenter a (b-d) h
    (by simpa only [Real.norm_eq_abs] using hm)
  have he : b+h-d = (b-d)+h := by ring
  refine ⟨S, ?_, ?_, ?_⟩
  · change RealSeriesHasSum (fun n => a n * (b+h-d)^n) S
    simpa only [he] using real_series_hasSum_of_hasSum ho
  · change RealSeriesHasSum
      (fun k => realRecenteredCoefficient a d b k * (b+h-b)^k) S
    simpa only [realRecenteredCoefficient, add_sub_cancel_left] using
      real_series_hasSum_of_hasSum hn
  · change RealSeriesConverges (fun k => |realRecenteredCoefficient a d b k * (b+h-b)^k|)
    have ht : Summable (fun k => |realRecenteredCoefficient a d b k * (b+h-b)^k|) := by
      simpa only [realRecenteredCoefficient, add_sub_cancel_left, Real.norm_eq_abs] using ha
    exact ⟨_, real_series_hasSum_of_hasSum ht.hasSum⟩

/-- The complex estimate and ordinary sum identity, with real centers. -/
theorem complex_powerSeries_recentering (a : ℕ → ℂ) (d b : ℝ) (h : ℂ)
    (hR : ENNReal.ofReal (|b-d|+‖h‖) < complexPowerSeriesRadius a) :
    ∃ S : ℂ, ComplexPowerSeriesHasSum a d ((b : ℂ)+h) S ∧
      ComplexPowerSeriesHasSum (complexRecenteredCoefficient a d b) b ((b : ℂ)+h) S ∧
      ComplexPowerSeriesAbsolutelyConverges (complexRecenteredCoefficient a d b) b ((b : ℂ)+h) := by
  have hm := Recentering.complex_majorant a (|b-d|+‖h‖) (by positivity) hR
  obtain ⟨S, ho, hn, ha⟩ := Recentering.recenter a ((b-d : ℝ) : ℂ) h
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hm)
  have he : (b : ℂ)+h-(d : ℂ) = ((b-d : ℝ) : ℂ)+h := by
    rw [Complex.ofReal_sub]
    ring
  refine ⟨S, ?_, ?_, ?_⟩
  · change ComplexSeriesHasSum (fun n => a n * ((b : ℂ)+h-(d : ℂ))^n) S
    simpa only [he] using complex_series_hasSum_of_hasSum ho
  · change ComplexSeriesHasSum
      (fun k => complexRecenteredCoefficient a d b k * ((b : ℂ)+h-(b : ℂ))^k) S
    simpa only [complexRecenteredCoefficient, add_sub_cancel_left] using
      complex_series_hasSum_of_hasSum hn
  · change RealSeriesConverges
      (fun k => ‖complexRecenteredCoefficient a d b k * ((b : ℂ)+h-(b : ℂ))^k‖)
    have ht : Summable
        (fun k => ‖complexRecenteredCoefficient a d b k * ((b : ℂ)+h-(b : ℂ))^k‖) := by
      simpa only [complexRecenteredCoefficient, add_sub_cancel_left] using ha
    exact ⟨_, real_series_hasSum_of_hasSum ht.hasSum⟩

/-- A positive real neighborhood of each interior real center. -/
theorem real_powerSeries_recentering_neighborhood (a : ℕ → ℝ) (d b : ℝ)
    (hR : ENNReal.ofReal |b-d| < realPowerSeriesRadius a) :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (|b-d|+r) < realPowerSeriesRadius a ∧
      ∀ h : ℝ, |h| < r → ∃ S : ℝ,
        RealPowerSeriesHasSum a d (b+h) S ∧
        RealPowerSeriesHasSum (realRecenteredCoefficient a d b) b (b+h) S ∧
        RealPowerSeriesAbsolutelyConverges (realRecenteredCoefficient a d b) b (b+h) := by
  obtain ⟨r, hr, hrr⟩ := Recentering.positive_gap (abs_nonneg _) hR
  refine ⟨r, hr, hrr, fun h hh => real_powerSeries_recentering a d b h ?_⟩
  exact (ENNReal.ofReal_le_ofReal (by linarith : |b-d|+|h| ≤ |b-d|+r)).trans_lt hrr

/-- A positive disk for complex estimates about every interior real center. -/
theorem complex_powerSeries_recentering_neighborhood (a : ℕ → ℂ) (d b : ℝ)
    (hR : ENNReal.ofReal |b-d| < complexPowerSeriesRadius a) :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (|b-d|+r) < complexPowerSeriesRadius a ∧
      ∀ h : ℂ, ‖h‖ < r → ∃ S : ℂ,
        ComplexPowerSeriesHasSum a d ((b : ℂ)+h) S ∧
        ComplexPowerSeriesHasSum (complexRecenteredCoefficient a d b) b ((b : ℂ)+h) S ∧
        ComplexPowerSeriesAbsolutelyConverges (complexRecenteredCoefficient a d b) b ((b : ℂ)+h) := by
  obtain ⟨r, hr, hrr⟩ := Recentering.positive_gap (abs_nonneg _) hR
  refine ⟨r, hr, hrr, fun h hh => complex_powerSeries_recentering a d b h ?_⟩
  exact (ENNReal.ofReal_le_ofReal (by linarith : |b-d|+‖h‖ ≤ |b-d|+r)).trans_lt hrr

end SingleVariableAnalysis
