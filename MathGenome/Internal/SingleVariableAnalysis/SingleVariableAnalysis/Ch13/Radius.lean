import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.PowerSeries
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Root
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Radius
import Mathlib.Order.Filter.ENNReal

/-!
# Cauchy–Hadamard radius, including zero and infinity

The roots are the upstream nonnegative integer roots. A finite nonnegative
factor t multiplies their extended limsup by t, including t=0 and infinite
growth. The root bounds below bridge the ENNReal representation of the radius
to the ordinary geometric comparison and term test from Chapter 11.
No convergence assertion is made on the boundary.
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped ENNReal BigOperators Topology

namespace PowerSeriesRadius

/-- Root growth of a nonnegative real magnitude sequence. -/
def rootGrowth (b : ℕ → ℝ) : ℝ≥0∞ :=
  limsup (fun n : ℕ => ENNReal.ofReal (nonnegativeRoot (n+1) (b (n+1)))) atTop

/-- Finite power algebra and uniqueness of the nonnegative root. -/
theorem root_mul_pow (b t : ℝ) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (m : ℕ) (hm : 0 < m) :
    nonnegativeRoot m (b * t^m) = nonnegativeRoot m b * t := by
  apply (nonnegativeRoot_unique m hm (b * t^m) (by positivity)
    (nonnegativeRoot m b * t) (mul_nonneg (nonnegativeRoot_nonneg m hm b hb) ht) ?_).symm
  rw [mul_pow, nonnegativeRoot_pow m hm b hb]

/-- Scaling roots commutes with limsup for every finite t ≥ 0. -/
theorem rootGrowth_mul_pow (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (t : ℝ) (ht : 0 ≤ t) :
    rootGrowth (fun n => b n * t^n) = ENNReal.ofReal t * rootGrowth b := by
  unfold rootGrowth
  simp_rw [root_mul_pow _ t (hb _) ht _ (Nat.succ_pos _),
    ENNReal.ofReal_mul (nonnegativeRoot_nonneg _ (Nat.succ_pos _) _ (hb _))]
  exact ENNReal.limsup_mul_const_of_ne_top ENNReal.ofReal_ne_top

/-- A strict extended root bound gives ordinary convergence of magnitudes. -/
theorem converges_of_rootGrowth_lt_one (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (h : rootGrowth b < 1) : RealSeriesConverges b := by
  obtain ⟨q, hq0, hGq, hq1⟩ := ENNReal.lt_iff_exists_real_btwn.mp h
  have hqpos : 0 < q := ENNReal.ofReal_pos.mp (bot_le.trans_lt hGq)
  have hqone : q < 1 := by
    simpa using (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mp (by simpa using hq1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hGq)
  apply nonnegative_converges_of_geometric_bound b hb q hq0 hqone (N+1)
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hr : nonnegativeRoot (k+1) (b (k+1)) ≤ q :=
    ((ENNReal.ofReal_lt_ofReal_iff hqpos).mp (hN k (by omega))).le
  calc
    b (k+1) = nonnegativeRoot (k+1) (b (k+1)) ^ (k+1) :=
      (nonnegativeRoot_pow _ (Nat.succ_pos _) _ (hb _)).symm
    _ ≤ q^(k+1) := pow_le_pow_left₀
      (nonnegativeRoot_nonneg _ (Nat.succ_pos _) _ (hb _)) hr _

/-- The ordinary term test bounds the extended nonnegative root growth. -/
theorem rootGrowth_le_one_of_term_limit (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (h : RealSequenceConverges b 0) : rootGrowth b ≤ 1 := by
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  apply limsup_le_of_le (by isBoundedDefault)
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  have hsmall : b (n+1) ≤ 1 := by
    have := hN (n+1) (by omega)
    simpa only [sub_zero, abs_of_nonneg (hb _)] using this.le
  have hr : nonnegativeRoot (n+1) (b (n+1)) ≤ 1 := by
    apply (pow_le_pow_iff_left₀
      (nonnegativeRoot_nonneg _ (Nat.succ_pos n) _ (hb _)) zero_le_one
      (Nat.succ_ne_zero n)).mp
    simpa only [nonnegativeRoot_pow _ (Nat.succ_pos n) _ (hb _), one_pow] using hsmall
  simpa using ENNReal.ofReal_le_ofReal hr

/-- Reciprocal comparison on the strict interior, with no finiteness of L. -/
theorem scaled_growth_lt_one {L : ℝ≥0∞} {t : ℝ} (h : ENNReal.ofReal t < L⁻¹) :
    ENNReal.ofReal t * L < 1 := by
  have h' : L < 1 / ENNReal.ofReal t := by
    simpa using ENNReal.lt_inv_iff_lt_inv.mp h
  simpa [mul_comm] using ENNReal.mul_lt_of_lt_div h'

/-- On the exterior, t is positive, so multiplication is an order isomorphism. -/
theorem one_lt_scaled_growth {L : ℝ≥0∞} {t : ℝ} (h : L⁻¹ < ENNReal.ofReal t) :
    1 < ENNReal.ofReal t * L := by
  have ht : ENNReal.ofReal t ≠ 0 := ne_of_gt (bot_le.trans_lt h)
  have h' := (ENNReal.mul_lt_mul_iff_right ht ENNReal.ofReal_ne_top).mpr
    (ENNReal.inv_lt_iff_inv_lt.mp h)
  simpa [ENNReal.mul_inv_cancel ht ENNReal.ofReal_ne_top] using h'

/-- Any two strict interior/exterior characterizations determine the same radius.
Only nonnegative finite distances are used, even when a radius is infinite. -/
theorem unique_radius (P : ℝ → Prop) (r s : ℝ≥0∞)
    (hir : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < r → P t)
    (hor : ∀ t : ℝ, 0 ≤ t → r < ENNReal.ofReal t → ¬ P t)
    (his : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < s → P t)
    (hos : ∀ t : ℝ, 0 ≤ t → s < ENNReal.ofReal t → ¬ P t) : r = s := by
  apply le_antisymm
  · apply le_of_not_gt
    intro h
    obtain ⟨t, ht, hst, htr⟩ := ENNReal.lt_iff_exists_real_btwn.mp h
    exact hos t ht hst (hir t ht htr)
  · apply le_of_not_gt
    intro h
    obtain ⟨t, ht, hrt, hts⟩ := ENNReal.lt_iff_exists_real_btwn.mp h
    exact hor t ht hrt (his t ht hts)

end PowerSeriesRadius

open PowerSeriesRadius

theorem real_powerSeries_center_hasSum (a : ℕ → ℝ) (c : ℝ) :
    RealPowerSeriesHasSum a c c (a 0) ∧ RealPowerSeriesAbsolutelyConverges a c c := by
  constructor
  · intro ε hε
    refine ⟨0, fun N _ => ?_⟩
    simpa [realPowerSeriesPartialSum, realPartialSum, realPowerSeriesTerm,
      zero_pow_eq, apply_ite] using hε
  · refine ⟨|a 0|, ?_⟩
    intro ε hε
    refine ⟨0, fun N _ => ?_⟩
    simpa [realPartialSum, realPowerSeriesTerm, zero_pow_eq, apply_ite] using hε

theorem complex_powerSeries_center_hasSum (a : ℕ → ℂ) (c : ℝ) :
    ComplexPowerSeriesHasSum a c (c : ℂ) (a 0) ∧
    ComplexPowerSeriesAbsolutelyConverges a c (c : ℂ) := by
  constructor
  · intro ε hε
    refine ⟨0, fun N _ => ?_⟩
    simpa [complexPowerSeriesPartialSum, complexPartialSum, complexPowerSeriesTerm,
      zero_pow_eq, apply_ite] using hε
  · refine ⟨‖a 0‖, ?_⟩
    intro ε hε
    refine ⟨0, fun N _ => ?_⟩
    simpa [realPartialSum, complexPowerSeriesTerm, zero_pow_eq, apply_ite] using hε

theorem real_powerSeries_radius_absolute (a : ℕ → ℝ) (c x : ℝ)
    (h : ENNReal.ofReal |x-c| < realPowerSeriesRadius a) :
    RealPowerSeriesAbsolutelyConverges a c x := by
  change RealSeriesConverges (fun n => |realPowerSeriesTerm a c x n|)
  simp_rw [real_powerSeries_term_magnitude]
  apply converges_of_rootGrowth_lt_one _ (fun n => by positivity)
  rw [rootGrowth_mul_pow _ (fun _ => abs_nonneg _) _ (abs_nonneg _)]
  exact scaled_growth_lt_one h

theorem complex_powerSeries_radius_absolute (a : ℕ → ℂ) (c : ℝ) (z : ℂ)
    (h : ENNReal.ofReal ‖z-(c : ℂ)‖ < complexPowerSeriesRadius a) :
    ComplexPowerSeriesAbsolutelyConverges a c z := by
  change RealSeriesConverges (fun n => ‖complexPowerSeriesTerm a c z n‖)
  simp_rw [complex_powerSeries_term_magnitude]
  apply converges_of_rootGrowth_lt_one _ (fun n => by positivity)
  rw [rootGrowth_mul_pow _ (fun _ => norm_nonneg _) _ (norm_nonneg _)]
  exact scaled_growth_lt_one h

theorem real_powerSeries_radius_diverges (a : ℕ → ℝ) (c x : ℝ)
    (h : realPowerSeriesRadius a < ENNReal.ofReal |x-c|) :
    ¬ RealPowerSeriesConverges a c x := by
  intro hc
  have ht := real_abs _ 0 (real_series_term_limit _ hc)
  have ht0 : RealSequenceConverges (fun n => |realPowerSeriesTerm a c x n|) 0 := by
    simpa using ht
  have hg := rootGrowth_le_one_of_term_limit _ (fun _ => abs_nonneg _) ht0
  simp_rw [real_powerSeries_term_magnitude] at hg
  rw [rootGrowth_mul_pow _ (fun _ => abs_nonneg _) _ (abs_nonneg _)] at hg
  exact (not_le_of_gt (one_lt_scaled_growth h)) hg

theorem complex_powerSeries_radius_diverges (a : ℕ → ℂ) (c : ℝ) (z : ℂ)
    (h : complexPowerSeriesRadius a < ENNReal.ofReal ‖z-(c : ℂ)‖) :
    ¬ ComplexPowerSeriesConverges a c z := by
  intro hc
  have ht := complex_norm _ 0 (complex_series_term_limit _ hc)
  have ht0 : RealSequenceConverges (fun n => ‖complexPowerSeriesTerm a c z n‖) 0 := by
    simpa using ht
  have hg := rootGrowth_le_one_of_term_limit _ (fun _ => norm_nonneg _) ht0
  simp_rw [complex_powerSeries_term_magnitude] at hg
  rw [rootGrowth_mul_pow _ (fun _ => norm_nonneg _) _ (norm_nonneg _)] at hg
  exact (not_le_of_gt (one_lt_scaled_growth h)) hg

theorem real_powerSeries_radius_unique (a : ℕ → ℝ) (c : ℝ) (r : ℝ≥0∞)
    (hi : ∀ x : ℝ, ENNReal.ofReal |x-c| < r →
      RealPowerSeriesAbsolutelyConverges a c x)
    (ho : ∀ x : ℝ, r < ENNReal.ofReal |x-c| →
      ¬ RealPowerSeriesConverges a c x) : r = realPowerSeriesRadius a := by
  have hd (t : ℝ) (ht : 0 ≤ t) : |(c+t)-c| = t := by
    simpa using abs_of_nonneg ht
  apply unique_radius (fun t => RealPowerSeriesConverges a c (c+t)) r
    (realPowerSeriesRadius a)
  · intro t ht h
    exact real_absolute_converges _ (hi (c+t) (by rwa [hd t ht]))
  · intro t ht h
    exact ho (c+t) (by rwa [hd t ht])
  · intro t ht h
    exact real_absolute_converges _
      (real_powerSeries_radius_absolute a c (c+t) (by rwa [hd t ht]))
  · intro t ht h
    exact real_powerSeries_radius_diverges a c (c+t) (by rwa [hd t ht])

theorem complex_powerSeries_radius_unique (a : ℕ → ℂ) (c : ℝ) (r : ℝ≥0∞)
    (hi : ∀ z : ℂ, ENNReal.ofReal ‖z-(c : ℂ)‖ < r →
      ComplexPowerSeriesAbsolutelyConverges a c z)
    (ho : ∀ z : ℂ, r < ENNReal.ofReal ‖z-(c : ℂ)‖ →
      ¬ ComplexPowerSeriesConverges a c z) : r = complexPowerSeriesRadius a := by
  have hd (t : ℝ) (ht : 0 ≤ t) : ‖((c+t : ℝ) : ℂ)-(c : ℂ)‖ = t := by
    rw [← Complex.ofReal_sub, Complex.norm_real, add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg ht]
  apply unique_radius (fun t => ComplexPowerSeriesConverges a c ((c+t : ℝ) : ℂ)) r
    (complexPowerSeriesRadius a)
  · intro t ht h
    exact complex_absolute_converges _ (hi _ (by rwa [hd t ht]))
  · intro t ht h
    exact ho _ (by rwa [hd t ht])
  · intro t ht h
    exact complex_absolute_converges _
      (complex_powerSeries_radius_absolute a c _ (by rwa [hd t ht]))
  · intro t ht h
    exact complex_powerSeries_radius_diverges a c _ (by rwa [hd t ht])

theorem real_powerSeries_radius_endpoints (a : ℕ → ℝ) (c : ℝ) :
    (realPowerSeriesRadius a = 0 → ∀ x : ℝ, x ≠ c →
      ¬ RealPowerSeriesConverges a c x) ∧
    (realPowerSeriesRadius a = ⊤ → ∀ x : ℝ,
      RealPowerSeriesAbsolutelyConverges a c x) := by
  constructor
  · intro h x hx
    apply real_powerSeries_radius_diverges
    rw [h]
    exact ENNReal.ofReal_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hx))
  · intro h x
    apply real_powerSeries_radius_absolute
    rw [h]
    exact ENNReal.ofReal_lt_top

theorem complex_powerSeries_radius_endpoints (a : ℕ → ℂ) (c : ℝ) :
    (complexPowerSeriesRadius a = 0 → ∀ z : ℂ, z ≠ (c : ℂ) →
      ¬ ComplexPowerSeriesConverges a c z) ∧
    (complexPowerSeriesRadius a = ⊤ → ∀ z : ℂ,
      ComplexPowerSeriesAbsolutelyConverges a c z) := by
  constructor
  · intro h z hz
    apply complex_powerSeries_radius_diverges
    rw [h]
    exact ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
  · intro h z
    apply complex_powerSeries_radius_absolute
    rw [h]
    exact ENNReal.ofReal_lt_top

end SingleVariableAnalysis
