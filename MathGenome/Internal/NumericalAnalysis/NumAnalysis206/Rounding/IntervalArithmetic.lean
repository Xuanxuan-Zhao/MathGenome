import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.Enclosures
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.IntervalArithmetic
import Mathlib.Algebra.Order.Field.Basic

/-! Outward interval arithmetic, paper.tex W05. -/
namespace NumAnalysis206.Rounding

theorem interval_addition : Specs.interval_addition := by
  intro a b c d _ _ x hx y hy
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem interval_subtraction : Specs.interval_subtraction := by
  intro a b c d _ _ x hx y hy
  exact ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

/-- An affine function stays between any bounds on its two endpoint values. -/
private theorem mul_between (a b x k l u : ℝ) (hx : x ∈ Set.Icc a b)
    (hla : l ≤ a*k) (hlb : l ≤ b*k) (hau : a*k ≤ u) (hbu : b*k ≤ u) :
    x*k ∈ Set.Icc l u := by
  rcases le_total 0 k with hk | hk
  · exact ⟨hla.trans (mul_le_mul_of_nonneg_right hx.1 hk),
      (mul_le_mul_of_nonneg_right hx.2 hk).trans hbu⟩
  · exact ⟨hlb.trans (mul_le_mul_of_nonpos_right hx.2 hk),
      (mul_le_mul_of_nonpos_right hx.1 hk).trans hau⟩

theorem interval_multiplication : Specs.interval_multiplication := by
  intro a b c d _ _ x hx y hy
  let l := min (min (a*c) (a*d)) (min (b*c) (b*d))
  let u := max (max (a*c) (a*d)) (max (b*c) (b*d))
  have hlac : l ≤ a*c := (min_le_left _ _).trans (min_le_left _ _)
  have hlad : l ≤ a*d := (min_le_left _ _).trans (min_le_right _ _)
  have hlbc : l ≤ b*c := (min_le_right _ _).trans (min_le_left _ _)
  have hlbd : l ≤ b*d := (min_le_right _ _).trans (min_le_right _ _)
  have hacu : a*c ≤ u := (le_max_left _ _).trans (le_max_left _ _)
  have hadu : a*d ≤ u := (le_max_right _ _).trans (le_max_left _ _)
  have hbcu : b*c ≤ u := (le_max_left _ _).trans (le_max_right _ _)
  have hbdu : b*d ≤ u := (le_max_right _ _).trans (le_max_right _ _)
  have ha : a*y ∈ Set.Icc l u := by
    simpa only [mul_comm] using mul_between c d y a l u hy
      (by simpa only [mul_comm] using hlac) (by simpa only [mul_comm] using hlad)
      (by simpa only [mul_comm] using hacu) (by simpa only [mul_comm] using hadu)
  have hb : b*y ∈ Set.Icc l u := by
    simpa only [mul_comm] using mul_between c d y b l u hy
      (by simpa only [mul_comm] using hlbc) (by simpa only [mul_comm] using hlbd)
      (by simpa only [mul_comm] using hbcu) (by simpa only [mul_comm] using hbdu)
  exact mul_between a b x y l u hx ha.1 hb.1 ha.2 hb.2

theorem interval_reciprocal : Specs.interval_reciprocal := by
  intro c d _ hzero y hy
  have hy0 : y ≠ 0 := by
    intro h
    exact hzero (h ▸ hy)
  refine ⟨hy0, ?_⟩
  by_cases hc : 0 < c
  · have hyp : 0 < y := hc.trans_le hy.1
    exact ⟨one_div_le_one_div_of_le hyp hy.2,
      one_div_le_one_div_of_le hc hy.1⟩
  · have hd : d < 0 := by
      by_contra h
      exact hzero ⟨le_of_not_gt hc, le_of_not_gt h⟩
    have hyn : y < 0 := hy.2.trans_lt hd
    exact ⟨one_div_le_one_div_of_neg_of_le hd hy.2,
      one_div_le_one_div_of_neg_of_le hyn hy.1⟩

theorem outward_interval : Specs.outward_interval := by
  intro l u lo hi hl hu x hx
  exact ⟨hl.trans hx.1, hx.2.trans hu⟩

theorem interval_division : Specs.interval_division := by
  intro a b c d rlo rhi hab hcd hzero hl hu x hx y hy _hy0
  have hr := (interval_reciprocal c d hcd hzero y hy).2
  have hr' := outward_interval (1/d) (1/c) rlo rhi hl hu hr
  have horder : rlo ≤ rhi := hr'.1.trans hr'.2
  simpa only [div_eq_mul_inv, one_mul] using
    interval_multiplication a b rlo rhi hab horder x hx (1/y) hr'

theorem outward_addition : Specs.outward_addition := by
  intro a b c d lo hi hab hcd hl hu x hx y hy
  exact outward_interval _ _ lo hi hl hu (interval_addition a b c d hab hcd x hx y hy)

theorem outward_subtraction : Specs.outward_subtraction := by
  intro a b c d lo hi hab hcd hl hu x hx y hy
  exact outward_interval _ _ lo hi hl hu (interval_subtraction a b c d hab hcd x hx y hy)

theorem outward_multiplication : Specs.outward_multiplication := by
  intro a b c d lo hi hab hcd hl hu x hx y hy
  exact outward_interval _ _ lo hi hl hu (interval_multiplication a b c d hab hcd x hx y hy)

theorem outward_reciprocal : Specs.outward_reciprocal := by
  intro c d lo hi hcd hzero hl hu y hy
  have h := interval_reciprocal c d hcd hzero y hy
  exact ⟨h.1, outward_interval _ _ lo hi hl hu h.2⟩

theorem outward_division : Specs.outward_division := by
  intro a b c d rlo rhi lo hi hab hcd hzero hrl hru hl hu x hx y hy hy0
  exact outward_interval _ _ lo hi hl hu
    (interval_division a b c d rlo rhi hab hcd hzero hrl hru x hx y hy hy0)

/-- The endpoints are chosen once for the entire interval, rather than separately
for each operand value. Nonemptiness is the exact availability condition. -/
theorem finite_outward_interval : Specs.finite_outward_interval := by
  intro P l u hl hu
  obtain ⟨lo, hlo⟩ := finite_directed_lower P l hl
  obtain ⟨hi, hhi⟩ := finite_directed_upper P u hu
  exact ⟨lo, hi, hlo, hhi, outward_interval l u lo hi hlo.1.2 hhi.1.2⟩

end NumAnalysis206.Rounding
