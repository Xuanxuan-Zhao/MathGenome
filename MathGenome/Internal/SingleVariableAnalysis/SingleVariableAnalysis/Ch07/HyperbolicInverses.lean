import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.Hyperbolic
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogDerivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.HyperbolicInverses
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Field

/-!
Principal real inverses in K03.07.hyperbolic, paper.tex:1769–1792.
The definitions retain the upstream logarithm, the inverse of the factorial
series. Positive-argument bridges identify the formulas with the canonical
Mathlib inverses. Arsinh/Arcosh prove inverse identities by exponential algebra
and their derivatives by the inverse rule; Artanh proves its inverse identities
by exponential algebra. We differentiate its half-log formula below.
At 1, the reciprocal cosh slope at 0 gives the infinite right derivative.
-/

noncomputable section
namespace SingleVariableAnalysis

open Set Filter
open scoped Topology

def realArsinh (y : ℝ) : ℝ := seriesLog (y + Real.sqrt (y ^ 2 + 1))
def realArcosh (y : ℝ) : ℝ := seriesLog (y + Real.sqrt (y ^ 2 - 1))
def realArtanh (y : ℝ) : ℝ := (1 / 2) * seriesLog ((1 + y) / (1 - y))

theorem arsinh_log_argument_pos (y : ℝ) : 0 < y + Real.sqrt (y ^ 2 + 1) := by
  have h : -y < Real.sqrt (y ^ 2 + 1) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  linarith

theorem realArsinh_eq_arsinh (y : ℝ) : realArsinh y = Real.arsinh y := by
  rw [realArsinh, seriesLog_eq_realLog _ (arsinh_log_argument_pos y), Real.arsinh,
    add_comm (y ^ 2) 1]

theorem realArcosh_eq_arcosh (y : ℝ) (hy : 1 ≤ y) :
    realArcosh y = Real.arcosh y := by
  rw [realArcosh, seriesLog_eq_realLog _ (by positivity), Real.arcosh]

theorem realArtanh_eq_artanh (y : ℝ) (hy : |y| < 1) :
    realArtanh y = Real.artanh y := by
  have hb := abs_lt.mp hy
  have hp : 0 < (1 + y) / (1 - y) := div_pos (by linarith) (by linarith)
  rw [realArtanh, seriesLog_eq_realLog _ hp, Real.artanh_eq_half_log ⟨hb.1.le, hb.2.le⟩]

theorem realSinh_realArsinh (y : ℝ) : realSinh (realArsinh y) = y := by
  rw [realSinh_eq_sinh, realArsinh_eq_arsinh, Real.sinh_arsinh]

theorem realArsinh_realSinh (x : ℝ) : realArsinh (realSinh x) = x := by
  rw [realSinh_eq_sinh, realArsinh_eq_arsinh, Real.arsinh_sinh]

theorem realCosh_realArcosh (y : ℝ) (hy : 1 ≤ y) : realCosh (realArcosh y) = y := by
  rw [realCosh_eq_cosh, realArcosh_eq_arcosh y hy, Real.cosh_arcosh hy]

theorem realArcosh_realCosh (x : ℝ) (hx : 0 ≤ x) : realArcosh (realCosh x) = x := by
  rw [realCosh_eq_cosh, realArcosh_eq_arcosh _ (Real.one_le_cosh x), Real.arcosh_cosh hx]

theorem realTanh_realArtanh (y : ℝ) (hy : |y| < 1) : realTanh (realArtanh y) = y := by
  rw [realTanh_eq_tanh, realArtanh_eq_artanh y hy, Real.tanh_artanh (abs_lt.mp hy)]

theorem realArtanh_realTanh (x : ℝ) : realArtanh (realTanh x) = x := by
  have h : |Real.tanh x| < 1 := abs_lt.mpr ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
  rw [realTanh_eq_tanh, realArtanh_eq_artanh _ h, Real.artanh_tanh]

theorem realArsinh_range : range realArsinh = univ := by
  apply range_eq_univ.mpr
  intro x
  exact ⟨realSinh x, realArsinh_realSinh x⟩

theorem realArcosh_range : realArcosh '' Ici 1 = Ici 0 := by
  calc
    realArcosh '' Ici 1 = Real.arcosh '' Ici 1 :=
      image_congr fun y hy => realArcosh_eq_arcosh y hy
    _ = Ici 0 := Real.arcosh_bijOn.image_eq

theorem realArtanh_range : realArtanh '' {y | |y| < 1} = univ := by
  apply eq_univ_of_forall
  intro x
  refine ⟨realTanh x, ?_, realArtanh_realTanh x⟩
  rw [realTanh_eq_tanh]
  exact abs_lt.mpr ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩

theorem realArsinh_hasDerivAt (y : ℝ) :
    HasDerivAt realArsinh (1 / Real.sqrt (1 + y ^ 2)) y := by
  rw [show realArsinh = Real.arsinh from funext realArsinh_eq_arsinh, one_div]
  exact Real.hasDerivAt_arsinh y

theorem realArcosh_hasDerivAt (y : ℝ) (hy : 1 < y) :
    HasDerivAt realArcosh (1 / Real.sqrt (y ^ 2 - 1)) y := by
  rw [one_div]
  apply (Real.hasDerivAt_arcosh hy).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hy] with z hz
  exact realArcosh_eq_arcosh z hz.le

theorem realArtanh_hasDerivAt (y : ℝ) (hy : |y| < 1) :
    HasDerivAt realArtanh (1 / (1 - y ^ 2)) y := by
  have hb := abs_lt.mp hy
  have hd : 1 - y ≠ 0 := by linarith
  have hp : 0 < (1 + y) / (1 - y) := div_pos (by linarith) (by linarith)
  have hq := ((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).div
    ((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)) hd
  have hl := (seriesLog_hasDerivAt _ hp).comp y hq
  simp only [zero_add, zero_sub] at hl
  change HasDerivAt (fun z : ℝ => seriesLog ((1 + z) / (1 - z)))
    (1 / ((1 + y) / (1 - y)) * ((1 * (1 - y) - (1 + y) * (-1)) / (1 - y) ^ 2)) y at hl
  have hn : 1 + y ≠ 0 := by linarith
  have hs : 1 - y ^ 2 ≠ 0 := by
    have := mul_pos (by linarith : 0 < 1 - y) (by linarith : 0 < 1 + y)
    nlinarith
  convert hl.const_mul (1 / 2) using 1
  · rfl
  · field_simp [hd, hn, hs]
    <;> ring

theorem realArsinh_continuous : Continuous realArsinh := by
  rw [show realArsinh = Real.arsinh from funext realArsinh_eq_arsinh]
  exact Real.continuous_arsinh

theorem realArcosh_continuousOn : ContinuousOn realArcosh (Ici 1) := by
  exact Real.continuousOn_arcosh.congr (fun y hy => realArcosh_eq_arcosh y hy)

theorem realArtanh_continuousOn : ContinuousOn realArtanh {y | |y| < 1} := by
  intro y hy
  exact (realArtanh_hasDerivAt y hy).continuousAt.continuousWithinAt

theorem realArcosh_one : realArcosh 1 = 0 := by
  rw [realArcosh_eq_arcosh 1 le_rfl, Real.arcosh_zero]

theorem realArcosh_infinite_right_derivative :
    Tendsto (fun y => (realArcosh y - realArcosh 1) / (y - 1))
      (𝓝[>] 1) atTop := by
  have hzero : Tendsto realArcosh (𝓝[>] 1) (𝓝 0) := by
    have hc : Tendsto realArcosh (𝓝[>] 1) (𝓝 (realArcosh 1)) :=
      (realArcosh_continuousOn 1 (by norm_num)).mono Ioi_subset_Ici_self
    simpa only [realArcosh_one] using hc
  have harg : Tendsto realArcosh (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hzero, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    change 0 < realArcosh y
    rw [realArcosh_eq_arcosh y hy.le]
    exact Real.arcosh_pos hy
  have hcosh : Tendsto (slope Real.cosh 0) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sinh_zero] using
      (Real.hasDerivAt_cosh 0).tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
  have hsmall : Tendsto (fun y => (y - 1) / realArcosh y) (𝓝[>] 1) (𝓝 0) := by
    apply (hcosh.comp harg).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Function.comp_def, slope_def_field, Real.cosh_zero, sub_zero]
    rw [← realCosh_eq_cosh, realCosh_realArcosh y hy.le]
  have hpos : ∀ᶠ y in 𝓝[>] (1 : ℝ), 0 < (y - 1) / realArcosh y := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    apply div_pos (sub_pos.mpr hy)
    rw [realArcosh_eq_arcosh y hy.le]
    exact Real.arcosh_pos hy
  have hinv := (tendsto_nhdsWithin_iff.mpr ⟨hsmall, hpos⟩).inv_tendsto_nhdsGT_zero
  change Tendsto (fun y => ((y - 1) / realArcosh y)⁻¹) (𝓝[>] 1) atTop at hinv
  simpa only [inv_div, realArcosh_one, sub_zero] using hinv

theorem realArcosh_no_finite_right_derivative (d : ℝ) :
    ¬ HasDerivWithinAt realArcosh d (Ici 1) 1 := by
  intro hd
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp hd
  have he : Ici (1 : ℝ) \ {1} = Ioi 1 := by
    ext y
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  rw [he] at hs
  have hs' : Tendsto (fun y => (realArcosh y - realArcosh 1) / (y - 1))
      (𝓝[>] 1) (𝓝 d) := by
    change Tendsto (fun y => slope realArcosh 1 y) (𝓝[>] 1) (𝓝 d) at hs
    simpa only [slope_def_field] using hs
  exact not_tendsto_nhds_of_tendsto_atTop realArcosh_infinite_right_derivative d hs'

end SingleVariableAnalysis
