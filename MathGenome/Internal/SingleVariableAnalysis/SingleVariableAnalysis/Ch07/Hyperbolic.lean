import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpProperties
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.Hyperbolic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Real hyperbolic functions from the factorial-series exponential

Direct-function part of K03.07.hyperbolic, paper.tex:1761–1801.
The definitions use the upstream series construction. Its proved equality
with `Real.exp` identifies them with Mathlib's real hyperbolic functions.
Provenance: Complex/Trigonometric proves the square identity and positivity
by exponential algebra; Trigonometric/DerivHyp proves the sinh/cosh
derivatives and monotonicity by differentiation and the mean value theorem.
Below the quotient rule gives the tanh derivative. The sinh range follows
from continuity and limits; the tanh range is obtained from the positive
range of the upstream exponential. No inverse hyperbolic function is used.
-/

noncomputable section
namespace SingleVariableAnalysis

open Set Filter
open scoped Topology

def realSinh (x : ℝ) : ℝ := (realSeriesExp x - realSeriesExp (-x)) / 2
def realCosh (x : ℝ) : ℝ := (realSeriesExp x + realSeriesExp (-x)) / 2
def realTanh (x : ℝ) : ℝ := realSinh x / realCosh x

private theorem realSeriesExp_eq_exp : realSeriesExp = Real.exp :=
  funext expSeries_eq_realExp

theorem realSinh_eq_sinh (x : ℝ) : realSinh x = Real.sinh x := by
  rw [realSinh, realSeriesExp_eq_exp, Real.sinh_eq]

theorem realCosh_eq_cosh (x : ℝ) : realCosh x = Real.cosh x := by
  rw [realCosh, realSeriesExp_eq_exp, Real.cosh_eq]

theorem realTanh_eq_tanh (x : ℝ) : realTanh x = Real.tanh x := by
  rw [realTanh, realSinh_eq_sinh, realCosh_eq_cosh, Real.tanh_eq_sinh_div_cosh]

theorem realCosh_sq_sub_realSinh_sq (x : ℝ) : realCosh x ^ 2 - realSinh x ^ 2 = 1 := by
  rw [realCosh_eq_cosh, realSinh_eq_sinh]
  exact Real.cosh_sq_sub_sinh_sq x

theorem realCosh_pos (x : ℝ) : 0 < realCosh x := by
  rw [realCosh_eq_cosh]
  exact Real.cosh_pos x

theorem realSinh_hasDerivAt (x : ℝ) : HasDerivAt realSinh (realCosh x) x := by
  rw [show realSinh = Real.sinh from funext realSinh_eq_sinh, realCosh_eq_cosh]
  exact Real.hasDerivAt_sinh x

theorem realCosh_hasDerivAt (x : ℝ) : HasDerivAt realCosh (realSinh x) x := by
  rw [show realCosh = Real.cosh from funext realCosh_eq_cosh, realSinh_eq_sinh]
  exact Real.hasDerivAt_cosh x

theorem realTanh_hasDerivAt (x : ℝ) : HasDerivAt realTanh (1 / realCosh x ^ 2) x := by
  change HasDerivAt (fun y => realSinh y / realCosh y) (1 / realCosh x ^ 2) x
  have h := (realSinh_hasDerivAt x).fun_div (realCosh_hasDerivAt x) (ne_of_gt (realCosh_pos x))
  have hn : realCosh x * realCosh x - realSinh x * realSinh x = 1 := by
    nlinarith [realCosh_sq_sub_realSinh_sq x]
  simpa only [hn] using h

theorem realSinh_strictMono : StrictMono realSinh := by
  rw [show realSinh = Real.sinh from funext realSinh_eq_sinh]
  exact Real.sinh_strictMono

theorem realTanh_strictMono : StrictMono realTanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(realTanh_hasDerivAt x).deriv]
  exact one_div_pos.mpr (sq_pos_of_pos (realCosh_pos x))

theorem realCosh_strictAntiOn : StrictAntiOn realCosh (Iic 0) := by
  intro x hx y hy hxy
  change x ≤ 0 at hx
  change y ≤ 0 at hy
  simp only [realCosh_eq_cosh, Real.cosh_lt_cosh, abs_of_nonpos hx, abs_of_nonpos hy]
  exact neg_lt_neg hxy

theorem realCosh_strictMonoOn : StrictMonoOn realCosh (Ici 0) := by
  rw [show realCosh = Real.cosh from funext realCosh_eq_cosh]
  exact Real.cosh_strictMonoOn

theorem realCosh_minimum : realCosh 0 = 1 ∧
    ∀ x, 1 ≤ realCosh x ∧ (realCosh x = 1 ↔ x = 0) := by
  simp only [realCosh_eq_cosh, Real.cosh_zero]
  refine ⟨trivial, fun x => ⟨Real.one_le_cosh x, ?_⟩⟩
  constructor
  · intro hx
    by_contra hne
    have := Real.one_lt_cosh.mpr hne
    linarith
  · rintro rfl
    exact Real.cosh_zero

theorem realSinh_neg (x : ℝ) : realSinh (-x) = -realSinh x := by
  simp only [realSinh_eq_sinh, Real.sinh_neg]

theorem realCosh_neg (x : ℝ) : realCosh (-x) = realCosh x := by
  simp only [realCosh_eq_cosh, Real.cosh_neg]

theorem realTanh_neg (x : ℝ) : realTanh (-x) = -realTanh x := by
  simp only [realTanh_eq_tanh, Real.tanh_neg]

theorem realSinh_tendsto_atTop : Tendsto realSinh atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [realSinh_eq_sinh]
  exact Real.self_le_sinh_iff.mpr hx

theorem realSinh_tendsto_atBot : Tendsto realSinh atBot atBot := by
  apply tendsto_atBot_mono' atBot _ tendsto_id
  filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
  rw [realSinh_eq_sinh]
  exact Real.sinh_le_self_iff.mpr hx

theorem realSinh_range : range realSinh = univ := by
  apply range_eq_univ.mpr
  exact (Real.continuous_sinh.congr (fun x => (realSinh_eq_sinh x).symm)).surjective
    realSinh_tendsto_atTop realSinh_tendsto_atBot

theorem realTanh_exp_quotient (x : ℝ) : realTanh x =
    (realSeriesExp (2 * x) - 1) / (realSeriesExp (2 * x) + 1) := by
  simp only [realTanh_eq_tanh, realSeriesExp_eq_exp, Real.tanh_eq]
  rw [show 2 * x = x + x by ring, Real.exp_add, Real.exp_neg]
  have hp := Real.exp_pos x
  have hd : Real.exp x + (Real.exp x)⁻¹ ≠ 0 := by positivity
  have hq : Real.exp x * Real.exp x + 1 ≠ 0 := by positivity
  field_simp

theorem realTanh_range : range realTanh = Ioo (-1) 1 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [realTanh_eq_tanh]
    exact ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
  · intro hy
    have hp : 0 < (1 + y) / (1 - y) := div_pos (by linarith [hy.1]) (by linarith [hy.2])
    obtain ⟨u, _, hu⟩ := real_expSeries_bijOn_positive.2.2 hp
    refine ⟨u / 2, ?_⟩
    rw [realTanh_exp_quotient, show 2 * (u / 2) = u by ring]
    change realSeriesExp u = (1 + y) / (1 - y) at hu
    rw [hu]
    have hd : 1 - y ≠ 0 := by linarith [hy.2]
    have hq : (1 + y) / (1 - y) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem realTanh_tendsto_atBot : Tendsto realTanh atBot (𝓝 (-1)) := by
  have he : Tendsto (fun x : ℝ => realSeriesExp (2 * x)) atBot (𝓝 0) :=
    real_expSeries_tendsto_atBot.comp
      ((tendsto_id : Tendsto (fun x : ℝ => x) atBot atBot).const_mul_atBot
        (by norm_num : (0 : ℝ) < 2))
  have h := (he.sub_const 1).div (he.add_const 1) (by norm_num : (0 : ℝ) + 1 ≠ 0)
  change Tendsto (fun x => (realSeriesExp (2 * x) - 1) / (realSeriesExp (2 * x) + 1))
    atBot (𝓝 ((0 - 1) / (0 + 1))) at h
  simpa only [← realTanh_exp_quotient, zero_sub, zero_add, div_one] using h

theorem realTanh_tendsto_atTop : Tendsto realTanh atTop (𝓝 1) := by
  have h := realTanh_tendsto_atBot.comp tendsto_neg_atTop_atBot
  have hn := h.neg
  simpa only [Function.comp_def, realTanh_neg, neg_neg] using hn

end SingleVariableAnalysis
