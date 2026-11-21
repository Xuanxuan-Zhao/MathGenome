import MathGenome.Internal.SingleVariableAnalysis.D03SupportRepairs.EndpointMagnitudes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Derivative magnitude divergence at the two endpoints of the canonical
real inverse branches (paper.tex:82–89,92–96; original manuscript:1739–1742). -/
open Filter Set
open scoped Topology

namespace D03SupportRepairs

theorem leftEndpointInteriorNeBot :
    NeBot (nhdsWithin (-1 : ℝ) (Ioo (-1 : ℝ) 1)) :=
  left_nhdsWithin_Ioo_neBot (by norm_num)

theorem rightEndpointInteriorNeBot :
    NeBot (nhdsWithin (1 : ℝ) (Ioo (-1 : ℝ) 1)) :=
  right_nhdsWithin_Ioo_neBot (by norm_num)

/-- The common positive denominator tends to zero from above at either endpoint. -/
lemma tendsto_sqrt_one_sub_sq_endpoint (a : ℝ) (ha : a = -1 ∨ a = 1) :
    Tendsto (fun x : ℝ => Real.sqrt (1 - x ^ 2))
      (nhdsWithin a (Ioo (-1 : ℝ) 1)) (𝓝[>] (0 : ℝ)) := by
  have ha2 : a ^ 2 = 1 := by rcases ha with rfl | rfl <;> norm_num
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun x : ℝ => Real.sqrt (1 - x ^ 2))
        (nhdsWithin a (Ioo (-1 : ℝ) 1)) (𝓝 (Real.sqrt (1 - a ^ 2))) :=
      (tendsto_const_nhds.sub (tendsto_id.pow 2)).sqrt |>.mono_left nhdsWithin_le_nhds
    simpa [ha2] using h
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sqrt_pos.mpr (by nlinarith [hx.1, hx.2])

/-- All four derivative limits as actual real-valued limits to `atTop`. -/
theorem endpointDerivativeDivergence
    (F : ℝ → ℝ) (hF : F = Real.arcsin ∨ F = Real.arccos)
    (a : ℝ) (ha : a = -1 ∨ a = 1) :
    Tendsto (derivativeMagnitude F)
      (nhdsWithin a (Ioo (-1 : ℝ) 1)) atTop := by
  have h := (tendsto_sqrt_one_sub_sq_endpoint a ha).inv_tendsto_nhdsGT_zero
  rcases hF with rfl | rfl
  · apply h.congr'
    filter_upwards [] with x
    simp only [derivativeMagnitude, Real.deriv_arcsin, one_div, Pi.inv_apply,
      abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  · apply h.congr'
    filter_upwards [] with x
    simp only [derivativeMagnitude, Real.deriv_arccos, one_div, Pi.inv_apply,
      abs_neg, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]

end D03SupportRepairs
