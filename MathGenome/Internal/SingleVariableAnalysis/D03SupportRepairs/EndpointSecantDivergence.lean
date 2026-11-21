import MathGenome.Internal.SingleVariableAnalysis.D03SupportRepairs.EndpointDerivativeDivergence
import Mathlib.Analysis.Calculus.LHopital

/-! Secant half of the endpoint theorem in paper.tex:77–90,92–99
(original manuscript:1739–1742). L'Hôpital's rule transfers the interior
arcsine derivative limit to the actual endpoint quotient. -/
open Filter Set
open scoped Topology

namespace D03SupportRepairs

/-- The signed arcsine secant tends to positive infinity at either endpoint. -/
lemma arcsin_endpoint_slope_tendsto (a : ℝ) (ha : a = -1 ∨ a = 1) :
    Tendsto (fun x : ℝ => (Real.arcsin x - Real.arcsin a) / (x - a))
      (nhdsWithin a (Ioo (-1 : ℝ) 1)) atTop := by
  have hnot : a ∉ Ioo (-1 : ℝ) 1 := by
    rcases ha with rfl | rfl <;> simp
  have hs : Ioo (-1 : ℝ) 1 \ {a} = Ioo (-1 : ℝ) 1 :=
    sdiff_singleton_eq_self hnot
  have hnum : Tendsto (fun x : ℝ => Real.arcsin x - Real.arcsin a)
      (nhdsWithin a (Ioo (-1 : ℝ) 1)) (𝓝 0) := by
    simpa using ((Real.continuous_arcsin.tendsto a).sub_const
      (Real.arcsin a)).mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun x : ℝ => x - a)
      (nhdsWithin a (Ioo (-1 : ℝ) 1)) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 a) (𝓝 a)).sub_const a).mono_left
      (nhdsWithin_le_nhds (s := Ioo (-1 : ℝ) 1))
  have hd : Tendsto (fun x : ℝ => (1 / Real.sqrt (1 - x ^ 2)) / 1)
      (nhdsWithin a (Ioo (-1 : ℝ) 1)) atTop := by
    have hD := endpointDerivativeDivergence Real.arcsin (Or.inl rfl) a ha
    change Tendsto (fun x : ℝ => |deriv Real.arcsin x|) _ _ at hD
    simpa only [Real.deriv_arcsin, abs_div, abs_one,
      abs_of_nonneg (Real.sqrt_nonneg _), div_one] using hD
  have h := HasDerivWithinAt.lhopital_zero_nhdsWithin_convex
    (s := Ioo (-1 : ℝ) 1) (a := a) (l := atTop)
    (f := fun x : ℝ => Real.arcsin x - Real.arcsin a)
    (f' := fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2))
    (g := fun x : ℝ => x - a) (g' := fun _ : ℝ => (1 : ℝ))
    (convex_Ioo (-1 : ℝ) 1) ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [hs] using h
  · rw [hs]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ((Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)).sub_const
      (Real.arcsin a)).hasDerivWithinAt
  · exact Eventually.of_forall fun x => ((hasDerivAt_id x).sub_const a).hasDerivWithinAt
  · exact Eventually.of_forall fun _ => one_ne_zero
  · simpa only [hs] using hnum
  · simpa only [hs] using hden
  · simpa only [hs] using hd

/-- All four secant magnitude limits, using the actual endpoint value and the
same nontrivial interior filters as the derivative divergence theorem. -/
theorem endpointSecantDivergence
    (F : ℝ → ℝ) (hF : F = Real.arcsin ∨ F = Real.arccos)
    (a : ℝ) (ha : a = -1 ∨ a = 1) :
    Tendsto (fun x : ℝ => secantMagnitude F a x)
      (nhdsWithin a (Ioo (-1 : ℝ) 1)) atTop := by
  have h := tendsto_abs_atTop_atTop.comp (arcsin_endpoint_slope_tendsto a ha)
  rcases hF with rfl | rfl
  · exact h
  · apply h.congr'
    filter_upwards [] with x
    dsimp only [Function.comp_apply, secantMagnitude]
    rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
    have heq : Real.pi / 2 - Real.arcsin x - (Real.pi / 2 - Real.arcsin a) =
        -(Real.arcsin x - Real.arcsin a) := by ring
    rw [heq, neg_div, abs_neg]

end D03SupportRepairs
