import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDerivative
import MathGenome.Internal.RealAnalysis.D11.Ch12.BvDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch12.MonotoneDifferentiation
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Differentiation of the original BV function, with the sharp bound for
real and complex values (in fact, for every finite dimensional real normed
space). The variation function controls the norm of each forward increment.
Taking limits at common differentiability points gives `‖F'‖ ≤ V'`.
The monotone derivative integral bound for `V` then proves the sharp estimate.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace D11.Ch12.BvDerivative

variable {E : Type*} [NormedAddCommGroup E]

/-- Finite variation bounds every increment by the increase of variation. -/
lemma norm_increment_le_variation_increment {F : ℝ → E} {a b x y : ℝ}
    (hF : BV F a b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    ‖F y - F x‖ ≤ (variation F a y).toReal - (variation F a x).toReal := by
  have subinterval {u v : ℝ} (hau : a ≤ u) (hvb : v ≤ b) : BV F u v :=
    (bv_iff_boundedVariationOn F u v).mpr
      (((bv_iff_boundedVariationOn F a b).mp hF).mono (Icc_subset_Icc hau hvb))
  have hax := subinterval (u := a) le_rfl hx.2
  have hxy' := subinterval hx.1 hy.2
  have hadd := congrArg ENNReal.toReal (variation_additive F hx.1 hxy)
  rw [ENNReal.toReal_add (ne_of_lt hax) (ne_of_lt hxy')] at hadd
  have hnorm := norm_sub_le_variation F hxy hxy'
  linarith

/-- The real variation function increases on the original closed interval. -/
lemma monotoneOn_variation {F : ℝ → E} {a b : ℝ} (hF : BV F a b) :
    MonotoneOn (fun x => (variation F a x).toReal) (Icc a b) := by
  intro x hx y hy hxy
  have h := norm_increment_le_variation_increment hF hx hy hxy
  have := norm_nonneg (F y - F x)
  linarith

variable [NormedSpace ℝ E]

/-- At common differentiability points, variation controls the derivative
norm without any loss from decomposing the target into coordinates. -/
lemma norm_deriv_le_variation_deriv {F : ℝ → E} {a b x : ℝ}
    (hF : BV F a b) (hx : x ∈ Ioo a b)
    (hdF : DifferentiableAt ℝ F x)
    (hdV : DifferentiableAt ℝ (fun y => (variation F a y).toReal) x) :
    ‖deriv F x‖ ≤ deriv (fun y => (variation F a y).toReal) x := by
  let V : ℝ → ℝ := fun y => (variation F a y).toReal
  have htF := hdF.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
  have htV := hdV.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
  apply le_of_tendsto_of_tendsto htF.norm htV
  have hnear : ∀ᶠ y in 𝓝[>] x, y ∈ Ioo a b :=
    (nhdsWithin_le_nhds : 𝓝[>] x ≤ 𝓝 x) (Ioo_mem_nhds hx.1 hx.2)
  filter_upwards [hnear, self_mem_nhdsWithin] with y hy hxy
  have hpos : 0 < y - x := sub_pos.mpr hxy
  have hbound := norm_increment_le_variation_increment hF
    (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy.le
  simpa only [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hpos, smul_eq_mul] using mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)

end D11.Ch12.BvDerivative

namespace D11.Ch12.BvDerivative

/-- The full BV differentiation theorem, retaining the original point values
and the sharp constant one, also for complex scalars. -/
theorem bv_differentiation : Specs.D11.Ch12.BvDerivative.bv_differentiation_type := by
  intro E _ _ _ _ _ F a b hab hF
  change BV F a b at hF
  let V : ℝ → ℝ := fun x => (variation F a x).toReal
  have hVm : MonotoneOn V (Icc a b) := monotoneOn_variation hF
  obtain ⟨NV, hNVm, hNVs, hNVnull, hVdiff, hVzero, hVmeas, hVnonneg, hVint, hVbound⟩ :=
    MonotoneDifferentiation.monotone_differentiation V hab hVm
  have hFdiff : ∀ᵐ x ∂volume, x ∈ Ioo a b → DifferentiableAt ℝ F x := by
    have hFu : BoundedVariationOn F (uIcc a b) := by
      simpa only [uIcc_of_le hab.le] using (bv_iff_boundedVariationOn F a b).mp hF
    filter_upwards [hFu.ae_differentiableAt_of_mem_uIcc] with x hx hxi
    exact hx (by simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self hxi)
  let N := {x | x ∈ Ioo a b ∧ ¬ DifferentiableAt ℝ F x}
  have hNm : MeasurableSet N :=
    measurableSet_Ioo.inter (measurableSet_of_differentiableAt ℝ F).compl
  have hNnull : volume N = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hFdiff] with x hx
    exact fun hn => hn.2 (hx hn.1)
  have hdom : ∀ᵐ x ∂volume, ‖zeroExtendedDerivative F a b x‖ ≤
      MonotoneDifferentiation.zeroExtendedDerivative V a b x := by
    filter_upwards [hFdiff, measure_eq_zero_iff_ae_notMem.mp hNVnull] with x hx hxV
    by_cases hxi : x ∈ Ioo a b
    · have hdV := (hVdiff x hxi hxV).differentiableAt
      simpa only [zeroExtendedDerivative, MonotoneDifferentiation.zeroExtendedDerivative,
        indicator_of_mem hxi] using
        norm_deriv_le_variation_deriv hF hxi (hx hxi) hdV
    · simp only [zeroExtendedDerivative, MonotoneDifferentiation.zeroExtendedDerivative,
        indicator_of_notMem hxi, norm_zero, le_refl]
  have hmeas : Measurable (zeroExtendedDerivative F a b) :=
    (measurable_deriv F).indicator measurableSet_Ioo
  have hInt : Integrable (zeroExtendedDerivative F a b) volume :=
    hVint.mono' ((stronglyMeasurable_deriv F).indicator measurableSet_Ioo).aestronglyMeasurable hdom
  refine ⟨N, hNm, fun _ hx => hx.1, hNnull, ?_, ?_, hmeas, hInt, ?_⟩
  · intro x hx hxN
    have hd : DifferentiableAt ℝ F x := by
      by_contra h
      exact hxN ⟨hx, h⟩
    simpa only [zeroExtendedDerivative, indicator_of_mem hx] using hd.hasDerivAt
  · intro x hx
    simp only [zeroExtendedDerivative, indicator_of_mem hx.1,
      deriv_zero_of_not_differentiableAt hx.2]
  · have hcomp : (∫ x in a..b, ‖zeroExtendedDerivative F a b x‖) ≤
        ∫ x in a..b, MonotoneDifferentiation.zeroExtendedDerivative V a b x :=
      intervalIntegral.integral_mono_ae hab.le hInt.norm.intervalIntegrable
        hVint.intervalIntegrable hdom
    have hVa : V a = 0 := by simp [V, variation_self]
    change (∫ x in a..b, ‖zeroExtendedDerivative F a b x‖) ≤ (variation F a b).toReal
    simpa only [hVa, sub_zero, V] using hcomp.trans hVbound

/-- The same result for arbitrary functions whose domain is the closed
interval, with agreement of all original point values and of variation. -/
theorem interval_domain : Specs.D11.Ch12.BvDerivative.interval_domain_type := by
  intro E _ _ _ _ _ a b hab F hF
  obtain ⟨G, heq, hvar⟩ := interval_domain_extension a b F
  refine ⟨G, heq, hvar, bv_differentiation G hab ?_⟩
  change variation G a b < ⊤
  rwa [hvar]

end D11.Ch12.BvDerivative
