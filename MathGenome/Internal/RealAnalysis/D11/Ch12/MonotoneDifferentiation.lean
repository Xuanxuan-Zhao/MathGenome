import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.MonotoneDifferentiation
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-! Differentiation of the original monotone function, paper.tex:4089–4120.

`MonotoneOn.ae_differentiableWithinAt_of_mem` applies to arbitrary monotone
point values. Its proof uses `Monotone.ae_hasDerivAt`, which explicitly
squeezes the original values between shifted right-limit values. It does not
infer differentiability from a.e. equality of representatives.

The derivative-integral bound uses nonnegative forward slopes of a constant
extension, their integral bound, and Fatou's lemma, as implemented in
`MonotoneOn.intervalIntegral_deriv_mem_uIcc`. It therefore needs neither
absolute continuity nor a reconstruction identity.
-/

open Set MeasureTheory Filter

namespace D11.Ch12.MonotoneDifferentiation

theorem monotone_differentiation :
    Specs.D11.Ch12.MonotoneDifferentiation.monotone_differentiation_type := by
  intro F a b hab hF
  let N := {x | x ∈ Ioo a b ∧ ¬ DifferentiableAt ℝ F x}
  have hNm : MeasurableSet N :=
    measurableSet_Ioo.inter (measurableSet_of_differentiableAt ℝ F).compl
  have hdiff : ∀ᵐ x ∂volume, x ∈ Ioo a b → DifferentiableAt ℝ F x := by
    filter_upwards [hF.ae_differentiableWithinAt_of_mem] with x hx hxi
    exact (hx (Ioo_subset_Icc_self hxi)).differentiableAt
      (Icc_mem_nhds hxi.1 hxi.2)
  have hNnull : volume N = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hdiff] with x hx
    exact fun hn => hn.2 (hx hn.1)
  have hnonneg (x : ℝ) : 0 ≤ zeroExtendedDerivative F a b x := by
    by_cases hx : x ∈ Ioo a b
    · rw [zeroExtendedDerivative, indicator_of_mem hx,
        ← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
      exact hF.derivWithin_nonneg
    · simp [zeroExtendedDerivative, hx]
  have hFu : MonotoneOn F (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using hF
  have hInt : IntegrableOn (deriv F) (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp
      hFu.intervalIntegrable_deriv
  have hIntZero : Integrable (zeroExtendedDerivative F a b) volume := by
    exact (hInt.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  refine ⟨N, hNm, fun _ hx => hx.1, hNnull, ?_, ?_,
    (measurable_deriv F).indicator measurableSet_Ioo, hnonneg, hIntZero, ?_⟩
  · intro x hx hxN
    have hd : DifferentiableAt ℝ F x := by
      by_contra h
      exact hxN ⟨hx, h⟩
    simpa only [zeroExtendedDerivative, indicator_of_mem hx] using hd.hasDerivAt
  · intro x hx
    simp only [zeroExtendedDerivative, indicator_of_mem hx.1,
      deriv_zero_of_not_differentiableAt hx.2]
  · have hbound := hFu.intervalIntegral_deriv_mem_uIcc
    rw [uIcc_of_le (sub_nonneg.mpr (hF (by simp [hab.le]) (by simp [hab.le]) hab.le))]
      at hbound
    have heq : (∫ x in a..b, zeroExtendedDerivative F a b x) =
        ∫ x in a..b, deriv F x := by
      apply intervalIntegral.integral_congr_uIoo
      rw [uIoo_of_le hab.le]
      intro x hx
      exact indicator_of_mem hx _
    exact heq.trans_le hbound.2

theorem interval_domain :
    Specs.D11.Ch12.MonotoneDifferentiation.interval_domain_type := by
  intro a b hab F hF
  let G : ℝ → ℝ := fun x => if hx : x ∈ Icc a b then F ⟨x, hx⟩ else 0
  have heq (x : Icc a b) : G x = F x := by
    simp only [G, dite_eq_left x.property]
  have hG : MonotoneOn G (Icc a b) := by
    intro x hx y hy hxy
    simpa only [G, dite_eq_left hx, dite_eq_left hy] using (hF hxy : F ⟨x,hx⟩ ≤ F ⟨y,hy⟩)
  exact ⟨G, heq, monotone_differentiation G hab hG⟩

end D11.Ch12.MonotoneDifferentiation
