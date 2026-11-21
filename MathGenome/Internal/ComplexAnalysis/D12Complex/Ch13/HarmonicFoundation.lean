import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicFoundation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.RealComplexDifferential
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.TaylorSmoothness
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Ring

noncomputable section
open Complex Filter Set InnerProductSpace Laplacian
open scoped Topology

open private partialX_eq partialY_eq from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.RealComplexDifferential

namespace D12Complex.HarmonicFoundation

abbrev coordinateLaplacian := D12Complex.coordinateLaplacian
abbrev HarmonicOn := D12Complex.HarmonicOn

private lemma second_partial_eq (u : ℂ → ℝ) (z : ℂ)
    (hu : ContDiffAt ℝ 2 u z) :
    partialX (partialX u) z = fderiv ℝ (fderiv ℝ u) z 1 1 ∧
    partialY (partialY u) z = fderiv ℝ (fderiv ℝ u) z I I := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hX : partialX u =ᶠ[𝓝 z] (fun w => fderiv ℝ u w 1) := by
    filter_upwards [hu.eventually (by norm_num)] with w hw
    exact partialX_eq u w (hw.differentiableAt (by norm_num))
  have hY : partialY u =ᶠ[𝓝 z] (fun w => fderiv ℝ u w I) := by
    filter_upwards [hu.eventually (by norm_num)] with w hw
    exact partialY_eq u w (hw.differentiableAt (by norm_num))
  have hdX : DifferentiableAt ℝ (fun w => fderiv ℝ u w 1) z :=
    hd.clm_apply (differentiableAt_const _)
  have hdY : DifferentiableAt ℝ (fun w => fderiv ℝ u w I) z :=
    hd.clm_apply (differentiableAt_const _)
  constructor
  · rw [partialX_eq _ _ (hdX.congr_of_eventuallyEq hX), hX.fderiv_eq]
    simp [fderiv_clm_apply hd (differentiableAt_const _)]
  · rw [partialY_eq _ _ (hdY.congr_of_eventuallyEq hY), hY.fderiv_eq]
    simp [fderiv_clm_apply hd (differentiableAt_const _)]

theorem coordinateLaplacian_eq_laplacian :
    Specs.D12Complex.Ch13.HarmonicFoundation.coordinateLaplacian_eq_laplacian_type := by
  intro u z hu
  obtain ⟨hX, hY⟩ := second_partial_eq u z hu
  simp [D12Complex.coordinateLaplacian, hX, hY,
    laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply]

theorem harmonicOn_iff_harmonicOnNhd :
    Specs.D12Complex.Ch13.HarmonicFoundation.harmonicOn_iff_harmonicOnNhd_type := by
  intro U u hU
  constructor
  · rintro ⟨_, hC, hL⟩ z hz
    refine ⟨(hC z hz).contDiffAt (hU.mem_nhds hz), ?_⟩
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (coordinateLaplacian_eq_laplacian u w
      ((hC w hw).contDiffAt (hU.mem_nhds hw))).symm.trans (hL w hw)
  · intro h
    refine ⟨hU, h.contDiffOn, fun z hz => ?_⟩
    rw [coordinateLaplacian_eq_laplacian u z (h z hz).1]
    exact (h z hz).2.eq_of_nhds

theorem holomorphic_harmonic_re :
    Specs.D12Complex.Ch13.HarmonicFoundation.holomorphic_harmonic_re_type := by
  intro U f hf
  apply (harmonicOn_iff_harmonicOnNhd U _ hf.1).mpr
  intro z hz
  have hd : DifferentiableOn ℂ f U := fun w hw => (hf.2 w hw).differentiableWithinAt
  exact (hd.analyticAt (hf.1.mem_nhds hz)).harmonicAt_re

theorem holomorphic_harmonic_im :
    Specs.D12Complex.Ch13.HarmonicFoundation.holomorphic_harmonic_im_type := by
  intro U f hf
  apply (harmonicOn_iff_harmonicOnNhd U _ hf.1).mpr
  intro z hz
  have hd : DifferentiableOn ℂ f U := fun w hw => (hf.2 w hw).differentiableWithinAt
  exact (hd.analyticAt (hf.1.mem_nhds hz)).harmonicAt_im

lemma hessian_comp (u : ℂ → ℝ) (F : ℂ → ℂ) (z : ℂ)
    (hu : ContDiffAt ℝ 2 u (F z)) (hF : ContDiffAt ℝ 2 F z) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ (u ∘ F)) z v w =
      fderiv ℝ u (F z) (fderiv ℝ (fderiv ℝ F) z v w) +
      fderiv ℝ (fderiv ℝ u) (F z) (fderiv ℝ F z v) (fderiv ℝ F z w) := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) (F z) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (u ∘ F) =ᶠ[𝓝 z]
      (fun y => (fderiv ℝ u (F y)).comp (fderiv ℝ F y)) := by
    filter_upwards [hF.eventually (by norm_num),
      (hF.continuousAt.tendsto.eventually (hu.eventually (by norm_num)))] with y hy hUy
    exact fderiv_comp y (hUy.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num))
  have hc := fderiv_clm_comp
    (c := fun y => fderiv ℝ u (F y)) (d := fderiv ℝ F)
    (hdu.comp z (hF.differentiableAt (by norm_num))) hdF
  have hdc := fderiv_comp z hdu (hF.differentiableAt (by norm_num))
  simp only [Function.comp_def] at hdc
  rw [heq.fderiv_eq, hc, hdc]
  simp

lemma bilinear_complex_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (c : ℂ) :
    B c c + B (c * I) (c * I) = ‖c‖^2 * (B 1 1 + B I I) := by
  have hc : c = c.re • (1 : ℂ) + c.im • I := by simp
  have hci : c * I = (-c.im) • (1 : ℂ) + c.re • I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  calc
    _ = B (c.re • 1 + c.im • I) (c.re • 1 + c.im • I) +
        B ((-c.im) • 1 + c.re • I) ((-c.im) • 1 + c.re • I) := by rw [← hc, ← hci]
    _ = _ := by
      simp only [map_add, map_smul, add_apply,
        smul_apply, smul_eq_mul, ← normSq_eq_norm_sq, normSq_apply]
      ring

lemma laplacian_eq_hessian_trace {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (u : ℂ → A) (z : ℂ) :
    Δ u z = fderiv ℝ (fderiv ℝ u) z 1 1 + fderiv ℝ (fderiv ℝ u) z I I := by
  simp [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply]

lemma laplacian_comp_analyticAt (u : ℂ → ℝ) (F : ℂ → ℂ) (z : ℂ)
    (hu : ContDiffAt ℝ 2 u (F z)) (hF : AnalyticAt ℂ F z) :
    Δ (u ∘ F) z = ‖deriv F z‖^2 * Δ u (F z) := by
  have hFr : ContDiffAt ℝ 2 F z := hF.contDiffAt.restrict_scalars ℝ
  have hd (v : ℂ) : fderiv ℝ F z v = deriv F z * v := by
    rw [hF.differentiableAt.hasDerivAt.complexToReal_fderiv.fderiv]
    simp
  have hzero := hF.harmonicAt.2.eq_of_nhds
  change Δ F z = 0 at hzero
  rw [laplacian_eq_hessian_trace] at hzero
  rw [laplacian_eq_hessian_trace, hessian_comp u F z hu hFr,
    hessian_comp u F z hu hFr]
  rw [show fderiv ℝ u (F z) (fderiv ℝ (fderiv ℝ F) z 1 1) +
        fderiv ℝ (fderiv ℝ u) (F z) (fderiv ℝ F z 1) (fderiv ℝ F z 1) +
        (fderiv ℝ u (F z) (fderiv ℝ (fderiv ℝ F) z I I) +
        fderiv ℝ (fderiv ℝ u) (F z) (fderiv ℝ F z I) (fderiv ℝ F z I)) =
      fderiv ℝ u (F z) (fderiv ℝ (fderiv ℝ F) z 1 1 +
        fderiv ℝ (fderiv ℝ F) z I I) +
        (fderiv ℝ (fderiv ℝ u) (F z) (fderiv ℝ F z 1) (fderiv ℝ F z 1) +
        fderiv ℝ (fderiv ℝ u) (F z) (fderiv ℝ F z I) (fderiv ℝ F z I)) by
      rw [map_add]; ring]
  simp only [hzero, map_zero, zero_add, hd, mul_one]
  rw [bilinear_complex_trace, laplacian_eq_hessian_trace]

theorem coordinateLaplacian_comp_holomorphic :
    Specs.D12Complex.Ch13.HarmonicFoundation.coordinateLaplacian_comp_holomorphic_type := by
  intro U V u F hU hu hF hFU z hz
  have hu' : ContDiffAt ℝ 2 u (F z) :=
    (hu (F z) (hFU hz)).contDiffAt (hU.mem_nhds (hFU hz))
  have hd : DifferentiableOn ℂ F V := fun w hw => (hF.2 w hw).differentiableWithinAt
  have ha := hd.analyticAt (hF.1.mem_nhds hz)
  have hFr : ContDiffAt ℝ 2 F z := ha.contDiffAt.restrict_scalars ℝ
  rw [coordinateLaplacian_eq_laplacian (u ∘ F) z (hu'.comp z hFr),
    coordinateLaplacian_eq_laplacian u (F z) hu']
  exact laplacian_comp_analyticAt u F z hu' ha

theorem harmonicOn_comp_holomorphic :
    Specs.D12Complex.Ch13.HarmonicFoundation.harmonicOn_comp_holomorphic_type := by
  intro U V u F hu hF hFU
  refine ⟨hF.1, ?_, fun z hz => ?_⟩
  · exact hu.2.1.comp
      ((TaylorSmoothness.holomorphic_real_smooth V F hF).of_le (by simp)) hFU
  · rw [coordinateLaplacian_comp_holomorphic U V u F hu.1 hu.2.1 hF hFU z hz,
      hu.2.2 (F z) (hFU hz), mul_zero]

end D12Complex.HarmonicFoundation

