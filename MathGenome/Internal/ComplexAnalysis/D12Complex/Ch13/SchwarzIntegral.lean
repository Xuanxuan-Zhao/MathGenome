import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.SchwarzIntegral
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.DiskDirichlet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.RealComplexDifferential
import Mathlib.Analysis.Calculus.MeanValue

/-! Reconstruction from the continuous boundary values of the real part.
Dirichlet uniqueness identifies the real part of the Schwarz integral.
The real differential then shows the difference is constant; evaluation at
zero determines its imaginary part. -/

noncomputable section
open Complex Metric Set Filter InnerProductSpace
open scoped Topology

namespace D12Complex.SchwarzIntegral
open PoissonHarmonic

/-- CR in differential form: a holomorphic function with zero real part has
zero derivative. This requires only local complex differentiability. -/
lemma deriv_eq_zero_of_re_eq_zero {U : Set ℂ} {g : ℂ → ℂ}
    (hg : HolomorphicOn U g) (hr : ∀ z ∈ U, (g z).re = 0)
    {z : ℂ} (hz : z ∈ U) : deriv g z = 0 := by
  have hd := (hg.2 z hz).hasDerivAt.complexToReal_fderiv
  have hre := reCLM.hasFDerivAt.comp z hd
  have he : (fun w => (g w).re) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hg.1.mem_nhds hz] with w hw
    exact hr w hw
  have hzero := hre.congr_of_eventuallyEq he.symm
  have hmap := hzero.unique (hasFDerivAt_const (0 : ℝ) z)
  apply Complex.ext
  · have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) hmap
    simpa using h
  · have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L I) hmap
    simpa using h

/-- The Schwarz integral is real at its center. -/
lemma schwarzIntegral_im_zero (R : ℝ) (φ : ℂ → ℝ) :
    (schwarzIntegral R φ 0).im = 0 := by
  have hk (t : ℝ) :
      complexKernel 0 (circleMap 0 R t) * (φ (circleMap 0 R t) : ℂ) =
        ((if circleMap 0 R t = 0 then 0 else φ (circleMap 0 R t) : ℝ) : ℂ) := by
    by_cases h : circleMap 0 R t = 0 <;> simp [complexKernel, h]
  simp only [schwarzIntegral, hk, intervalIntegral.integral_ofReal, real_smul,
    mul_im, ofReal_re, ofReal_im, mul_zero, zero_mul, add_zero]

theorem schwarz_integral :
    Specs.D12Complex.Ch13.SchwarzIntegral.schwarz_integral_type := by
  intro R f φ hR hf hext z hz
  obtain ⟨u, hu, huf, hb⟩ := hext
  have hφ : ContinuousOn φ (sphere 0 R) :=
    (hu.mono sphere_subset_closedBall).congr (fun w hw => (hb hw).symm)
  have huH : HarmonicOn (ball 0 R) u := by
    apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mpr
    have hre := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp
      (HarmonicFoundation.holomorphic_harmonic_re _ _ hf)
    intro w hw
    have heq : (fun v => (f v).re) =ᶠ[𝓝 w] u := by
      filter_upwards [isOpen_ball.mem_nhds hw] with v hv
      exact (huf hv).symm
    exact (harmonicAt_congr_nhds heq).mp (hre w hw)
  have hreal (w : ℂ) (hw : w ∈ ball (0 : ℂ) R) :
      (schwarzIntegral R φ w).re = (f w).re := by
    have huni := DiskDirichlet.disk_dirichlet_unique R φ u hR hφ hu huH hb
      (ball_subset_closedBall hw)
    change u w = DiskDirichlet.closedPoissonIntegral R φ w at huni
    rw [DiskDirichlet.closedPoissonIntegral_eq_interior φ hw] at huni
    exact (schwarzIntegral_re R φ hR hφ w (by simpa using hw)).trans
      (huni.symm.trans (huf hw))
  let g := fun w => f w - schwarzIntegral R φ w
  have hg : HolomorphicOn (ball 0 R) g :=
    ⟨isOpen_ball, fun w hw => (hf.2 w hw).sub
      ((schwarzIntegral_holomorphic R φ hR hφ).2 w hw)⟩
  have hgr : ∀ w ∈ ball (0 : ℂ) R, (g w).re = 0 := by
    intro w hw
    simp only [g, sub_re, hreal w hw, sub_self]
  have hz' : z ∈ ball (0 : ℂ) R := by simpa using hz
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hc : g z = g 0 := isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℂ) R).isPreconnected
    (fun w hw => (hg.2 w hw).differentiableWithinAt)
    (fun w hw => deriv_eq_zero_of_re_eq_zero hg hgr hw) hz' h0
  have him : (f z).im = (schwarzIntegral R φ z).im + (f 0).im := by
    have h := congrArg Complex.im hc
    simp only [g, sub_im, schwarzIntegral_im_zero, sub_zero] at h
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h)
  change f z = schwarzIntegral R φ z + I * (f 0).im
  apply Complex.ext
  · simpa using (hreal z hz').symm
  · simpa using him

end D12Complex.SchwarzIntegral
