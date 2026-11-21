import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.LocalConjugateRegularity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarmonicFoundation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.CauchyRiemannRegularity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.TaylorSmoothness
import Mathlib.Analysis.Complex.Harmonic.Analytic

noncomputable section
open Complex InnerProductSpace Set Metric
open scoped Topology ContDiff

namespace D12Complex.LocalConjugateRegularity

abbrev HarmonicConjugateOn := D12Complex.HarmonicConjugateOn

theorem conjugate_harmonic :
    Specs.D12Complex.Ch13.LocalConjugateRegularity.conjugate_harmonic_type := by
  intro U u v h
  constructor
  · simpa using HarmonicFoundation.holomorphic_harmonic_re U _ h
  · simpa using HarmonicFoundation.holomorphic_harmonic_im U _ h

theorem conjugate_partials :
    Specs.D12Complex.Ch13.LocalConjugateRegularity.conjugate_partials_type := by
  intro U u v h z hz
  have hc := cauchyRiemann_of_holomorphicOn U _ h z hz
  simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
    zero_mul, one_mul, sub_zero, add_zero, add_im, mul_im, zero_add] at hc
  exact ⟨by linarith [hc.2], hc.1.symm⟩

/-- Mathlib constructs a primitive of u_x - i u_y on a disk and fixes its
real part by matching the differential and one basepoint value. Its premise
is exactly C² harmonicity after the upstream Laplacian bridge. -/
lemma local_holomorphic_real_part (U : Set ℂ) (u : ℂ → ℝ)
    (hu : HarmonicOn U u) (a : ℂ) (ha : a ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ U ∧ ∃ F : ℂ → ℂ,
      HolomorphicOn (ball a r) F ∧ EqOn (fun z => (F z).re) u (ball a r) := by
  obtain ⟨r, hr, hsub⟩ := isOpen_iff.mp hu.1 a ha
  have hh := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U u hu.1).mp hu
  obtain ⟨F, hF, hre⟩ := (hh.mono hsub).exists_analyticOnNhd_ball_re_eq
  exact ⟨r, hr, hsub, F, ⟨isOpen_ball, fun z hz => (hF z hz).differentiableAt⟩, hre⟩

theorem local_conjugate :
    Specs.D12Complex.Ch13.LocalConjugateRegularity.local_conjugate_type := by
  intro U u hu a ha
  obtain ⟨r, hr, hsub, F, hF, hre⟩ := local_holomorphic_real_part U u hu a ha
  refine ⟨r, hr, hsub, fun z => (F z).im,
    HarmonicFoundation.holomorphic_harmonic_im _ F hF, isOpen_ball, ?_⟩
  intro z hz
  apply (hF.2 z hz).congr_of_eventuallyEq
  have heq : EqOn (fun w => (u w : ℂ) + I * ((F w).im : ℂ)) F (ball a r) := by
    intro w hw
    change (u w : ℂ) + I * ((F w).im : ℂ) = F w
    rw [← hre hw]
    exact Complex.ext (by simp) (by simp)
  exact heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)

theorem harmonic_real_analytic :
    Specs.D12Complex.Ch13.LocalConjugateRegularity.harmonic_real_analytic_type := by
  intro U u hu a ha
  obtain ⟨r, hr, _, F, hF, hre⟩ := local_holomorphic_real_part U u hu a ha
  have haF : AnalyticAt ℂ F a :=
    (show DifferentiableOn ℂ F (ball a r) from
      fun z hz => (hF.2 z hz).differentiableWithinAt).analyticAt (ball_mem_nhds a hr)
  have haRe : AnalyticAt ℝ (fun z => (F z).re) a :=
    (reCLM.analyticAt (F a)).comp haF.restrictScalars
  exact haRe.congr (hre.eventuallyEq_of_mem (ball_mem_nhds a hr))

theorem harmonic_smooth :
    Specs.D12Complex.Ch13.LocalConjugateRegularity.harmonic_smooth_type := by
  intro U u hu a ha
  exact (harmonic_real_analytic U u hu a ha).contDiffAt.contDiffWithinAt

theorem harmonic_real_taylor :
    Specs.D12Complex.Ch13.LocalConjugateRegularity.harmonic_real_taylor_type := by
  intro U u hu a ha
  obtain ⟨r, hr, hsub, F, hF, hre⟩ := local_holomorphic_real_part U u hu a ha
  refine ⟨r, hr, hsub, F, hF, hre, fun z hz => ?_⟩
  have hball : eball a (ENNReal.ofReal r) = ball a r := by
    ext w
    simp [mem_ball]
  have hs := TaylorSmoothness.taylor_hasSum a (ENNReal.ofReal r) F
    (by simpa using hr) (by simpa only [hball] using hF) z
    (by simpa only [hball] using hz)
  exact ⟨hs, by simpa only [reCLM_apply, hre hz] using hs.mapL reCLM⟩

end D12Complex.LocalConjugateRegularity
