import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.PoissonHarmonic
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarmonicFoundation
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Tactic.Linarith

noncomputable section
open Complex Metric Real Set

namespace D12Complex.PoissonHarmonic

/-- The real Poisson kernel on the radius-R circle. -/
def kernel (R : ℝ) (z ζ : ℂ) : ℝ :=
  (R ^ 2 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2

/-- The complex kernel whose real part is the Poisson kernel. -/
def complexKernel (z ζ : ℂ) : ℂ := (ζ + z) / (ζ - z)

/-- The angular Poisson integral of real boundary data. -/
def poissonIntegral (R : ℝ) (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi,
    kernel R z (circleMap 0 R t) * φ (circleMap 0 R t)

/-- A specific holomorphic integral whose real part is the Poisson integral. -/
def schwarzIntegral (R : ℝ) (φ : ℂ → ℝ) (z : ℂ) : ℂ :=
  (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..2 * Real.pi,
    complexKernel z (circleMap 0 R t) * (φ (circleMap 0 R t) : ℂ)

theorem kernel_positive :
    Specs.D12Complex.Ch13.PoissonHarmonic.kernel_positive_type := by
  intro R hR z ζ hz hζ
  change 0 < kernel R z ζ
  have hne : ζ - z ≠ 0 := by
    intro he
    have : ζ = z := sub_eq_zero.mp he
    rw [this] at hζ
    exact hz.ne hζ
  apply div_pos
  · nlinarith [norm_nonneg z]
  · exact pow_pos (norm_pos_iff.mpr hne) 2

theorem kernel_eq_re :
    Specs.D12Complex.Ch13.PoissonHarmonic.kernel_eq_re_type := by
  intro R z ζ hζ
  change kernel R z ζ = (complexKernel z ζ).re
  have h := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := z)) ζ
  simpa only [poissonKernel_def, herglotzRieszKernel_def, Function.comp_apply,
    sub_zero, hζ, kernel, complexKernel] using h

lemma poissonIntegral_eq_circleAverage (R : ℝ) (φ : ℂ → ℝ) (z : ℂ) :
    poissonIntegral R φ z = circleAverage (poissonKernel 0 z • φ) 0 R := by
  simp [poissonIntegral, circleAverage_def, kernel, poissonKernel_def,
    norm_circleMap_zero, sq_abs, smul_eq_mul]

lemma schwarzIntegral_eq_circleAverage (R : ℝ) (φ : ℂ → ℝ) (z : ℂ) :
    schwarzIntegral R φ z =
      circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • (φ ζ : ℂ)) 0 R := by
  simp [schwarzIntegral, circleAverage_def, complexKernel, herglotzRieszKernel_def,
    smul_eq_mul]

private lemma not_on_circle {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R) :
    z ∉ sphere (0 : ℂ) |R| := by
  simpa only [mem_sphere_iff_norm, sub_zero, abs_of_pos hR] using hz.ne

private lemma boundary_integrable {R : ℝ} {φ : ℂ → ℝ} (hR : 0 < R)
    (hφ : ContinuousOn φ (sphere 0 R)) : CircleIntegrable φ 0 R :=
  hφ.circleIntegrable hR.le

private lemma boundary_complex_integrable {R : ℝ} {φ : ℂ → ℝ} (hR : 0 < R)
    (hφ : ContinuousOn φ (sphere 0 R)) :
    CircleIntegrable (fun ζ => (φ ζ : ℂ)) 0 R := by
  exact (Complex.continuous_ofReal.comp_continuousOn hφ).circleIntegrable hR.le

theorem schwarzIntegral_holomorphic :
    Specs.D12Complex.Ch13.PoissonHarmonic.schwarzIntegral_holomorphic_type := by
  intro R φ hR hφ
  change HolomorphicOn (ball 0 R) (schwarzIntegral R φ)
  refine ⟨isOpen_ball, fun z hz => ?_⟩
  have hz' : ‖z‖ < R := by simpa using hz
  simpa only [← schwarzIntegral_eq_circleAverage] using
    (hasDerivAt_circleAverage_herglotzRieszKernel_smul
      (boundary_complex_integrable hR hφ) (not_on_circle hR hz')).differentiableAt

theorem schwarzIntegral_re :
    Specs.D12Complex.Ch13.PoissonHarmonic.schwarzIntegral_re_type := by
  intro R φ hR hφ z hz
  change (schwarzIntegral R φ z).re = poissonIntegral R φ z
  rw [schwarzIntegral_eq_circleAverage, poissonIntegral_eq_circleAverage]
  rw [re_circleAverage_herglotzRieszKernel_smul
    (boundary_integrable hR hφ) (not_on_circle hR hz)]
  rw [poissonKernel_eq_re_herglotzRieszKernel]

theorem kernel_normalized :
    Specs.D12Complex.Ch13.PoissonHarmonic.kernel_normalized_type := by
  intro R hR z hz
  change (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..2 * Real.pi,
    kernel R z (circleMap 0 R t)) = 1
  have hc : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (ball 0 R) :=
    diffContOnCl_const
  have h := hc.circleAverage_poissonKernel_smul (by simpa using hz)
  have hi : CircleIntegrable (fun ζ => (poissonKernel 0 z ζ : ℂ)) 0 R := by
    have hk : ContinuousOn (poissonKernel 0 z) (sphere 0 R) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      exact Complex.continuous_re.comp_continuousOn
        (by simpa only [abs_of_pos hR] using
          continuousOn_herglotzRieszKernel_sphere (not_on_circle hR hz))
    exact (Complex.continuous_ofReal.comp_continuousOn hk).circleIntegrable hR.le
  have hr := congrArg Complex.re h
  simp only [Pi.smul_def', real_smul, mul_one] at hr
  have hm : circleAverage (poissonKernel 0 z) 0 R =
      (circleAverage (fun ζ => (poissonKernel 0 z ζ : ℂ)) 0 R).re := by
    simpa [Function.comp_def] using Complex.reCLM.circleAverage_comp_comm hi
  have hr' := hm.trans hr
  simpa [circleAverage_def, kernel, poissonKernel_def, norm_circleMap_zero, sq_abs,
    Function.comp_def, smul_eq_mul] using hr'

theorem integrands_integrable :
    Specs.D12Complex.Ch13.PoissonHarmonic.integrands_integrable_type := by
  intro R φ hR hφ z hz
  change IntervalIntegrable (fun t => kernel R z (circleMap 0 R t) *
    φ (circleMap 0 R t)) MeasureTheory.volume 0 (2 * Real.pi) ∧
    IntervalIntegrable (fun t => complexKernel z (circleMap 0 R t) *
      (φ (circleMap 0 R t) : ℂ)) MeasureTheory.volume 0 (2 * Real.pi)
  have hw := not_on_circle hR hz
  have hkc : ContinuousOn (herglotzRieszKernel 0 z) (sphere 0 R) := by
    simpa only [abs_of_pos hR] using continuousOn_herglotzRieszKernel_sphere hw
  have hk : ContinuousOn (poissonKernel 0 z) (sphere 0 R) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn hkc
  constructor
  · have h := (hk.mul hφ).circleIntegrable hR.le
    simpa [CircleIntegrable, kernel, poissonKernel_def, norm_circleMap_zero, sq_abs] using h
  · have h := (hkc.mul (Complex.continuous_ofReal.comp_continuousOn hφ)).circleIntegrable hR.le
    simpa [CircleIntegrable, complexKernel, herglotzRieszKernel_def] using h

theorem poissonIntegral_harmonic :
    Specs.D12Complex.Ch13.PoissonHarmonic.poissonIntegral_harmonic_type := by
  intro R φ hR hφ
  change HarmonicOn (ball 0 R) (poissonIntegral R φ)
  have hh := HarmonicFoundation.holomorphic_harmonic_re _ _
    (schwarzIntegral_holomorphic R φ hR hφ)
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mpr
  have hh' := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp hh
  intro z hz
  have heq : (fun w => (schwarzIntegral R φ w).re) =ᶠ[nhds z] poissonIntegral R φ := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact schwarzIntegral_re R φ hR hφ w (by simpa using hw)
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mp (hh' z hz)

end D12Complex.PoissonHarmonic
