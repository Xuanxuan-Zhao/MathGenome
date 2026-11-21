import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierInversion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierConvention

open MeasureTheory
open scoped SchwartzMap FourierTransform

noncomputable section
namespace ExpandedFA.Fourier
namespace Inversion

theorem schwartz_automorphism :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.schwartzAutomorphismType := by
  intro d
  exact ⟨FourierTransform.fourierCLE ℂ (Schwartz ℂ d), fun _ => rfl, fun _ => rfl⟩

theorem fourier_square :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.fourierSquareType := by
  intro d f x
  have h := congrArg (fun g : Schwartz ℂ d => g (-x))
    (FourierTransform.fourierInv_fourier_eq (F := Schwartz ℂ d) f)
  change (𝓕 (𝓕 f) : Schwartz ℂ d) (-(-x)) = f (-x) at h
  simpa only [neg_neg, schwartzFourier, FourierTransform.fourierCLM_apply] using h

theorem inversion :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.inversionType := by
  intro d f x
  calc
    f x = (𝓕⁻ (𝓕 f) : Schwartz ℂ d) x := by rw [FourierTransform.fourierInv_fourier_eq]
    _ = ∫ ξ : Euclidean d,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) *
          schwartzFourier f ξ := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [schwartzFourier, FourierTransform.fourierCLM_apply, smul_eq_mul]
      congr 2
      rw [real_inner_comm ξ x]
      push_cast
      ring

theorem partial_apply :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.partialApplyType := by
  intro d i f x
  exact SchwartzMap.lineDerivOp_apply_eq_fderiv (basisVector i) f x

theorem fourier_partial :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.fourierPartialType := by
  intro d i f
  exact schwartz_fourier_partial i f

theorem fourier_coordinate :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.fourierCoordinateType := by
  intro d i f
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  rw [schwartz_partial_fourier]
  rw [smul_smul, neg_mul_neg, inv_mul_cancel₀ hc, one_smul]

theorem convolution_integral :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.convolutionIntegralType := by
  intro d f g x
  rw [SchwartzMap.convolution_apply, MeasureTheory.convolution_def]
  rfl

theorem fourier_convolution :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.fourierConvolutionType := by
  intro d f g ξ
  change (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g)) ξ = _
  rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
  rfl

theorem tempered_automorphism :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.temperedAutomorphismType := by
  intro d
  let e := (FourierTransform.fourierCLE ℂ (Schwartz ℂ d)).symm.arrowCongr
    (ContinuousLinearEquiv.refl ℂ ℂ)
  refine ⟨e, ?_, ?_⟩
  · intro u
    ext φ
    rfl
  · intro u φ
    rfl

theorem tempered_square :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.temperedSquareType := by
  intro d u φ
  change u (schwartzFourier (schwartzFourier φ)) = _
  congr 1
  ext x
  exact fourier_square d φ x

theorem regular_distribution_pairing :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.regularDistributionPairingType := by
  intro d f φ
  rfl

theorem fourier_regular_distribution :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.fourierRegularDistributionType := by
  intro d f
  ext φ
  change (∫ x : Euclidean d, f x * (𝓕 φ) x) = ∫ x : Euclidean d, (𝓕 f) x * φ x
  exact (SchwartzMap.integral_fourier_mul_eq f φ).symm

theorem tempered_fourier_partial :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.temperedFourierPartialType :=
  ExpandedFA.Fourier.fourier_partial

theorem tempered_fourier_coordinate :
    Specs.ExpandedFA.Fourier.SchwartzFourierInversion.temperedFourierCoordinateType :=
  ExpandedFA.Fourier.fourier_coordinate

end Inversion
end ExpandedFA.Fourier
