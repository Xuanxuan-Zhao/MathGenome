import MathGenome.Internal.FourierSobolev.P102.U3.SchwartzFourier
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.FourierInversion
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace P102.U3.FourierInversion

section Euclidean
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Bilinear transposition of the integral Fourier transform. Both factors are
L¹, so Fubini applies without any integrability assumption on their transforms. -/
theorem integral_fourier_mul (f g : V → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  simpa using!
    (VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner hf hg)

/-- The positive-sign transform has the same bilinear transposition identity. -/
theorem integral_check_mul (f g : V → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕⁻ f x * g x) = ∫ x, f x * 𝓕⁻ g x := by
  have hflip : (-innerₗ V).flip = -innerₗ V := by
    ext x y
    simp [real_inner_comm]
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := -innerₗ V)
    Real.continuous_fourierChar continuous_inner.neg hf hg
  rw [hflip] at h
  exact h

/-- Continuity follows from integrability of the input to the positive-sign transform. -/
theorem continuous_check {f : V → ℂ} (hf : Integrable f) : Continuous (𝓕⁻ f) := by
  have h : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have heq : 𝓕⁻ f = fun x => 𝓕 f (-x) := funext (Real.fourierInv_eq_fourier_neg f)
  rw [heq]
  exact h.comp continuous_neg

/-- Full almost-everywhere inversion. Test against a compactly supported smooth
function, apply transposition twice and Schwartz inversion, and then use
uniqueness of locally integrable functions from their test integrals. -/
theorem fourierInv_fourier_ae {f : V → ℂ} (hf : Integrable f)
    (hF : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) =ᵐ[volume] f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (continuous_check hF).locallyIntegrable hf.locallyIntegrable
  intro g hg hgc
  let φ : SchwartzMap V ℂ :=
    SchwartzMap.postcompCLM Complex.ofRealCLM (hgc.toSchwartzMap hg)
  have hφ (x : V) : φ x = (g x : ℂ) := rfl
  have hInv : ((𝓕⁻ φ : SchwartzMap V ℂ) : V → ℂ) = 𝓕⁻ (φ : V → ℂ) := SchwartzMap.fourierInv_coe φ
  have hPair : 𝓕 (𝓕⁻ (φ : V → ℂ)) = (φ : V → ℂ) := by
    rw [← hInv, ← SchwartzMap.fourier_coe]
    exact congrArg (fun ψ : SchwartzMap V ℂ => (ψ : V → ℂ))
      (FourierTransform.fourier_fourierInv_eq φ)
  calc
    (∫ x, g x • 𝓕⁻ (𝓕 f) x) = ∫ x, 𝓕⁻ (𝓕 f) x * φ x := by
      simp only [hφ, Complex.real_smul, mul_comm]
    _ = ∫ x, 𝓕 f x * 𝓕⁻ (φ : V → ℂ) x :=
      integral_check_mul _ _ hF φ.integrable
    _ = ∫ x, f x * 𝓕 (𝓕⁻ (φ : V → ℂ)) x :=
      integral_fourier_mul _ _ hf (hInv ▸ (𝓕⁻ φ).integrable)
    _ = ∫ x, g x • f x := by
      rw [hPair]
      simp only [hφ, Complex.real_smul, mul_comm]

end Euclidean

theorem l1_inversion : P102.Specs.U3.FourierInversion.l1Inversion_type := by
  intro d f hf hF
  exact ⟨continuous_check hF, fourierInv_fourier_ae hf hF,
    fun _ hx => hf.fourierInv_fourier_eq hF hx⟩

theorem schwartz_inversion : P102.Specs.U3.FourierInversion.schwartzInversion_type := by
  intro d
  refine ⟨?_, ?_, (P102.Specs.U3.fourierValue d).continuous,
    (P102.Specs.U3.checkValue d).continuous⟩
  · ext φ x
    change (𝓕⁻ (𝓕 φ : Test d) : Test d) x = φ x
    exact congrArg (fun ψ : Test d => ψ x) (FourierTransform.fourierInv_fourier_eq φ)
  · ext φ x
    change (𝓕 (𝓕⁻ φ : Test d) : Test d) x = φ x
    exact congrArg (fun ψ : Test d => ψ x) (FourierTransform.fourier_fourierInv_eq φ)

end P102.U3.FourierInversion
