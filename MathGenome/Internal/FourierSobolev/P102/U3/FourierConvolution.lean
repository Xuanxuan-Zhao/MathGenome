import Mathlib.Analysis.Fourier.Convolution
import MathGenome.Internal.FourierSobolev.P102.U2.Young
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.FourierConvolution

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace P102.U3.FourierConvolution

open FourierConvolutionExpected

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Native Fourier transformation uses precisely the manuscript's exponential. -/
lemma transform_eq_fourier (f : E → ℂ) : transform f = 𝓕 f := by
  funext ξ
  simp only [transform, kernel, Real.fourier_eq', smul_eq_mul]

/-- Native convolution places its first input at y. Swapping the inputs and
using commutativity gives f(x-y)g(y), including for totalized integrals. -/
lemma convolution_eq_library (f g : E → ℂ) :
    convolution f g = MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  simp only [FourierConvolutionExpected.convolution, MeasureTheory.convolution_def,
    ContinuousLinearMap.mul_apply', mul_comm]

/-- The joint integrand is integrable, which justifies the Fubini interchange
in the Fourier product theorem without requiring existence at every x. -/
lemma integrable_joint {f g : E → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : E × E => f (p.1 - p.2) * g p.2) (volume.prod volume) := by
  simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
    hg.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf

lemma continuous_transform {f : E → ℂ} (hf : Integrable f) : Continuous (transform f) := by
  rw [transform_eq_fourier]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

lemma transform_congr {f g : E → ℂ} (h : f =ᵐ[volume] g) : transform f = transform g := by
  simp only [transform_eq_fourier]
  funext ξ
  exact Real.fourier_congr_ae h ξ

/-- The Fourier integrals are absolutely convergent at every frequency. -/
lemma integrable_fourier_integrand {f : E → ℂ} (hf : Integrable f) (ξ : E) :
    Integrable (fun x => kernel x ξ * f x) := by
  simpa only [kernel, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul,
    smul_eq_mul] using (Real.fourierIntegral_convergent_iff ξ).mpr hf

/-- All finite dimensions, including zero, with standard Euclidean volume. -/
theorem fourier_convolution : FourierConvolutionExpected.FourierConvolution := by
  intro E _ _ _ _ _ f g hf hg
  have hc : Integrable (convolution f g) := by
    rw [convolution_eq_library]
    exact hg.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  refine ⟨?_, hc, continuous_transform hf, continuous_transform hg, ?_, ?_⟩
  · filter_upwards [hg.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hf] with x hx
    simpa only [MeasureTheory.ConvolutionExistsAt, ContinuousLinearMap.mul_apply', mul_comm] using hx
  · intro h hh
    have hh' : Integrable h := hc.congr hh.symm
    refine ⟨continuous_transform hh', ?_⟩
    intro ξ
    rw [transform_congr hh, transform_eq_fourier, transform_eq_fourier,
      transform_eq_fourier, convolution_eq_library,
      Real.fourier_mul_convolution_eq hg hf, mul_comm]
  · intro f' g' hf' hg'
    simp only [convolution_eq_library]
    exact MeasureTheory.convolution_congr (ContinuousLinearMap.mul ℂ ℂ) hg' hf'

/-- The completed integral equals the Borel-space totalized integral. This
also holds for nonintegrable functions, as proved in the upstream interface. -/
lemma completedTransform_eq (f : E → ℂ) : completedTransform f = transform f := by
  funext ξ
  exact P102.U2.Young.integral_completion volume (fun x : E => kernel x ξ * f x)

lemma completedConvolution_eq (f g : E → ℂ) :
    completedConvolution f g = convolution f g := by
  funext x
  exact P102.U2.Young.integral_completion volume (fun y : E => f (x - y) * g y)

/-- A completed-Lebesgue L¹ input admits a Borel-measurable L¹ replacement.
Transferring back along that a.e. equality supplies exactly the integrability
hypothesis expected by the native convolution and Fourier theorems. -/
lemma integrable_completed_iff (f : E → ℂ) :
    Integrable (α := NullMeasurableSpace E volume) f volume.completion ↔ Integrable f := by
  constructor
  · intro hf
    obtain ⟨f₀, _hf₀meas, hff₀, hf₀, _hnorm, _hint⟩ :=
      P102.U2.Young.completed_borel_representative volume (memLp_one_iff_integrable.mpr hf)
    exact (memLp_one_iff_integrable.mp hf₀).congr hff₀.symm
  · intro hf
    exact memLp_one_iff_integrable.mp
      ((P102.Periodic.mem_completion volume f 1).mpr (memLp_one_iff_integrable.mpr hf))

/-- The same theorem for completed-Lebesgue representatives, with completed
integrals throughout and no additional pointwise existence assumption. -/
theorem completed_fourier_convolution :
    FourierConvolutionExpected.CompletedFourierConvolution := by
  intro E _ _ _ _ _ f g hf hg
  have hf' := (integrable_completed_iff f).mp hf
  have hg' := (integrable_completed_iff g).mp hg
  have hmain := fourier_convolution E f g hf' hg'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hmain.1] with x hx
    exact (integrable_completed_iff (fun y : E => f (x - y) * g y)).mpr hx
  · rw [completedConvolution_eq]
    exact (integrable_completed_iff (convolution f g)).mpr hmain.2.1
  · simpa only [completedTransform_eq] using hmain.2.2.1
  · simpa only [completedTransform_eq] using hmain.2.2.2.1
  · intro h hh
    rw [completedConvolution_eq] at hh
    simpa only [completedTransform_eq] using hmain.2.2.2.2.1 h hh
  · intro f' g' hff' hgg'
    simp only [completedConvolution_eq]
    exact hmain.2.2.2.2.2 f' g' hff' hgg'

end P102.U3.FourierConvolution
