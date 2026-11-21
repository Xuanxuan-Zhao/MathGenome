import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Independent statements for paper.tex:1034–1041, with the conventions at
paper.tex:47–56 and 1015–1022. No positivity assumption on the dimension is made.
In particular a zero-dimensional space has its standard volume of mass one. -/
noncomputable section
open MeasureTheory

namespace P102.U3.FourierConvolutionExpected

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The manuscript's negative-sign, 2π Fourier kernel. -/
def kernel (x ξ : E) : ℂ :=
  Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) : ℂ) * Complex.I)

/-- The integral Fourier representative for standard Euclidean volume. -/
def transform (f : E → ℂ) (ξ : E) : ℂ := ∫ x, kernel x ξ * f x

/-- The order in the manuscript is f(x-y)g(y). This is a totalized integral;
absolute existence is asserted only almost everywhere. -/
def convolution (f g : E → ℂ) (x : E) : ℂ := ∫ y, f (x - y) * g y

/-- L¹ closure and Fourier multiplication for every representative of the
convolution class, together with independence of the two input representatives. -/
def Result (f g : E → ℂ) : Prop :=
  (∀ᵐ x, Integrable (fun y => f (x - y) * g y)) ∧
  Integrable (convolution f g) ∧
  Continuous (transform f) ∧ Continuous (transform g) ∧
  (∀ h : E → ℂ, h =ᵐ[volume] convolution f g →
    Continuous (transform h) ∧
    ∀ ξ, transform h ξ = transform f ξ * transform g ξ) ∧
  ∀ f' g' : E → ℂ, f =ᵐ[volume] f' → g =ᵐ[volume] g' →
    convolution f g = convolution f' g'

/-- Completion is explicit in all integral and integrability assertions. -/
def completedTransform (f : E → ℂ) (ξ : E) : ℂ :=
  ∫ x : NullMeasurableSpace E volume, kernel (E := E) x ξ * f x ∂volume.completion

def completedConvolution (f g : E → ℂ) (x : E) : ℂ :=
  ∫ y : NullMeasurableSpace E volume, f (@Sub.sub E _ x y) * g y ∂volume.completion

def CompletedResult (f g : E → ℂ) : Prop :=
  (∀ᵐ x ∂volume.completion,
    Integrable (fun y : NullMeasurableSpace E volume => f (@Sub.sub E _ x y) * g y)
      volume.completion) ∧
  Integrable (α := NullMeasurableSpace E volume) (completedConvolution (E := E) f g)
    volume.completion ∧
  Continuous (completedTransform f) ∧ Continuous (completedTransform g) ∧
  (∀ h : E → ℂ, h =ᵐ[volume.completion] completedConvolution (E := E) f g →
    Continuous (completedTransform h) ∧
    ∀ ξ, completedTransform h ξ = completedTransform f ξ * completedTransform g ξ) ∧
  ∀ f' g' : E → ℂ, f =ᵐ[volume.completion] f' → g =ᵐ[volume.completion] g' →
    completedConvolution f g = completedConvolution f' g'

def FourierConvolution : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f g : E → ℂ), Integrable f → Integrable g → Result f g

def CompletedFourierConvolution : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f g : E → ℂ),
    Integrable (α := NullMeasurableSpace E volume) f volume.completion →
    Integrable (α := NullMeasurableSpace E volume) g volume.completion →
    CompletedResult f g

end P102.U3.FourierConvolutionExpected
