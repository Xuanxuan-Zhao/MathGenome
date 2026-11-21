import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! Independent statements for the Schwartz and tempered-distribution parts of
`paper.tex`, fa2:p4:fourier-inversion (17385–17426). The L² extension is assigned
separately to Plancherel. All dimensions, including zero, are retained. -/

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace ExpandedFA.Fourier

/-- A Schwartz function as a continuous scalar-linear integral functional. -/
noncomputable def schwartzRegularDistribution {d : ℕ} (f : Schwartz ℂ d) : Tempered ℂ d :=
  (SchwartzMap.integralCLM ℂ (volume : Measure (Euclidean d))).comp
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f)

end ExpandedFA.Fourier

namespace Specs.ExpandedFA.Fourier.SchwartzFourierInversion
open _root_.ExpandedFA.Fourier

/-- The specified integral Fourier transform is a continuous linear
automorphism, and its inverse is the native positive-sign transform. -/
def schwartzAutomorphismType : Prop := ∀ d : ℕ,
  ∃ e : Schwartz ℂ d ≃L[ℂ] Schwartz ℂ d,
    (∀ f, e f = schwartzFourier f) ∧ (∀ f, e.symm f = 𝓕⁻ f)

def fourierSquareType : Prop := ∀ (d : ℕ) (f : Schwartz ℂ d) (x : Euclidean d),
  schwartzFourier (schwartzFourier f) x = f (-x)

def inversionType : Prop := ∀ (d : ℕ) (f : Schwartz ℂ d) (x : Euclidean d),
  f x = ∫ ξ : Euclidean d,
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) *
      schwartzFourier f ξ

/-- The coordinate derivative operator used below is the ordinary derivative
in that coordinate, on the original underlying smooth function. -/
def partialApplyType : Prop := ∀ (d : ℕ) (i : Fin d) (f : Schwartz ℂ d) (x : Euclidean d),
  LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) f x =
    fderiv ℝ f x (basisVector i)

def fourierPartialType : Prop := ∀ (d : ℕ) (i : Fin d) (f : Schwartz ℂ d),
  schwartzFourier (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) f) =
    (2 * (Real.pi : ℂ) * Complex.I) • coordinateMultiply i (schwartzFourier f)

def fourierCoordinateType : Prop := ∀ (d : ℕ) (i : Fin d) (f : Schwartz ℂ d),
  schwartzFourier (coordinateMultiply i f) =
    (-(2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
      LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) (schwartzFourier f)

/-- Schwartz convolution really is the integral convolution. In particular its
native Schwartz representative proves closure of the space under convolution. -/
def convolutionIntegralType : Prop := ∀ (d : ℕ) (f g : Schwartz ℂ d) (x : Euclidean d),
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g x =
    ∫ y : Euclidean d, f y * g (x - y)

def fourierConvolutionType : Prop := ∀ (d : ℕ) (f g : Schwartz ℂ d) (ξ : Euclidean d),
  schwartzFourier (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g) ξ =
    schwartzFourier f ξ * schwartzFourier g ξ

/-- Transposition on the continuous scalar-linear dual, with its topology of
uniform convergence on bounded sets. Neither pairing conjugates the test. -/
def temperedAutomorphismType : Prop := ∀ d : ℕ,
  ∃ e : Tempered ℂ d ≃L[ℂ] Tempered ℂ d,
    (∀ u, e u = temperedFourier u) ∧
      (∀ u φ, e.symm u φ = u (𝓕⁻ φ))

def temperedSquareType : Prop := ∀ (d : ℕ) (u : Tempered ℂ d) (φ : Schwartz ℂ d),
  temperedFourier (temperedFourier u) φ =
    u (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := Euclidean d)) φ)

def regularDistributionPairingType : Prop := ∀ (d : ℕ) (f φ : Schwartz ℂ d),
  schwartzRegularDistribution f φ = ∫ x : Euclidean d, f x * φ x

/-- The transpose extends the classical transform on regular Schwartz
distributions, rather than merely providing an unrelated dual automorphism. -/
def fourierRegularDistributionType : Prop := ∀ (d : ℕ) (f : Schwartz ℂ d),
  temperedFourier (schwartzRegularDistribution f) =
    schwartzRegularDistribution (schwartzFourier f)

def temperedFourierPartialType : Prop := ∀ (d : ℕ) (i : Fin d) (u : Tempered ℂ d),
  temperedFourier (temperedPartial i u) =
    (2 * (Real.pi : ℂ) * Complex.I) • temperedCoordinateMultiply i (temperedFourier u)

def temperedFourierCoordinateType : Prop := ∀ (d : ℕ) (i : Fin d) (u : Tempered ℂ d),
  temperedFourier (temperedCoordinateMultiply i u) =
    (-(2 * (Real.pi : ℂ) * Complex.I)⁻¹) • temperedPartial i (temperedFourier u)

end Specs.ExpandedFA.Fourier.SchwartzFourierInversion
