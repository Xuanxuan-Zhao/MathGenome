import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Basic

/-! Independent statements of the smooth part of `fa2:p4:paley-wiener`,
 paper.tex:17453–17493. No positive dimension or interior assumption is imposed.
 Complex frequencies have their Euclidean norm. The complex pairing in the
 exponential is bilinear, and the real integration measure is Lebesgue volume. -/

open MeasureTheory Set
open scoped ContDiff

namespace ExpandedFA.Fourier.PaleyWiener

abbrev ComplexEuclidean (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- The ordinary inclusion of real frequencies in complex frequencies. -/
def realFrequency {d : ℕ} (ξ : Euclidean d) : ComplexEuclidean d :=
  WithLp.toLp 2 (fun j => (ξ j : ℂ))

/-- Imaginary parts in real Euclidean coordinates. -/
def imaginaryPart {d : ℕ} (z : ComplexEuclidean d) : Euclidean d :=
  WithLp.toLp 2 (fun j => (z j).im)

/-- The bilinear pairing x·z; no conjugation of z occurs. -/
def complexPairing {d : ℕ} (x : Euclidean d) (z : ComplexEuclidean d) : ℂ :=
  ∑ j, (x j : ℂ) * z j

noncomputable def supportFunction {d : ℕ} (K : Set (Euclidean d)) (η : Euclidean d) : ℝ :=
  sSup ((fun x => inner ℝ x η) '' K)

noncomputable def fourierLaplace {d : ℕ} (f : Euclidean d → ℂ)
    (z : ComplexEuclidean d) : ℂ :=
  ∫ x, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * complexPairing x z) * f x

/-- Under the compactness hypothesis on K this is precisely smooth compact
 support in K, including when K has empty interior. -/
def SmoothSupportedIn {d : ℕ} (K : Set (Euclidean d)) (f : Euclidean d → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ tsupport f ⊆ K

/-- Every natural decay order has a constant uniform over all complex z. -/
def RapidExponentialType {d : ℕ} (K : Set (Euclidean d))
    (F : ComplexEuclidean d → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
    ‖F z‖ ≤ C * (1 + ‖z‖) ^ (-(N : ℤ)) *
      Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z))

noncomputable def inverseRealIntegral {d : ℕ} (F : ComplexEuclidean d → ℂ)
    (x : Euclidean d) : ℂ :=
  ∫ ξ : Euclidean d,
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) *
      F (realFrequency ξ)

end ExpandedFA.Fourier.PaleyWiener

namespace Specs.ExpandedFA.Fourier.SmoothPaleyWiener
open _root_.ExpandedFA.Fourier
open _root_.ExpandedFA.Fourier.PaleyWiener

/-- Forward half, including the precise support function in the exponential. -/
def forwardType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K → ∀ f : Euclidean d → ℂ,
  SmoothSupportedIn K f →
  Differentiable ℂ (fourierLaplace f) ∧ RapidExponentialType K (fourierLaplace f)

/-- The converse uses the actual inverse real Fourier integral and proves its
 support as well as the complex transform identity, without an interior condition. -/
def inverseType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K → ∀ F : ComplexEuclidean d → ℂ,
  Differentiable ℂ F → RapidExponentialType K F →
  SmoothSupportedIn K (inverseRealIntegral F) ∧
    fourierLaplace (inverseRealIntegral F) = F

/-- Exact characterization of all transforms, not merely real-axis agreement. -/
def characterizationType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K → ∀ F : ComplexEuclidean d → ℂ,
  (∃ f : Euclidean d → ℂ, SmoothSupportedIn K f ∧ fourierLaplace f = F) ↔
    Differentiable ℂ F ∧ RapidExponentialType K F

/-- Compatibility with the adopted real Fourier normalization. -/
def realRestrictionType : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ) (ξ : Euclidean d),
  fourierLaplace f (realFrequency ξ) = integralFourier f ξ

/-- The exact modulus used in exponential type estimates. -/
def kernelNormType : Prop := ∀ (d : ℕ) (x : Euclidean d) (z : ComplexEuclidean d),
  ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * complexPairing x z)‖ =
    Real.exp (2 * Real.pi * inner ℝ x (imaginaryPart z))

/-- Strict separation in the form needed to prove support of the inverse. -/
def separationType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K → ∀ x, x ∉ K →
  ∃ η : Euclidean d, supportFunction K η < inner ℝ x η

/-- A useful proved base case of the forward estimate. It does not assert
 the remaining inverse powers or holomorphy. -/
def zerothBoundType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → ∀ f : Euclidean d → ℂ,
  SmoothSupportedIn K f → ∀ z : ComplexEuclidean d,
  ‖fourierLaplace f z‖ ≤ (∫ x, ‖f x‖) *
    Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z))

/-- Inversion for smooth functions supported in a compact set, using the
 adopted Schwartz inversion theorem. -/
def smoothInversionType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  IsCompact K → ∀ f : Euclidean d → ℂ, SmoothSupportedIn K f →
  inverseRealIntegral (fourierLaplace f) = f

/-- In particular the entire transform identifies its smooth compactly
 supported preimage uniquely. -/
def injectivityType : Prop := ∀ (d : ℕ) (K L : Set (Euclidean d)),
  IsCompact K → IsCompact L → ∀ f g : Euclidean d → ℂ,
  SmoothSupportedIn K f → SmoothSupportedIn L g →
  fourierLaplace f = fourierLaplace g → f = g

/-- Convergence and continuity of the specified inverse integral, as a first
 stage of the smooth converse. -/
def inverseConvergenceType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → ∀ F : ComplexEuclidean d → ℂ,
  Differentiable ℂ F → RapidExponentialType K F →
  (∀ x : Euclidean d, Integrable (fun ξ : Euclidean d =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) *
      F (realFrequency ξ))) ∧ Continuous (inverseRealIntegral F)

/-- Arbitrary real smoothness of the specified inverse integral. -/
def inverseSmoothnessType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → ∀ F : ComplexEuclidean d → ℂ,
  Differentiable ℂ F → RapidExponentialType K F →
  ContDiff ℝ ∞ (inverseRealIntegral F)

end Specs.ExpandedFA.Fourier.SmoothPaleyWiener
