import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SmoothPaleyWiener
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.TemperedExamples

/-! Distribution form of `fa2:p4:paley-wiener`, paper.tex:17453–17510.
The LF distributions use ordinary real coordinates, while the frequency norm
is Euclidean. All dimensions, including zero, are allowed. The transform is
specified by the unique continuous extension to smooth functions. Its existence
is an upstream theorem, not an additional assumption on the distributions.
No claim relates the growth exponent to the least distribution order. -/

open Set TopologicalSpace MeasureTheory
open scoped ContDiff Pointwise

noncomputable section
namespace ExpandedFA.Fourier.DistributionPaleyWiener
open ExpandedFA.Distributions ExpandedFA.Fourier.PaleyWiener

abbrev Distribution (d : ℕ) := ScalarDistribution ℂ (⊤ : Opens (Domain d))
abbrev Smooth (d : ℕ) := SmoothFunctions ℂ (⊤ : Opens (Domain d))

/-- Transport the actual LF distribution support to Euclidean coordinates. -/
def euclideanSupport {d : ℕ} (u : Distribution d) : Set (Euclidean d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm '' distributionSupport u

def SupportedIn {d : ℕ} (K : Set (Euclidean d)) (u : Distribution d) : Prop :=
  euclideanSupport u ⊆ K

/-- The smooth exponential, without any conjugation in the pairing. -/
def laplaceKernel {d : ℕ} (z : ComplexEuclidean d) : Smooth d :=
  ⟨fun x => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      ∑ j, Complex.ofRealCLM (x j) * z j),
    (by fun_prop : ContDiff ℝ ∞ (fun x : Domain d => Complex.exp
      (-2 * (Real.pi : ℂ) * Complex.I * ∑ j, Complex.ofRealCLM (x j) * z j))).contDiffOn,
    by simp⟩

/-- A total choice of extension. All theorems using this definition prove
compactness of the actual support before using the extension property. -/
def smoothExtension {d : ℕ} (u : Distribution d) : Smooth d →L[ℂ] ℂ :=
  Classical.epsilon (fun L => ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
    L (testToSmoothLM ℂ ⊤ φ) = u φ)

def fourierLaplace {d : ℕ} (u : Distribution d) (z : ComplexEuclidean d) : ℂ :=
  smoothExtension u (laplaceKernel z)

/-- A single finite polynomial degree and a single constant, uniform in all
complex frequencies. The exponent need not be the distribution's order. -/
def PolynomialExponentialType {d : ℕ} (K : Set (Euclidean d))
    (F : ComplexEuclidean d → ℂ) : Prop :=
  ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z,
    ‖F z‖ ≤ C * (1 + ‖z‖) ^ M *
      Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z))

end ExpandedFA.Fourier.DistributionPaleyWiener

namespace Specs.ExpandedFA.Fourier.DistributionPaleyWiener
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Fourier
open _root_.ExpandedFA.Fourier.PaleyWiener
open _root_.ExpandedFA.Fourier.DistributionPaleyWiener

/-- Entire differentiability for the actual compact-support Fourier--Laplace transform. -/
def entireType : Prop := ∀ (d : ℕ) (u : Distribution d),
  IsCompact (euclideanSupport u) →
    Differentiable ℂ (DistributionPaleyWiener.fourierLaplace u)

/-- Every distribution supported in K has an entire transform with the exact
support-function exponential factor. No order estimate is assumed. -/
def forwardType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K → ∀ u : Distribution d,
  SupportedIn K u → Differentiable ℂ (DistributionPaleyWiener.fourierLaplace u) ∧
    PolynomialExponentialType K (DistributionPaleyWiener.fourierLaplace u)

/-- The converse existence assertion with its actual canonical complex transform. -/
def inverseExistenceType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K → ∀ F : ComplexEuclidean d → ℂ,
  Differentiable ℂ F → PolynomialExponentialType K F →
    ∃ u : Distribution d, SupportedIn K u ∧ DistributionPaleyWiener.fourierLaplace u = F

/-- Every entire function with the stated growth has exactly one inverse
LF-continuous scalar-linear distribution supported in the given K. -/
def inverseType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K → ∀ F : ComplexEuclidean d → ℂ,
  Differentiable ℂ F → PolynomialExponentialType K F →
    ∃! u : Distribution d, SupportedIn K u ∧ DistributionPaleyWiener.fourierLaplace u = F

def characterizationType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K → ∀ F : ComplexEuclidean d → ℂ,
  (∃ u : Distribution d, SupportedIn K u ∧ DistributionPaleyWiener.fourierLaplace u = F) ↔
    Differentiable ℂ F ∧ PolynomialExponentialType K F

/-- Uniqueness is also asserted for two arbitrary compact supports. -/
def injectivityType : Prop := ∀ (d : ℕ) (u v : Distribution d),
  IsCompact (euclideanSupport u) → IsCompact (euclideanSupport v) →
  DistributionPaleyWiener.fourierLaplace u = DistributionPaleyWiener.fourierLaplace v → u = v

/-- This precise equality explains why the exponential type does not record
holes in a nonconvex compact set. -/
def convexHullType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → ∀ η,
    supportFunction (convexHull ℝ K) η = supportFunction K η

/-- The chosen extension is the actual continuous extension, with no
certificate about order or growth supplied by the caller. -/
def extensionType : Prop := ∀ (d : ℕ) (u : Distribution d),
  IsCompact (euclideanSupport u) →
    ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      smoothExtension u (testToSmoothLM ℂ ⊤ φ) = u φ

/-- Any cutoff which equals one near the actual support evaluates the transform. -/
def cutoffType : Prop := ∀ (d : ℕ) (u : Distribution d),
  IsCompact (euclideanSupport u) →
  ∀ (χ : Tests ℂ (⊤ : Opens (Domain d))) (V : Set (Domain d)),
    IsOpen V → distributionSupport u ⊆ V → EqOn χ 1 V →
    ∀ z : ComplexEuclidean d, ∃ ψ : Tests ℂ (⊤ : Opens (Domain d)),
      (∀ x, ψ x = χ x * (laplaceKernel z).val x) ∧
        DistributionPaleyWiener.fourierLaplace u z = u ψ

/-- The real restriction gives an actual tempered distribution by integration,
including integrability of each pairing, rather than an assumed certificate. -/
def realAxisTemperedType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → ∀ F : ComplexEuclidean d → ℂ,
  Differentiable ℂ F → PolynomialExponentialType K F →
  ∃ U : Tempered ℂ d, ∀ φ : Schwartz ℂ d,
    Integrable (fun ξ => F (realFrequency ξ) * φ ξ) ∧
      U φ = ∫ ξ, F (realFrequency ξ) * φ ξ

/-- Polynomial growth is removed by multiplication with a smooth compact
support transform, with the exact Minkowski sum of support types. -/
def regularizedInverseType : Prop := ∀ (d : ℕ) (K L : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K →
  L.Nonempty → IsCompact L → Convex ℝ L →
  ∀ (F : ComplexEuclidean d → ℂ) (ρ : Euclidean d → ℂ),
  Differentiable ℂ F → PolynomialExponentialType K F → SmoothSupportedIn L ρ →
  let G := fun z => F z * PaleyWiener.fourierLaplace ρ z
  SmoothSupportedIn (K + L) (inverseRealIntegral G) ∧
    PaleyWiener.fourierLaplace (inverseRealIntegral G) = G

/-- The inverse real Fourier transform exists as a tempered distribution and
restricts to the original LF dual. The support assertion is a further obligation. -/
def inverseTemperedType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → ∀ F : ComplexEuclidean d → ℂ,
  Differentiable ℂ F → PolynomialExponentialType K F →
  ∃ (u : Distribution d) (U : Tempered ℂ d),
    (∀ φ : Tests ℂ (⊤ : Opens (Domain d)), u φ = U (Examples.testSchwartz ℂ φ)) ∧
    ∀ ψ : Schwartz ℂ d,
      Integrable (fun ξ => F (realFrequency ξ) * ψ ξ) ∧
        temperedFourier U ψ = ∫ ξ, F (realFrequency ξ) * ψ ξ

/-- Support of the actual inverse tempered distribution. Transform recovery
and uniqueness are additional parts of the full converse above. -/
def inverseSupportedTemperedType : Prop := ∀ (d : ℕ) (K : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K → ∀ F : ComplexEuclidean d → ℂ,
  Differentiable ℂ F → PolynomialExponentialType K F →
  ∃ (u : Distribution d) (U : Tempered ℂ d), SupportedIn K u ∧
    (∀ φ : Tests ℂ (⊤ : Opens (Domain d)), u φ = U (Examples.testSchwartz ℂ φ)) ∧
    ∀ ψ : Schwartz ℂ d,
      Integrable (fun ξ => F (realFrequency ξ) * ψ ξ) ∧
        temperedFourier U ψ = ∫ ξ, F (realFrequency ξ) * ψ ξ

/-- The regularized inverse is an actual LF distribution with the canonical
Fourier--Laplace transform, and the expected integral pairing. -/
def regularizedDistributionInverseType : Prop := ∀ (d : ℕ) (K L : Set (Euclidean d)),
  K.Nonempty → IsCompact K → Convex ℝ K →
  L.Nonempty → IsCompact L → Convex ℝ L →
  ∀ (F : ComplexEuclidean d → ℂ) (ρ : Euclidean d → ℂ),
  Differentiable ℂ F → PolynomialExponentialType K F → SmoothSupportedIn L ρ →
  let G := fun z => F z * PaleyWiener.fourierLaplace ρ z
  ∃ u : Distribution d, SupportedIn (K + L) u ∧
    DistributionPaleyWiener.fourierLaplace u = G ∧
    ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      u φ = ∫ x, inverseRealIntegral G x * Examples.testSchwartz ℂ φ x

/-- The inclusion uses the genuine LF and Schwartz topologies. -/
def testInclusionType : Prop := ∀ d : ℕ,
  Continuous (Examples.testSchwartz ℂ (d := d))

end Specs.ExpandedFA.Fourier.DistributionPaleyWiener
