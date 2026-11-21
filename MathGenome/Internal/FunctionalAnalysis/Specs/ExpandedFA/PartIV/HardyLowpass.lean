import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyWeightedKernel
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
Independent statements for `paper.tex`, fa2:p4:hardy-lowpass-inverse,
in the chapter with the explicit convention `d ≥ 1`.
The Fourier transform of a real scalar function is taken after its canonical
embedding in ℂ. Neither the hypotheses nor the conclusion assert smoothness
of the Fourier transform of the original kernel.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal FourierTransform

namespace ExpandedFA.PartIV.HardyLowpassSpec
open ExpandedFA.Fourier HardyMaximalSpec

/-- The usual complex Fourier transform, also for real-valued functions. -/
def scalarFourier {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Euclidean d → 𝕜) : Euclidean d → ℂ :=
  integralFourier (fun x => RCLike.map 𝕜 ℂ (f x))

/-- The full cutoff assertion, including smoothness and compact support. -/
def IsLowpass {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Schwartz 𝕜 d) (R : ℝ) : Prop :=
  0 < R ∧ ContDiff ℝ (⊤ : ℕ∞) (scalarFourier (η : Euclidean d → 𝕜)) ∧
    HasCompactSupport (scalarFourier (η : Euclidean d → 𝕜)) ∧
    tsupport (scalarFourier (η : Euclidean d → 𝕜)) ⊆ Metric.ball 0 (2 / R) ∧
    ∀ ξ ∈ Metric.ball (0 : Euclidean d) (1 / R), scalarFourier η ξ = 1

/-- The assigned result, with the pointwise convolution identity and decay
of an actual integrable representative, for either scalar field. -/
def LowpassInverse : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
  ∀ (Φ : Euclidean d → 𝕜), IsFixedKernel Φ →
  ∃ (R : ℝ) (η : Schwartz 𝕜 d) (Ψ : Euclidean d → 𝕜) (C : ℝ),
    IsLowpass η R ∧ Integrable Ψ ∧ 0 ≤ C ∧
    (∀ x, ‖Ψ x‖ ≤ C * (1 + ‖x‖) ^ (-(d : ℝ) - 1 / 2)) ∧
    (∀ x, η x = convolve Ψ Φ x)

def FixedKernelIntegrable : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (Φ : Euclidean d → 𝕜),
    IsFixedKernel Φ → Integrable Φ ∧ weightedNorm Φ < ∞

def SchwartzWeighted : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (η : Schwartz 𝕜 d), weightedNorm η < ∞

/-- Two nested Fourier cutoffs at any prescribed positive scale.
The second reproduces the first under convolution. -/
def NestedCutoffs : Prop :=
  ∀ (d : ℕ) (R : ℝ), 0 < R →
  ∃ η ζ : Schwartz ℂ d,
    (tsupport (schwartzFourier η) ⊆ Metric.ball 0 (2 / R)) ∧
    (∀ ξ ∈ Metric.ball (0 : Euclidean d) (1 / R), schwartzFourier η ξ = 1) ∧
    (tsupport (schwartzFourier ζ) ⊆ Metric.ball 0 (4 / R)) ∧
    (∀ ξ ∈ Metric.ball (0 : Euclidean d) (2 / R), schwartzFourier ζ ξ = 1) ∧
    (∀ x, convolve ζ η x = η x)

/-- The analytic input left after constructing the nested cutoffs: slow
dilation makes the convolution defect small in L¹. -/
def SmallDefect : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
  ∀ (Φ : Euclidean d → 𝕜), IsFixedKernel Φ →
  ∃ (R : ℝ) (η ζ : Schwartz 𝕜 d), IsLowpass η R ∧
    convolve ζ η = η ∧
    let h : Euclidean d → 𝕜 := fun x =>
      ζ x - (∫ y, Φ y)⁻¹ * convolve Φ ζ x
    Integrable h ∧ weightedNorm h < ∞ ∧
      (∫ x, ‖h x‖) < (2 * (2 : ℝ) ^ ((d : ℝ) + 1 / 2))⁻¹

/-- A weighted convolution-series factorization. All the assumptions on the
defect are ordinary analytic conditions, not an assumed inverse. -/
def ResolveDefect : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
  ∀ (Φ η ζ : Euclidean d → 𝕜) (c : 𝕜),
    Integrable Φ → Integrable η → Integrable ζ →
    weightedNorm Φ < ∞ → weightedNorm η < ∞ → weightedNorm ζ < ∞ →
    convolve ζ η = η →
    let h : Euclidean d → 𝕜 := fun x => ζ x - c⁻¹ * convolve Φ ζ x
    Integrable h → weightedNorm h < ∞ →
    (∫ x, ‖h x‖) < (2 * (2 : ℝ) ^ ((d : ℝ) + 1 / 2))⁻¹ →
    ∃ (Ψ : Euclidean d → 𝕜) (C : ℝ), Integrable Ψ ∧ 0 ≤ C ∧
      (∀ x, ‖Ψ x‖ ≤ C * (1 + ‖x‖) ^ (-(d : ℝ) - 1 / 2)) ∧
      (∀ x, η x = convolve Ψ Φ x)

/-- Assembly of the assigned theorem from the small-defect estimate. -/
def LowpassFromSmallDefect : Prop := SmallDefect → LowpassInverse

/-- A compatible family of cutoffs, with literal physical-space dilations.
The real-valued version is included in the scalar quantifier. -/
def ScaledCutoffs : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (d : ℕ),
  ∃ η₀ ζ₀ : Schwartz 𝕜 d, ∀ R : ℝ, 0 < R →
    ∃ η ζ : Schwartz 𝕜 d,
      (η : Euclidean d → 𝕜) = dilate R η₀ ∧
      (ζ : Euclidean d → 𝕜) = dilate R ζ₀ ∧
      IsLowpass η R ∧ convolve ζ η = η

/-- Slow dilations of a Schwartz function have an arbitrarily small L¹
defect against a mass-normalized fixed kernel. This assertion has no
Fourier cutoff or inverse in its conclusion. -/
def DilationDefect : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
  ∀ Φ : Euclidean d → 𝕜, Integrable Φ → weightedNorm Φ < ∞ → (∫ x, Φ x) ≠ 0 →
  ∀ (ζ₀ : Schwartz 𝕜 d) (ε : ℝ), 0 < ε →
  ∃ R : ℝ, 0 < R ∧
    let h : Euclidean d → 𝕜 := fun x =>
      dilate R ζ₀ x - (∫ y, Φ y)⁻¹ * convolve Φ (dilate R ζ₀) x
    Integrable h ∧ weightedNorm h < ∞ ∧ (∫ x, ‖h x‖) < ε

def SmallDefectAssembly : Prop := ScaledCutoffs → DilationDefect → SmallDefect

end ExpandedFA.PartIV.HardyLowpassSpec
