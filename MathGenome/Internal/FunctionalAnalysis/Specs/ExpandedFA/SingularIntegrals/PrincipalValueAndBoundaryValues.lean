import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Independent statements for `paper.tex`, fa2:p4:principal-value (18342–18376).
The domain is the ordinary real line with Lebesgue measure. Pairings are complex
linear and never conjugate the test. Limits below are weak distributional limits,
expressed against every Schwartz test. The Hilbert-transform assertions of the
same source theorem are allocated to ops_hilbert_transform. -/

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology

namespace ExpandedFA.SingularIntegrals

abbrev LineSchwartz := SchwartzMap ℝ ℂ
abbrev LineTempered := LineSchwartz →L[ℂ] ℂ

/-- An absolutely convergent representation used in constructing the pairing. -/
noncomputable def compensatedPairing (φ : LineSchwartz) : ℂ :=
  ∫ x : ℝ, (if |x| ≤ 1 then φ x - φ 0 else φ x) / (x : ℂ)

noncomputable def boundaryPairing (s ε : ℝ) (φ : LineSchwartz) : ℂ :=
  ∫ x : ℝ, φ x / ((x : ℂ) + (s * ε : ℝ) * Complex.I)

noncomputable def logPairing (φ : LineSchwartz) : ℂ :=
  ∫ x : ℝ, (Real.log |x| : ℂ) * φ x

noncomputable def signPairing (φ : LineSchwartz) : ℂ :=
  ∫ ξ : ℝ, (-Complex.I * (Real.pi : ℂ) * ((if ξ = 0 then 0 else if 0 < ξ then 1 else -1) : ℂ)) * φ ξ

end ExpandedFA.SingularIntegrals

namespace Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues
open _root_.ExpandedFA.SingularIntegrals

def symmetricTruncationType := ℝ → LineSchwartz → ℂ
noncomputable def symmetricTruncationValue : symmetricTruncationType :=
  fun ε φ => ∫ x in {x : ℝ | ε < |x|}, φ x / (x : ℂ)

def principalValuePairingType := LineSchwartz → ℂ
/-- The expected symmetric-limit value, independently of the implementation.
Existence of the limit remains an obligation below. -/
noncomputable def principalValuePairingValue : principalValuePairingType :=
  fun φ => limUnder (𝓝[>] (0 : ℝ)) (fun ε => symmetricTruncationValue ε φ)

def compensatedIntegrabilityType : Prop := ∀ φ : LineSchwartz,
  Integrable (fun x : ℝ => (if |x| ≤ 1 then φ x - φ 0 else φ x) / (x : ℂ))

def symmetricLimitType : Prop := ∀ φ : LineSchwartz,
  Tendsto (fun ε => symmetricTruncationValue ε φ) (𝓝[>] (0 : ℝ))
    (𝓝 (principalValuePairingValue φ))

def compensatedFormulaType : Prop := ∀ φ : LineSchwartz,
  principalValuePairingValue φ = compensatedPairing φ

/-- Actual continuity and scalar linearity, with the pairing fixed independently. -/
def temperednessType : Prop := ∃ T : LineTempered,
  ∀ φ : LineSchwartz, T φ = principalValuePairingValue φ

/-- The logarithm is locally integrable, including at zero, and defines a
regular tempered distribution whose derivative is the specified principal value. -/
def logarithmType : Prop :=
  LocallyIntegrable (fun x : ℝ => (Real.log |x| : ℂ)) ∧
  (∀ φ : LineSchwartz, Integrable (fun x : ℝ => (Real.log |x| : ℂ) * φ x)) ∧
  ∃ L : LineTempered, (∀ φ, L φ = logPairing φ) ∧
    ∀ φ : LineSchwartz,
      -L (SchwartzMap.derivCLM ℂ ℂ φ) = principalValuePairingValue φ

/-- Both half-plane approaches, with their exact opposing delta signs. -/
def boundaryValuesType : Prop := ∀ s : ℝ, s = 1 ∨ s = -1 →
  (∀ ε : ℝ, 0 < ε →
    (∀ φ : LineSchwartz,
      Integrable (fun x : ℝ => φ x / ((x : ℂ) + (s * ε : ℝ) * Complex.I))) ∧
    ∃ T : LineTempered, ∀ φ : LineSchwartz, T φ = boundaryPairing s ε φ) ∧
  ∀ φ : LineSchwartz,
    Tendsto (fun ε => boundaryPairing s ε φ) (𝓝[>] (0 : ℝ))
      (𝓝 (principalValuePairingValue φ - (s : ℂ) * Complex.I * Real.pi * φ 0))

/-- Native real-line Fourier transform uses exp(-2πixξ), as in the accepted
Fourier interface; this integral statement fixes that normalization explicitly. -/
def fourierNormalizationType : Prop := ∀ (φ : LineSchwartz) (ξ : ℝ),
  (FourierTransform.fourierCLM ℂ LineSchwartz φ) ξ =
    ∫ x : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (x * ξ : ℝ)) * φ x

/-- Transposition on scalar-linear test pairings: no inverse or conjugation. -/
def fourierPrincipalValueType : Prop := ∀ φ : LineSchwartz,
  principalValuePairingValue (FourierTransform.fourierCLM ℂ LineSchwartz φ) = signPairing φ

end Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues
