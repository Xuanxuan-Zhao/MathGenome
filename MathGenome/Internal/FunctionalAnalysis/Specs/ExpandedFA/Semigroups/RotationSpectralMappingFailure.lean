import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.SpectralInclusion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.TorusFourierBasis
import Mathlib.NumberTheory.Real.Irrational

/-! The rotation example in paper.tex, fa2:p3:semigroup-spectral-mapping.
The circle has angular period 2π, normalized Haar measure, and translations
act by f(θ) ↦ f(θ+t). The generator below is the canonical right-derivative
generator, on its exact domain; it is not an assumed diagonal operator. -/
noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology NNReal

namespace ExpandedFA.Semigroups.RotationSpectralMappingFailureSpec

open ExpandedFA.Fourier.TorusFourierBasisSpec

abbrev AngularCircle := AddCircle (2 * π)
abbrev H := Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * π))

/-- Actual translation of a.e. equivalence classes, not merely a spectral model. -/
def rotation (t : ℝ) : H →L[ℂ] H :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun θ : AngularCircle => (t : AngularCircle) + θ)
    (measurePreserving_add_left AddCircle.haarAddCircle (t : AngularCircle))).toContinuousLinearMap

def imaginaryIntegers : Set ℂ := Set.range (fun n : ℤ => Complex.I * n)
def unitCircle : Set ℂ := {z | ‖z‖ = 1}
def exponentialImage (t : ℝ) : Set ℂ :=
  (fun z : ℂ => Complex.exp (t • z)) '' imaginaryIntegers

def RotationModel : Prop :=
  ∃ T : C0Semigroup ℂ H, ∀ t, T.operators t = rotation t

def GeneratorSpectrum : Prop :=
  ∀ T : C0Semigroup ℂ H, (∀ t, T.operators t = rotation t) →
    C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T) = imaginaryIntegers

def TimeSpectrum : Prop :=
  ∀ t : ℝ, Irrational (t / (2 * π)) →
    _root_.spectrum ℂ (rotation t) = unitCircle

def ExponentialImage : Prop :=
  ∀ t : ℝ, Irrational (t / (2 * π)) →
    (exponentialImage t).Countable ∧ closure (exponentialImage t) = unitCircle ∧
      exponentialImage t ⊂ unitCircle

/-- Complete counterexample with its actual C₀ semigroup and its generator. -/
def Counterexample : Prop :=
  ∃ T : C0Semigroup ℂ H,
    (∀ t, T.operators t = rotation t) ∧
    C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T) = imaginaryIntegers ∧
    ∀ t : ℝ≥0, Irrational ((t : ℝ) / (2 * π)) →
      let E := (fun z : ℂ => Complex.exp ((t : ℝ) • z)) ''
        C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T)
      E.Countable ∧ closure E = unitCircle ∧
        _root_.spectrum ℂ (T.operators t) = unitCircle ∧
        E ⊂ _root_.spectrum ℂ (T.operators t) \ {0}

end ExpandedFA.Semigroups.RotationSpectralMappingFailureSpec
