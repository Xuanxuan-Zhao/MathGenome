import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.StoneTheorem
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.Support

/-! Proposed replacement interface, NOT a recovered parent source.
Names below are explicit new handoff decisions; no mathematical theorem is assumed.
The seven core definitions are owned by TranslationFourierModel.
The separately owned parent and coordinate model records must import this file. -/
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ContDiff

namespace ExpandedFA.Models.FullTranslationModel
open ExpandedFA.Unbounded ExpandedFA.Semigroups.Stone
open ExpandedFA.Unbounded.MeasurableSpectralCalculus
universe u v

section Core
variable (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

abbrev L2 := Lp M 2 (volume : Measure ℝ)

variable {M}

def translate (t : ℝ) : L2 M →ₗᵢ[ℂ] L2 M :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun s : ℝ => s + t)
    (measurePreserving_add_right (volume : Measure ℝ) t)

def IsTranslationGroup (U : UnitaryGroup (L2 M)) : Prop :=
  ∀ t f, U.operators t f = translate t f

def IsCoordinateGroup (U : UnitaryGroup (L2 M)) : Prop :=
  ∀ t f, (U.operators t f : ℝ → M) =ᵐ[volume]
    fun r => Complex.exp (Complex.I * (t : ℂ) * (r : ℂ)) • f r

def HasWeakDerivative (f w : L2 M) : Prop :=
  ∀ φ : ℝ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ s : ℝ, deriv φ s • f s) = -(∫ s : ℝ, φ s • w s)

def SpatialGraph (f g : L2 M) : Prop := HasWeakDerivative f (Complex.I • g)

def CoordinateGraph (f g : L2 M) : Prop :=
  (g : ℝ → M) =ᵐ[volume] fun r => (r : ℂ) • f r

end Core


section FourierAgreement
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

/-- The negative angular-frequency transform, with its exact normalization,
on every vector-valued Schwartz function. Equality is an a.e. L2 equality. -/
def AngularFourierAgreement (F : L2 M ≃ₗᵢ[ℂ] L2 M) : Prop :=
  ∀ φ : SchwartzMap ℝ M,
    (F (φ.toLp 2 volume) : ℝ → M) =ᵐ[volume] fun r =>
      (Real.sqrt (2 * Real.pi))⁻¹ •
        ∫ s : ℝ, Complex.exp (-Complex.I * (s : ℂ) * (r : ℂ)) • φ s

/-- Exact conjugacy as equality of L2 vectors; IsCoordinateGroup supplies
its a.e. scalar multiplier formula. -/
def FourierConjugacy (V W : UnitaryGroup (L2 M))
    (F : L2 M ≃ₗᵢ[ℂ] L2 M) : Prop :=
  ∀ t f, F (V.operators t f) = W.operators t (F f)

end FourierAgreement

end ExpandedFA.Models.FullTranslationModel

namespace ExpandedFA.Models.TranslationFourierModel.Spec
open ExpandedFA.Models.FullTranslationModel ExpandedFA.Semigroups.Stone
universe u

/-- A strongly continuous unitary group with the original translation formula,
for every complex Hilbert multiplicity, including zero and nonseparable spaces. -/
def TranslationGroupExpected : Prop :=
  ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M],
    ∃ V : UnitaryGroup (L2 M), IsTranslationGroup V

/-- An onto complex linear isometry on the actual real-base Bochner L2 space
that agrees with the original angular integral on all Schwartz inputs. -/
def AngularFourierExpected : Prop :=
  ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M],
    ∃ F : L2 M ≃ₗᵢ[ℂ] L2 M, AngularFourierAgreement F

/-- The translation and coordinate groups and Fourier transform are produced
together. No generator-domain or spectral-multiplicity certificate is a premise. -/
def TranslationConjugacyExpected : Prop :=
  ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M],
    ∃ (V W : UnitaryGroup (L2 M)) (F : L2 M ≃ₗᵢ[ℂ] L2 M),
      IsTranslationGroup V ∧ IsCoordinateGroup W ∧
      AngularFourierAgreement F ∧ FourierConjugacy V W F

end ExpandedFA.Models.TranslationFourierModel.Spec
