import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.EssentialSpectraDefinitions
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Independent full statements of `fa2:p2:essential-spectrum`.
The scalar field is complex and H is complete. The nonemptiness claim
requires infinite dimensionality; the other statements hold more generally. The
notion of isolation is expressed by an open ball meeting the spectrum only
at its centre; multiplicity is the dimension of the actual eigenspace.
-/
namespace ExpandedFA.Fredholm.EssentialWeylSpec
universe u
open EssentialSpectraSpec DefinitionsSpec

def WeylFormula : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (T : H →L[ℂ] H), WeylSpectrumValue T = EssentialSpectrumValue T ∪
    {z | ∃ h : IsFredholmValue (T - z • 1), fredholmIndexValue (T - z • 1) h ≠ 0}

def EssentialCompactPerturbation : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (T K : H →L[ℂ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    EssentialSpectrumValue (T + K) = EssentialSpectrumValue T

def WeylCompactPerturbation : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (T K : H →L[ℂ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    WeylSpectrumValue (T + K) = WeylSpectrumValue T

def CalkinSpectrum : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (T : H →L[ℂ] H), EssentialSpectrumValue T =
    spectrum ℂ (calkinProjectionValue ℂ H T)

def EssentialNonemptyCompact : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (T : H →L[ℂ] H), (¬ FiniteDimensional ℂ H) → (EssentialSpectrumValue T).Nonempty ∧
    IsCompact (EssentialSpectrumValue T)

/-- The exact description includes spectral membership in both alternatives.
Nonisolation uses every positive radius. An isolated point in the second
alternative has an infinite-dimensional eigenspace, hence is an eigenvalue. -/
def NormalEssentialDescription : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (N : H →L[ℂ] H), IsStarNormal N →
    EssentialSpectrumValue N =
      {z | z ∈ spectrum ℂ N ∧
        ((∀ ε : ℝ, 0 < ε → ∃ w ∈ spectrum ℂ N, w ≠ z ∧ dist w z < ε) ∨
          ((∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum ℂ N, dist w z < ε → w = z) ∧
            ¬ FiniteDimensional ℂ (N - z • 1).ker))}

def NormalWeylEssential : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (N : H →L[ℂ] H), IsStarNormal N → WeylSpectrumValue N = EssentialSpectrumValue N
end ExpandedFA.Fredholm.EssentialWeylSpec
