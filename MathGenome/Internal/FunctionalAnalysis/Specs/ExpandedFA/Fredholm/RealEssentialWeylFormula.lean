import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RealEssentialSpectraDefinitions
import Mathlib.Topology.Defs.Basic

/-! Independent statements for the intrinsic real clauses of
`fa2:p2:essential-spectrum`. These strengthen the infinite-dimensional statement
by also allowing zero and finite-dimensional complete real Hilbert spaces.
No nonemptiness assertion is made. -/
namespace ExpandedFA.Fredholm.RealEssentialWeylFormulaSpec
universe u
open DefinitionsSpec RealEssentialSpectraDefinitionsSpec

def WeylFormula : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H),
    realWeylSpectrumValue T = realEssentialSpectrumValue T ∪
      {z | ∃ h : IsFredholmValue (T - z • (1 : H →L[ℝ] H)),
        fredholmIndexValue (T - z • (1 : H →L[ℝ] H)) h ≠ 0}

def EssentialCompactPerturbation : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T K : H →L[ℝ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
      realEssentialSpectrumValue (T + K) = realEssentialSpectrumValue T

def WeylCompactPerturbation : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T K : H →L[ℝ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
      realWeylSpectrumValue (T + K) = realWeylSpectrumValue T

def EssentialCalkinSpectrum : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H),
    realEssentialSpectrumValue T =
      spectrum ℝ (calkinProjectionValue ℝ H T : CalkinValue ℝ H)

def EssentialCompact : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H),
    IsCompact (realEssentialSpectrumValue T)

/-- The correction acts on the original real space and has finite real rank. -/
def IndexZeroCorrection : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H) (h : IsFredholmValue T),
    fredholmIndexValue T h = 0 →
      ∃ F : H →L[ℝ] H, FiniteDimensional ℝ F.range ∧ IsUnit (T + F)

end ExpandedFA.Fredholm.RealEssentialWeylFormulaSpec
