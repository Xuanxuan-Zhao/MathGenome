import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RealEssentialWeylFormula
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RealFredholmComplexification
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.EssentialWeylSpectra

/-! The corrected real normal clauses and full real/complex assembly of
`fa2:p2:essential-spectrum`, paper.tex:10690–10739. No separability,
compactness of the operator, or nonzero-space hypothesis is imposed. -/
noncomputable section
namespace ExpandedFA.Fredholm.RealNormalEssentialSpectrum
universe u
namespace Spec
open RealEssentialSpectraDefinitionsSpec EssentialSpectraSpec
open TraceIdeals.RealComplexification (Space)
local instance {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] : CompleteSpace (Space H) :=
  TraceIdeals.RealComplexification.Spec.completeSpace

/-- This comparison holds for every bounded real operator. -/
def EssentialComplexification : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H),
    realEssentialSpectrumValue T =
      {r : ℝ | (r : ℂ) ∈ EssentialSpectrumValue
        (TraceIdeals.RealComplexification.Spec.operator T)}

def NormalWeylEssential : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (N : H →L[ℝ] H), IsStarNormal N →
    realWeylSpectrumValue N = realEssentialSpectrumValue N

/-- Disks and isolation are in the full complexified spectrum; multiplicity
is that of the original real eigenspace. Every real scalar is tested. -/
def NormalEssentialDescription : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (N : H →L[ℝ] H), IsStarNormal N →
    realEssentialSpectrumValue N =
      {r : ℝ | (r : ℂ) ∈ spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N) ∧
        ((∀ ε : ℝ, 0 < ε → ∃ w ∈ spectrum ℂ
            (TraceIdeals.RealComplexification.Spec.operator N),
            w ≠ (r : ℂ) ∧ dist w (r : ℂ) < ε) ∨
          ((∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum ℂ
              (TraceIdeals.RealComplexification.Spec.operator N),
              dist w (r : ℂ) < ε → w = (r : ℂ)) ∧
            ¬ FiniteDimensional ℝ (N - r • 1).ker))}

def SelfAdjointSpectrum : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (N : H →L[ℝ] H), IsSelfAdjoint N →
    (∀ w ∈ spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N),
      w = (w.re : ℂ)) ∧
    spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N) =
      Complex.ofReal '' spectrum ℝ N

def SelfAdjointEssentialDescription : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (N : H →L[ℝ] H), IsSelfAdjoint N →
    realEssentialSpectrumValue N =
      {r : ℝ | r ∈ spectrum ℝ N ∧
        ((∀ ε : ℝ, 0 < ε → ∃ s ∈ spectrum ℝ N, s ≠ r ∧ dist s r < ε) ∨
          ((∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ spectrum ℝ N, dist s r < ε → s = r) ∧
            ¬ FiniteDimensional ℝ (N - r • 1).ker))}

/-- Complete original-scalar statement, including the unchanged complex
nonemptiness clause and the possibly empty compact real essential set. -/
def EssentialWeylTheorem : Prop :=
  RealEssentialSpectraDefinitionsSpec.RealEssentialMembership.{u} ∧
  RealEssentialSpectraDefinitionsSpec.RealWeylMembership.{u} ∧
  RealEssentialWeylFormulaSpec.WeylFormula.{u} ∧
  RealEssentialWeylFormulaSpec.EssentialCompactPerturbation.{u} ∧
  RealEssentialWeylFormulaSpec.WeylCompactPerturbation.{u} ∧
  RealEssentialWeylFormulaSpec.EssentialCalkinSpectrum.{u} ∧
  RealEssentialWeylFormulaSpec.EssentialCompact.{u} ∧
  EssentialComplexification.{u} ∧ NormalWeylEssential.{u} ∧
  NormalEssentialDescription.{u} ∧ SelfAdjointSpectrum.{u} ∧
  SelfAdjointEssentialDescription.{u} ∧
  EssentialWeylSpec.WeylFormula.{u} ∧
  EssentialWeylSpec.EssentialCompactPerturbation.{u} ∧
  EssentialWeylSpec.WeylCompactPerturbation.{u} ∧
  EssentialWeylSpec.CalkinSpectrum.{u} ∧
  EssentialWeylSpec.EssentialNonemptyCompact.{u} ∧
  EssentialWeylSpec.NormalWeylEssential.{u} ∧
  EssentialWeylSpec.NormalEssentialDescription.{u}
end Spec
end ExpandedFA.Fredholm.RealNormalEssentialSpectrum
