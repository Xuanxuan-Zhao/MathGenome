import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.NormalPVM

/-! The three normal-operator assertions in paper.tex 12572–12599.
The singleton in the spectral space is the inverse image of {ζ}; thus ζ
need not belong to the spectrum. No nontriviality or separability is assumed. -/
noncomputable section
namespace ExpandedFA.SpectralMeasure.NormalSpectralTests.Spec
universe u

def SelfAdjointSpectrum : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N →
    (IsSelfAdjoint N ↔ ∀ z ∈ spectrum ℂ N, z.im = 0)

def UnitarySpectrum : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N →
    (N ∈ unitary (H →L[ℂ] H) ↔ ∀ z ∈ spectrum ℂ N, ‖z‖ = 1)

def Eigenprojection : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N →
    ∀ E : ProjectionValuedMeasure (spectrum ℂ N) H, NormalPVM.Spec.Resolves N E →
    ∀ ζ : ℂ, LinearMap.range (E {z | (z : ℂ) = ζ}).toLinearMap =
      LinearMap.ker (N - ζ • (1 : H →L[ℂ] H)).toLinearMap

/-- Explicitly records the source conventions at the zero space. -/
def ZeroSpace : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Subsingleton H] (N : H →L[ℂ] H),
    (1 : H →L[ℂ] H) = 0 ∧ spectrum ℂ N = ∅ ∧ IsSelfAdjoint N ∧
      N ∈ unitary (H →L[ℂ] H) ∧
      ∀ E : ProjectionValuedMeasure (spectrum ℂ N) H, ∀ ζ : ℂ,
        E {z | (z : ℂ) = ζ} = 0
end ExpandedFA.SpectralMeasure.NormalSpectralTests.Spec
