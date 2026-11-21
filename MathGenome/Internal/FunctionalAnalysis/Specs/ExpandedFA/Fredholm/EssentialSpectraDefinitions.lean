import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions

/-!
Independent specification for the definitions in paper.tex:10690–10701 and
10718–10728. The essential spectrum uses failure of Fredholmness; the Weyl
spectrum intersects spectra over every compact perturbation. Left and right
essential spectra use the corresponding semi-Fredholm predicates.

The formulas make sense even without completeness. In particular they apply
to all complex Hilbert spaces, including zero and finite-dimensional spaces.
Infinite dimensionality is needed for the later nonempty Calkin-spectrum
theorem, not for these definitions. Approximate point spectrum and reduced
minimum modulus are not redefined here.
-/

namespace ExpandedFA.Fredholm.EssentialSpectraSpec

universe u

def OperatorSpectrumType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H],
    (H →L[ℂ] H) → Set ℂ

def EssentialSpectrumValue : OperatorSpectrumType.{u} :=
  fun {_} _ _ T => {z | ¬ DefinitionsSpec.IsFredholmValue (T - z • 1)}

def WeylSpectrumValue : OperatorSpectrumType.{u} :=
  fun {H} _ _ T =>
    ⋂ (K : H →L[ℂ] H)
      (_ : Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap),
      Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue ℂ
        (H →L[ℂ] H) (T + K)

def LeftEssentialSpectrumValue : OperatorSpectrumType.{u} :=
  fun {_} _ _ T => {z | ¬ DefinitionsSpec.IsLeftSemiFredholmValue (T - z • 1)}

def RightEssentialSpectrumValue : OperatorSpectrumType.{u} :=
  fun {_} _ _ T => {z | ¬ DefinitionsSpec.IsRightSemiFredholmValue (T - z • 1)}

def EssentialSpectrumMembership : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (z : ℂ),
    z ∈ EssentialSpectrumValue T ↔
      ¬ DefinitionsSpec.IsFredholmValue (T - z • 1)

def WeylSpectrumMembership : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (z : ℂ),
    z ∈ WeylSpectrumValue T ↔
      ∀ K : H →L[ℂ] H,
        Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
          z ∈ Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue ℂ
            (H →L[ℂ] H) (T + K)

def LeftEssentialSpectrumMembership : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (z : ℂ),
    z ∈ LeftEssentialSpectrumValue T ↔
      ¬ DefinitionsSpec.IsLeftSemiFredholmValue (T - z • 1)

def RightEssentialSpectrumMembership : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (z : ℂ),
    z ∈ RightEssentialSpectrumValue T ↔
      ¬ DefinitionsSpec.IsRightSemiFredholmValue (T - z • 1)

def EssentialSpectrumUnion : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H),
    EssentialSpectrumValue T = LeftEssentialSpectrumValue T ∪ RightEssentialSpectrumValue T

end ExpandedFA.Fredholm.EssentialSpectraSpec
