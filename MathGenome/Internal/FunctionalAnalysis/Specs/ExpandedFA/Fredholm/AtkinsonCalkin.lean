import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.AtkinsonParametrices
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Independent obligations for `fa2:p2:atkinson`. Units are used in the
actual quotient ring, so invertibility also has its usual meaning when 0 = 1.
The one-sided equivalences are restricted to complete Hilbert spaces. -/
namespace ExpandedFA.Fredholm.AtkinsonCalkinSpec
universe u v w

/-- The two Banach-space assertions are retained from the accepted upstream interface. -/
def TwoSidedCompactCharacterization : Prop :=
  AtkinsonParametricesSpec.CompactParametrixCharacterization.{u, v, w}

def TwoSidedFiniteRankCharacterization : Prop :=
  AtkinsonParametricesSpec.FiniteRankParametrixCharacterization.{u, v, w}

def CalkinCharacterization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (T : X →L[𝕜] X),
    DefinitionsSpec.IsFredholmValue T ↔
      IsUnit (DefinitionsSpec.calkinProjectionValue 𝕜 X T)

def LeftCompactCharacterization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    DefinitionsSpec.IsLeftSemiFredholmValue T ↔
      ∃ S : K →L[𝕜] H, Compactness.DefinitionsSpec.IsCompactLinearMapValue
        (S.comp T - ContinuousLinearMap.id 𝕜 H).toLinearMap

def RightCompactCharacterization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    DefinitionsSpec.IsRightSemiFredholmValue T ↔
      ∃ S : K →L[𝕜] H, Compactness.DefinitionsSpec.IsCompactLinearMapValue
        (T.comp S - ContinuousLinearMap.id 𝕜 K).toLinearMap

def LeftFiniteRankCharacterization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    DefinitionsSpec.IsLeftSemiFredholmValue T ↔
      ∃ S : K →L[𝕜] H, FiniteDimensional 𝕜
        (S.comp T - ContinuousLinearMap.id 𝕜 H).range

def RightFiniteRankCharacterization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    DefinitionsSpec.IsRightSemiFredholmValue T ↔
      ∃ S : K →L[𝕜] H, FiniteDimensional 𝕜
        (T.comp S - ContinuousLinearMap.id 𝕜 K).range

/-- The right criterion is exactly the left criterion for the Hilbert adjoint. -/
def RightAdjointCharacterization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    DefinitionsSpec.IsRightSemiFredholmValue T ↔
      DefinitionsSpec.IsLeftSemiFredholmValue (ContinuousLinearMap.adjoint T)

end ExpandedFA.Fredholm.AtkinsonCalkinSpec
