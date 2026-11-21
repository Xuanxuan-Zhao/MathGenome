import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions

/-! The two Banach-space parametrix characterizations in
`paper.tex`, Theorem `fa2:p2:atkinson`. Defects use the actual
continuous maps and finite rank means finite-dimensional range. -/
namespace ExpandedFA.Fredholm.AtkinsonParametricesSpec
universe u v w

def CompactParametrixCharacterization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y] (T : X →L[𝕜] Y),
    DefinitionsSpec.IsFredholmValue T ↔
      ∃ S : Y →L[𝕜] X,
        Compactness.DefinitionsSpec.IsCompactLinearMapValue
          (S.comp T - ContinuousLinearMap.id 𝕜 X).toLinearMap ∧
        Compactness.DefinitionsSpec.IsCompactLinearMapValue
          (T.comp S - ContinuousLinearMap.id 𝕜 Y).toLinearMap

def FiniteRankParametrixCharacterization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y] (T : X →L[𝕜] Y),
    DefinitionsSpec.IsFredholmValue T ↔
      ∃ S : Y →L[𝕜] X,
        FiniteDimensional 𝕜 (S.comp T - ContinuousLinearMap.id 𝕜 X).range ∧
        FiniteDimensional 𝕜 (T.comp S - ContinuousLinearMap.id 𝕜 Y).range

end ExpandedFA.Fredholm.AtkinsonParametricesSpec
