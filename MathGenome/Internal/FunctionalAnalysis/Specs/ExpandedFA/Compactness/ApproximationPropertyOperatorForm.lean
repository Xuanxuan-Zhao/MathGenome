import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.ApproximationPropertyDefinitions
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Independent statements for the equivalence in fa2:p2:approximation-property,
paper.tex:9531–9559. Finite rank is over the original scalar field. -/
namespace ExpandedFA.Compactness.ApproximationPropertyOperatorFormSpec
universe u v w

/-- AP gives finite-rank approximation in operator norm, for every domain universe. -/
def Forward : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y],
    ApproximationPropertyDefinitionsSpec.HasApproximationPropertyValue 𝕜 X →
    ∀ T : Y →L[𝕜] X, IsCompactOperator T →
      ∀ ε : ℝ, 0 < ε → ∃ S : Y →L[𝕜] X,
        FiniteDimensional 𝕜 (LinearMap.range S.toLinearMap) ∧ ‖S - T‖ < ε

/-- In the converse it suffices to test all Banach domains in the universe of X;
this includes the compact disk space furnished by the upstream theorem. -/
def Converse : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    (∀ (Y : Type v) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y],
      ∀ T : Y →L[𝕜] X, IsCompactOperator T →
        ∀ ε : ℝ, 0 < ε → ∃ S : Y →L[𝕜] X,
          FiniteDimensional 𝕜 (LinearMap.range S.toLinearMap) ∧ ‖S - T‖ < ε) →
    ApproximationPropertyDefinitionsSpec.HasApproximationPropertyValue 𝕜 X

/-- The equivalence, with arbitrary Banach domains. Forward above also exposes
its specialization to a domain in any other universe. -/
def Equivalence : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    ApproximationPropertyDefinitionsSpec.HasApproximationPropertyValue 𝕜 X ↔
    ∀ (Y : Type v) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y],
      ∀ T : Y →L[𝕜] X, IsCompactOperator T →
        ∀ ε : ℝ, 0 < ε → ∃ S : Y →L[𝕜] X,
          FiniteDimensional 𝕜 (LinearMap.range S.toLinearMap) ∧ ‖S - T‖ < ε

end ExpandedFA.Compactness.ApproximationPropertyOperatorFormSpec
