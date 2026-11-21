import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.TvsDefinitions

namespace ExpandedFA.P1

/-- The notes' default topological vector space, with separation explicit. -/
abbrev HausdorffTVS (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] : Prop :=
  TVS 𝕜 E ∧ T2Space E

/-- The notes' default locally convex space, with separation explicit. -/
abbrev HausdorffLCS (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] : Prop :=
  LCS 𝕜 E ∧ T2Space E

end ExpandedFA.P1
