import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpaceBidualIsometry

/-!
The complete theorem `fa2:p1:james-space`, paper.tex:4512–4599.

The upstream model fixes the actual subtype of real null sequences of finite
cyclic variation, its pointwise operations, and its exact displayed norm.
`BanachBasisConclusion` includes completeness, the normalized coordinate unit
vectors, unique ordered expansions and contractive initial projections.
`ShrinkingConclusion` identifies the continuous coordinates with the sequence
entries and asserts norm convergence of every dual expansion.

The quotient in `CodimensionOne` is by canonical evaluation into the continuous
real-linear bidual. `ExplicitIsometry` prescribes the noncanonical isometry and
its inverse by the manuscript's limit-and-shift formulas. The final component
states explicitly that canonical evaluation is not surjective. Nonemptiness
prevents the statements about all models from being vacuous.
-/
noncomputable section

namespace ExpandedFA.P1.JamesSpace.Spec

def JamesSpaceConclusion : Prop :=
  JamesBanachBasisSpec.BanachBasisConclusion ∧
  JamesShrinkingSpec.ShrinkingConclusion ∧
  JamesBidualSpec.CodimensionOne ∧
  JamesBidualIsometrySpec.ExplicitIsometry ∧
  JamesBidualIsometrySpec.NonreflexiveIsometric

/-- The James space itself witnesses that even a surjective real-linear
isometry onto the bidual does not imply reflexivity. The normed structures
and completeness are fixed by the Banach basis model, not extra hypotheses. -/
def IsometryDoesNotImplyReflexivity : Prop :=
  ∃ m : JamesBanachBasisSpec.BanachBasisModel,
    Nonempty (JamesBidualSpec.ModelSpace m ≃ₗᵢ[ℝ] JamesBidualSpec.Bidual m) ∧
    ¬ C04CanonicalMap.Spec.IsReflexiveValue ℝ (JamesBidualSpec.ModelSpace m)

end ExpandedFA.P1.JamesSpace.Spec
