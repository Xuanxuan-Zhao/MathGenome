import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01FiniteDimension
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.StrictApproximation

/-! Statements for `fa2:p1:finite-dimensional-approximation`, paper.tex:6376–6389.
The set is closed in the finite-dimensional subspace's own norm topology.
The ambient real or complex normed space need not be complete. Nearest points
minimize the original ambient norm distance; convexity is over the reals.
-/
namespace ExpandedFA.Supplements.FiniteDimensionalApproximation.Spec
universe u v
noncomputable section

def ClosedSubsetExistence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M]
    (C : Set M), C.Nonempty → IsClosed C → ∀ x : E,
    ∃ z : M, P1.StrictApproximation.Spec.IsNearestPoint E (Subtype.val '' C) x (z : E)

def SubspaceExistence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M] (x : E),
    ∃ z : E, P1.StrictApproximation.Spec.IsNearestPoint E (M : Set E) x z

/-- The uniqueness assertion applies to all convex subsets whenever a nearest
point exists, without finite dimension, closedness, or completeness. -/
def ConvexSubsetUniqueness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    P1.RotundDefinitions.Spec.RotundValue 𝕜 E →
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ C : Set E, Convex ℝ C → ∀ x z w : E,
      P1.StrictApproximation.Spec.IsNearestPoint E C x z →
      P1.StrictApproximation.Spec.IsNearestPoint E C x w → z = w

end
end ExpandedFA.Supplements.FiniteDimensionalApproximation.Spec
