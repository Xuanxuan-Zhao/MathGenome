import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.HolderSpaces

/-! The Hölder completeness clauses of paper.tex:5804–5832.
These statements use the canonical spaces and their specified sum norms.
No completeness certificate or regular extension at the endpoints is assumed. -/
namespace ExpandedFA.Supplements.HolderCompletenessSpec

/-- Completeness of the interval Hölder space, including order zero. -/
def CmHolderComplete : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) (a b : ℝ) (hab : a < b)
    (α : HolderSpacesSpec.HolderExponent),
    CompleteSpace (HolderSpacesSpec.CmHolder 𝕜 m hab α)

/-- Bounded Hölder functions on every metric space, including the empty space. -/
def BoundedHolderComplete : Prop :=
  ∀ (X 𝕜 : Type*) [MetricSpace X] [RCLike 𝕜]
    (α : HolderSpacesSpec.HolderExponent),
    CompleteSpace (HolderSpacesSpec.BoundedHolder X 𝕜 α)

end ExpandedFA.Supplements.HolderCompletenessSpec
