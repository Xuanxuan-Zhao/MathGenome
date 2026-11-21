import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.HolderSpaces

/-! Completeness in precisely the sum norm of the canonical interval space. -/
namespace ExpandedFA.Supplements.DifferentiableCompletenessSpec

/-- No extension across the endpoints is part of this assertion. -/
def CmComplete : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) (a b : ℝ) (hab : a < b),
    CompleteSpace (HolderSpacesSpec.Cm 𝕜 m hab)

end ExpandedFA.Supplements.DifferentiableCompletenessSpec
