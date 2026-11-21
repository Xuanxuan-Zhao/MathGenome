import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach

/-!
Independent statements for Proposition `fa2:p1:c02:complete-subspace`,
paper.tex lines 345–350. A submodule carries the norm, metric, and topology
inherited from the ambient normed space. Completeness is the norm Cauchy-sequence
condition of Chapter 1. Both real and complex scalars, the zero subspace,
the whole space, and the zero ambient space are included.
-/

namespace ExpandedFA.P1.C02CompleteSubspace.Spec

open ExpandedFA.P1.C01Banach.Spec

/-- Completeness of a subspace implies closedness without ambient completeness. -/
def CompleteSubspaceClosed : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), IsBanachSpaceValue M → IsClosed (M : Set E)

/-- In a Banach ambient space, inherited completeness is equivalent to closedness. -/
def CompleteSubspaceIffClosed : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    IsBanachSpaceValue E → ∀ (M : Submodule 𝕜 E),
      IsBanachSpaceValue M ↔ IsClosed (M : Set E)

end ExpandedFA.P1.C02CompleteSubspace.Spec
