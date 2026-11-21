import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions

/-! Independent statement of Markov--Kakutani, paper.tex:5704--5715.
The maps are defined on the compact convex subset itself. Affineness means
preservation of real convex combinations, also over complex scalars.
The family index type may be empty. -/

open Set

namespace ExpandedFA.P1.MarkovKakutaniSpec

/-- A continuous commuting family of affine self-maps of a nonempty compact
convex subset of a Hausdorff real or complex LCS has a common fixed point. -/
def CommonFixedPoint : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [LocallyConvexSpace ℝ E],
    ∀ (K : Set E), K.Nonempty → IsCompact K → ∀ hconv : Convex ℝ K,
    ∀ (ι : Type*) (f : ι → K → K),
    (∀ i, Continuous (f i)) →
    (∀ (i : ι) (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hab : a + b = 1),
      (f i ⟨a • (x : E) + b • (y : E), hconv x.prop y.prop ha hb hab⟩ : E) =
        a • (f i x : E) + b • (f i y : E)) →
    (∀ i j, Function.Commute (f i) (f j)) →
    ∃ x : K, ∀ i, f i x = x

end ExpandedFA.P1.MarkovKakutaniSpec
