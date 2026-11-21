import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
Independent statement of Ryll--Nardzewski, paper.tex:5757--5764.
The manuscript's Hausdorff convention is at paper.tex:1745--1758.
Maps act on K itself. Composition closure expresses the semigroup condition
without imposing an identity or commutativity. Continuity is for σ(E,E′),
where E′ is the continuous scalar-linear dual over the original field.
The closure in the noncontraction premise is for the original topology.
Convexity and affineness use real coefficients, also over complex scalars.
-/

universe u v w

namespace ExpandedFA.P1.RyllNardzewskiSpec

/-- The subspace weak topology of K, using the original scalar-linear dual. -/
noncomputable def weakSubtypeTopology (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] (K : Set E) :
    TopologicalSpace K :=
  TopologicalSpace.induced (fun x : K => toWeakSpace 𝕜 E (x : E)) inferInstance

/-- The complete source theorem, including arbitrary semigroups and both fields. -/
def CommonFixedPoint : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K : Set E),
    K.Nonempty → IsCompact (toWeakSpace 𝕜 E '' K) → ∀ hconv : Convex ℝ K,
    ∀ (ι : Type w) (f : ι → K → K),
    (∀ i j, ∃ k, f k = f i ∘ f j) →
    (∀ i, @Continuous K K (weakSubtypeTopology 𝕜 E K)
      (weakSubtypeTopology 𝕜 E K) (f i)) →
    (∀ (i : ι) (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hab : a + b = 1),
      (f i ⟨a • (x : E) + b • (y : E), hconv x.prop y.prop ha hb hab⟩ : E) =
        a • (f i x : E) + b • (f i y : E)) →
    (∀ x y : K, x ≠ y →
      (0 : E) ∉ closure (Set.range (fun i => (f i x : E) - (f i y : E)))) →
    ∃ x : K, ∀ i, f i x = x

end ExpandedFA.P1.RyllNardzewskiSpec
