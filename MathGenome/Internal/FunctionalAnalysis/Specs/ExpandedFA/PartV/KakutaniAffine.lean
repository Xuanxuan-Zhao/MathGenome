import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.MilmanConverse
import Mathlib.Topology.Homeomorph.Defs

/-!
Independent statements for `fa2:p5:kakutani-affine`, paper.tex:23219–23244.
The maps act on K with its original subspace topology. The abstract indexing
group need not have a topology or act faithfully. Affineness uses real convex
combinations, including in the complex case.
-/

universe u v

namespace ExpandedFA.PartV.KakutaniAffineSpec

open Filter Set
open scoped Topology

/-- Ordinary pointwise equicontinuity, expressed using zero neighborhoods in
the ambient topological vector space and neighborhoods in K. The difference
formulation is the translation-uniformity formulation of equicontinuity. -/
def EquicontinuousOnK {E : Type u} [AddCommGroup E] [TopologicalSpace E]
    {G : Type v} {K : Set E} (T : G → K ≃ₜ K) : Prop :=
  ∀ x : K, ∀ U ∈ 𝓝 (0 : E), ∀ᶠ y in 𝓝 x,
    ∀ g : G, (T g y : E) - (T g x : E) ∈ U

/-- Kakutani's theorem for equicontinuous groups on a real compact convex set.
No ambient extension, metrizability, completeness, commutativity, or continuity
in the group parameter is assumed. -/
def realKakutaniType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] {G : Type v} [Group G]
    (K : Set E) (T : G → K ≃ₜ K),
    K.Nonempty → IsCompact K → Convex ℝ K →
    (∀ x, T 1 x = x) → (∀ g h x, T (g * h) x = T g (T h x)) →
    (∀ g, ExpandedFA.P1.ExtremeAffineLiftingSpec.PreservesConvexCombinations (T g)) →
    EquicontinuousOnK T → ∃ x : K, ∀ g, T g x = x

/-- The complex version has the same real convexity and unchanged topology. -/
def complexKakutaniType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E] {G : Type v} [Group G]
    (K : Set E) (T : G → K ≃ₜ K),
    K.Nonempty → IsCompact K → Convex ℝ K →
    (∀ x, T 1 x = x) → (∀ g h x, T (g * h) x = T g (T h x)) →
    (∀ g, ExpandedFA.P1.ExtremeAffineLiftingSpec.PreservesConvexCombinations (T g)) →
    EquicontinuousOnK T → ∃ x : K, ∀ g, T g x = x

end ExpandedFA.PartV.KakutaniAffineSpec
