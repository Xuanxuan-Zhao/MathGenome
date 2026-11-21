import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24FaceExtreme

/-!
Independent statements for the extreme-point lifting clause of
`fa2:p1:milman-converse`, paper.tex:5415–5436.

Maps are defined on the subsets themselves, with their given subspace
topologies. Affineness means preservation of real convex combinations;
no extension to the ambient vector spaces is required. This is also the
meaning of affineness in the complex case. Empty compact convex sets are
allowed; an extreme point of the target supplies the necessary nonemptiness.
-/

universe u v

namespace ExpandedFA.P1.ExtremeAffineLiftingSpec

open C24FacesSpec

/-- Affineness for a map between convex subsets, expressed without requiring
the subsets to be vector spaces or choosing an ambient extension. -/
def PreservesConvexCombinations
    {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {K : Set E} {L : Set F} (T : K → L) : Prop :=
  ∀ (x z w : K) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    (w : E) = a • (x : E) + b • (z : E) →
    (T w : F) = a • (T x : F) + b • (T z : F)

/-- The fiber as a subset of the original ambient space. -/
def affineFiber {E : Type u} {F : Type v} {K : Set E} {L : Set F}
    (T : K → L) (y : L) : Set E :=
  Subtype.val '' (T ⁻¹' {y})

/-- The inverse image of an extreme point under a continuous affine
surjection is a nonempty compact face. This part needs no local convexity. -/
def compactFiberType : Prop :=
  ∀ {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [T2Space F]
    (K : Set E) (L : Set F) (T : K → L),
    IsCompact K → Convex ℝ K → Continuous T →
    PreservesConvexCombinations T → Function.Surjective T →
    ∀ y : L, (y : F) ∈ extremePoints L → IsCompactFace K (affineFiber T y)

/-- Continuous affine surjections between compact convex subsets of real
Hausdorff LCSs lift every extreme point to an extreme point. -/
def realLiftingType : Prop :=
  ∀ {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
    [LocallyConvexSpace ℝ F]
    (K : Set E) (L : Set F) (T : K → L),
    IsCompact K → Convex ℝ K → IsCompact L → Convex ℝ L →
    Continuous T → PreservesConvexCombinations T → Function.Surjective T →
    ∀ y : L, (y : F) ∈ extremePoints L →
      ∃ x : K, (x : E) ∈ extremePoints K ∧ T x = y

/-- The same assertion for complex Hausdorff LCSs, with real convexity
and the original topologies on both spaces. -/
def complexLiftingType : Prop :=
  ∀ {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [T2Space F]
    [LocallyConvexSpace ℝ F]
    (K : Set E) (L : Set F) (T : K → L),
    IsCompact K → Convex ℝ K → IsCompact L → Convex ℝ L →
    Continuous T → PreservesConvexCombinations T → Function.Surjective T →
    ∀ y : L, (y : F) ∈ extremePoints L →
      ∃ x : K, (x : E) ∈ extremePoints K ∧ T x = y

end ExpandedFA.P1.ExtremeAffineLiftingSpec
