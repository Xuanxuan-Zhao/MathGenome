import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ExtremeAffineLifting

/-!
Independent statements for `fa2:p1:milman-converse`, paper.tex:5415–5436.
Convexity and extreme points are real, including for a complex ambient space.
All closures and compactness refer to the given Hausdorff locally convex
topology. Neither nonemptiness, metrizability nor completeness is imposed.
The lifting statements use maps on the subsets, as in the shared interface.
-/

universe u v

namespace ExpandedFA.P1.MilmanConverseSpec

open C24FacesSpec

/-- Extreme points of a compact closed convex hull lie in the closure of its generators. -/
def realConverseType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K A : Set E),
    K = closure (convexHull ℝ A) → IsCompact K →
    extremePoints K ⊆ closure A

/-- The complex version retains real convex combinations and the original topology. -/
def complexConverseType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K A : Set E),
    K = closure (convexHull ℝ A) → IsCompact K →
    extremePoints K ⊆ closure A

/-- Continuous affine surjections between compact convex real LCS subsets lift extreme points. -/
def realLiftingType : Prop := ExtremeAffineLiftingSpec.realLiftingType.{u, v}

/-- The same lifting statement for complex ambient spaces and real affineness. -/
def complexLiftingType : Prop := ExtremeAffineLiftingSpec.complexLiftingType.{u, v}

end ExpandedFA.P1.MilmanConverseSpec
