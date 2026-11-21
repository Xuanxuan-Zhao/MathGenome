import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces
import Mathlib.Analysis.Complex.Basic

/-!
Independent statements for `paper.tex:4988–4993`,
Proposition `fa2:p1:c24:face-extreme`.

The topology is the supplied Hausdorff locally convex vector-space topology.
All extreme points and faces use real convex combinations, including in a
complex ambient space. No norm, completeness, or metrizability is assumed.
-/

universe u

namespace ExpandedFA.P1.C24FaceExtremeSpec

open ExpandedFA.P1.C24FacesSpec

/-- A nonempty compact convex set in a real Hausdorff LCS has an extreme point. -/
def realCompactConvexType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K : Set E),
    K.Nonempty → IsCompact K → Convex ℝ K →
    ∃ x ∈ K, x ∈ extremePoints K

/-- Every nonempty compact face contains an extreme point of the original set.
The ambient set need not itself be compact or convex, so this also covers every
compact face of the compact convex set in the proposition. Nonemptiness and
convexity of the face are included in the shared `IsCompactFace` definition. -/
def realCompactFaceType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K F : Set E),
    IsCompactFace K F → ∃ x ∈ F, x ∈ extremePoints K

/-- Complex spaces retain their given topology and use their underlying real space. -/
def complexCompactConvexType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K : Set E),
    K.Nonempty → IsCompact K → Convex ℝ K →
    ∃ x ∈ K, x ∈ extremePoints K

/-- A complex compact face contains a point extreme in the original set over ℝ. -/
def complexCompactFaceType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K F : Set E),
    IsCompactFace K F → ∃ x ∈ F, x ∈ extremePoints K

end ExpandedFA.P1.C24FaceExtremeSpec
