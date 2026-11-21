import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24FaceExtreme
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24FaceOperations
import Mathlib.Analysis.Convex.KreinMilman

/-!
# Extreme points in every compact face

Proposition `fa2:p1:c24:face-extreme` (paper.tex:4988–4993).

Mathlib's `IsCompact.extremePoints_nonempty` applies to the given Hausdorff
locally convex real topology. It uses Zorn's lemma, compact intersections, and
continuous real linear separation, without normability or completeness.
The accepted identification with native extreme points gives the first claim.
For a compact face, apply that claim to the face itself, then transfer the
resulting singleton face to the original set by face transitivity.
-/

universe u

namespace ExpandedFA.P1

/-- Every nonempty compact convex set has an extreme point, in its given topology. -/
theorem real_compact_convex_extremePoint :
    C24FaceExtremeSpec.realCompactConvexType.{u} := by
  intro E _ _ _ _ _ _ _ K hne hcompact _hconv
  obtain ⟨x, hx⟩ := hcompact.extremePoints_nonempty hne
  refine ⟨x, hx.1, ?_⟩
  change x ∈ extremePoints K
  rwa [extremePoints_eq_native]

/-- The point supplied in a compact face is extreme in the original set. -/
theorem real_compact_face_extremePoint :
    C24FaceExtremeSpec.realCompactFaceType.{u} := by
  intro E _ _ _ _ _ _ _ K F hF
  obtain ⟨x, hxF, hxext⟩ := real_compact_convex_extremePoint F
    hF.1.1 hF.2 hF.1.2.1
  refine ⟨x, hxF, ?_⟩
  exact (isFace_singleton_iff K x).mp
    (IsFace.trans hF.1 ((isFace_singleton_iff F x).mpr hxext))

/-- Restriction of complex scalars to real scalars preserves the ambient topology. -/
theorem complex_compact_convex_extremePoint :
    C24FaceExtremeSpec.complexCompactConvexType.{u} := by
  intro E _ _ _ _ _ _ _ K hne hcompact hconv
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact real_compact_convex_extremePoint K hne hcompact hconv

/-- Real convexity and the original topology are used also for complex faces. -/
theorem complex_compact_face_extremePoint :
    C24FaceExtremeSpec.complexCompactFaceType.{u} := by
  intro E _ _ _ _ _ _ _ K F hF
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact real_compact_face_extremePoint K F hF

end ExpandedFA.P1
