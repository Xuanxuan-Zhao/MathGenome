import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24KreinMilman
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24Faces
import Mathlib.Analysis.Convex.KreinMilman

/-!
# Krein–Milman in the given locally convex topology

Theorem `fa2:p1:c24:krein-milman` (also `fa2:p1:krein-milman`),
paper.tex:5010–5019.

Mathlib's `closure_convexHull_extremePoints` applies to the supplied Hausdorff
locally convex real topology. The upstream `extremePoints_eq_native` identifies
the paper's extreme points with its native extreme-point set. For a complex
space, restriction to real scalars preserves the topology and uses real convex
combinations throughout.
-/

universe u

namespace ExpandedFA.P1

/-- A compact convex set is the closed real convex hull of its extreme points. -/
theorem real_krein_milman : C24KreinMilmanSpec.realKreinMilmanType.{u} := by
  intro E _ _ _ _ _ _ _ K _hne hcompact hconv
  change K = closure (convexHull ℝ (extremePoints K))
  rw [extremePoints_eq_native]
  exact (closure_convexHull_extremePoints hcompact hconv).symm

/-- Krein–Milman for a complex space, with real convexity and its given topology. -/
theorem complex_krein_milman : C24KreinMilmanSpec.complexKreinMilmanType.{u} := by
  intro E _ _ _ _ _ _ _ K hne hcompact hconv
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact real_krein_milman K hne hcompact hconv

end ExpandedFA.P1
