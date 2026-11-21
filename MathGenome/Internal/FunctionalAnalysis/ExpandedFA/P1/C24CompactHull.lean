import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24CompactHull
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! Compactness of the norm-closed real convex hull in a Banach space. -/

namespace ExpandedFA.P1

/-- Compactness gives total boundedness; real convex hull and closure
preserve it. A closed subset of the complete normed ambient space is
complete, so the complete-totally-bounded criterion gives compactness.
This argument also includes the empty compact set and the zero space. -/
theorem compact_closed_convexHull_banach : C24CompactHullSpec.CompactHull := by
  intro 𝕜 E _ _ _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro Q hQ
  exact hQ.totallyBounded.convexHull.closure.isCompact_of_isClosed isClosed_closure

end ExpandedFA.P1
