import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.Schauder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.LeraySchauder

/-! Schauder's fixed point theorem for a relatively compact entire image.
The domain may be unbounded. -/

namespace VariationalNotes.FixedPoints.Schauder

universe u

/-- Schauder's theorem (`paper.tex`, Theorem 10.4). -/
theorem fixed_point : Spec.FixedPoint.{u} := by
  intro E _ _ _ C hCne hCclosed hCconvex F hF hcompact
  exact ExpandedFA.P1.LeraySchauder.compact_image_fixed_point
    ℝ E C hCne hCclosed hCconvex F hF hcompact

end VariationalNotes.FixedPoints.Schauder
