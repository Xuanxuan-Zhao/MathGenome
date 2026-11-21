import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.Schaefer
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.LeraySchauder

/-! Schaefer's fixed point theorem, paper.tex:4749–4772. -/

namespace VariationalNotes.FixedPoints.Schaefer

universe u

/-- Schaefer's bounded-solution-set criterion for an arbitrary real Banach space. -/
theorem schaefer : Spec.FixedPoint.{u} := by
  intro E _ _ _ T hT hcompact hbounded
  have h := ExpandedFA.P1.LeraySchauder.bounded_solution_set_fixed_point ℝ E
  simpa only [NormedSpace.restrictScalars_eq] using h T hT hcompact hbounded

end VariationalNotes.FixedPoints.Schaefer
