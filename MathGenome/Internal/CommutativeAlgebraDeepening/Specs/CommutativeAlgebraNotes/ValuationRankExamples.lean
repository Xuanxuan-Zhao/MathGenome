import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LexicographicLaurentValuation
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RationalValueGroupExample

namespace Specs.CommutativeAlgebraNotes.ValuationRankExamples

universe u

/-- The iterated Laurent-series and factorial-tower examples, with the convex
subgroups of their ordered value groups. -/
def RankExamples : Prop :=
  LexicographicLaurentValuation.LaurentExample.{u} ∧
  LexicographicLaurentValuation.ConvexSubgroups ∧
  RationalValueGroupExample.Example.{u} ∧
  RationalValueGroupExample.ConvexSubgroups

end Specs.CommutativeAlgebraNotes.ValuationRankExamples
