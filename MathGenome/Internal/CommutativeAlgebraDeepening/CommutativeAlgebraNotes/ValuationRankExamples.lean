import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ValuationRankExamples
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LexicographicLaurentValuation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RationalValueGroupExample

namespace CommutativeAlgebraNotes.ValuationRankExamples

universe u

/-- Over every field, the iterated Laurent series and the factorial tower
give non-Noetherian valuation rings of ranks two and one, respectively. -/
theorem valuation_rank_examples :
    Specs.CommutativeAlgebraNotes.ValuationRankExamples.RankExamples.{u} :=
  ⟨LexicographicLaurentValuation.laurent_example,
    LexicographicLaurentValuation.convex_subgroups,
    RationalValueGroupExample.rational_value_group_example,
    RationalValueGroupExample.convex_subgroups_rat⟩

end CommutativeAlgebraNotes.ValuationRankExamples
