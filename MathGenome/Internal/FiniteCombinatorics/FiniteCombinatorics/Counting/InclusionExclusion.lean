import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.InclusionExclusion
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

open scoped BigOperators

namespace FiniteCombinatorics.Counting

/-- Finite inclusion–exclusion, with cardinalities interpreted as integers.
There is no nonemptiness assumption on the index set. -/
theorem inclusion_exclusion_integer :
    Specs.FiniteCombinatorics.Counting.inclusionExclusionInteger := by
  intro ι α _ I A
  exact Finset.inclusion_exclusion_card_biUnion I A

/-- Finite inclusion–exclusion in any coefficient ring. -/
theorem inclusion_exclusion_ring :
    Specs.FiniteCombinatorics.Counting.inclusionExclusionRing := by
  intro ι α R _ _ I A
  have h := inclusion_exclusion_integer ι α I A
  have hR := congrArg (fun z : ℤ => (z : R)) h
  simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one] using hR

end FiniteCombinatorics.Counting
