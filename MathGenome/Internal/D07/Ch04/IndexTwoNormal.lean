import MathGenome.Internal.D07.Ch03.IndexTwoPreliminary
import MathGenome.Internal.Specs.D07.Ch04.IndexTwoNormal

/-!
The index-two normality corollary `K07.04.index_two_normal`
(paper.tex:730–736). This is the earlier index-two lemma, applied without
any finiteness assumption on the ambient group or the subgroup.
-/

namespace D07.Ch04.IndexTwoNormal

universe u

/-- A subgroup of index two in any group is normal. -/
theorem normal_of_index_two (G : Type u) [Group G] (H : Subgroup G)
    (hH : H.index = 2) : H.Normal :=
  D07.Ch03.IndexTwoPreliminary.normal_of_index_two G H hH

end D07.Ch04.IndexTwoNormal
