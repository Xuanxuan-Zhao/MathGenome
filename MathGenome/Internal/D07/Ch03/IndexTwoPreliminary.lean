import MathGenome.Internal.Specs.D07.Ch03.IndexTwoPreliminary
import Mathlib.GroupTheory.IndexNormal

/-!
# Subgroups of index two

The preliminary lemma at paper.tex:641–646. The library result applies to
arbitrary groups and uses the set of left cosets to define the index.
In particular, it requires neither a finite ambient group nor normality
as a prerequisite for forming the coset space.
-/

namespace D07.Ch03.IndexTwoPreliminary

universe u

/-- A subgroup of index two in any group is normal. -/
theorem normal_of_index_two (G : Type u) [Group G] (H : Subgroup G)
    (hH : H.index = 2) : H.Normal :=
  Subgroup.normal_of_index_eq_two hH

end D07.Ch03.IndexTwoPreliminary
