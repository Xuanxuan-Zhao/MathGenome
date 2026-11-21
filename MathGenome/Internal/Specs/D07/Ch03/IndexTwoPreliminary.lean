import MathGenome.Internal.Specs.D07.Ch03.CosetsPartition
import Mathlib.GroupTheory.Index

/-!
Independent specification of `support.index_two_preliminary`
(paper.tex:641–646, chapters/M07.03.tex:70–75).

The carrier is an arbitrary group, possibly infinite. `H.index` is the
natural cardinality of the set of left cosets (`G ⧸ H`), which is defined
without a normality assumption. Its value being two imposes exactly the
source's finite-index hypothesis; no finiteness of `G` or `H` is required.
`H.Normal` means closure under every ambient conjugation
`g * h * g⁻¹`, the normality condition in the source.
-/

namespace Specs.D07.Ch03.IndexTwoPreliminary

universe u

/-- Every subgroup of index two in an arbitrary group is normal. -/
def NormalOfIndexTwo : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G), H.index = 2 → H.Normal

end Specs.D07.Ch03.IndexTwoPreliminary
