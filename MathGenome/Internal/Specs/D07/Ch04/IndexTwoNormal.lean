import Mathlib.GroupTheory.Index

/-!
Independent specification of `K07.04.index_two_normal`
(paper.tex:730–736, chapters/M07.04.tex:71–77).

The index is the number of left cosets. Mathlib encodes an infinite coset
space by index zero, so `H.index = 2` asserts exactly that there are two
cosets. The ambient group and the subgroup need not be finite. `H.Normal`
is closure under all ambient conjugations, with no prior normality assumed.
-/

namespace Specs.D07.Ch04.IndexTwoNormal

universe u

/-- Every subgroup of index two in an arbitrary group is normal. -/
def NormalOfIndexTwo : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G), H.index = 2 → H.Normal

end Specs.D07.Ch04.IndexTwoNormal
