import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.SetTheory.Cardinal.Finite

/-!
Independent statement of K07.06.no_simple_order_thirty,
`paper.tex:1095–1102`: a finite group of order thirty is not simple.
`IsSimpleGroup` includes nontriviality and requires that every normal
subgroup be either the identity subgroup or the whole group.
-/

namespace Specs.D07.Ch06.NoSimpleOrderThirty

universe u

def NotSimple : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Nat.card G = 30 → ¬ IsSimpleGroup G

end Specs.D07.Ch06.NoSimpleOrderThirty
