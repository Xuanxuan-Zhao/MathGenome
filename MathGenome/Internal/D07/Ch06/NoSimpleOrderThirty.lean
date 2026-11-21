import MathGenome.Internal.Specs.D07.Ch06.NoSimpleOrderThirty
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
K07.06.no_simple_order_thirty, `paper.tex:1095–1102`.

We use the library's squarefree-order theorem: such a finite group has
cyclic Sylow subgroups and is solvable. A simple solvable group is
commutative, and a simple commutative group has prime order. Since
thirty is squarefree and composite, this gives the stated obstruction.
This is an alternative proof of the paper's Sylow counting argument;
no additional hypothesis on the group is imposed.
-/

namespace D07.Ch06.NoSimpleOrderThirty

universe u

theorem no_simple_order_thirty (G : Type u) [Group G] [Finite G]
    (hcard : Nat.card G = 30) : ¬ IsSimpleGroup G := by
  intro hsimple
  let : IsSimpleGroup G := hsimple
  have hsquarefree : Squarefree (Nat.card G) := by
    rw [hcard]
    change Squarefree (2 * (3 * 5) : ℕ)
    apply (Nat.squarefree_mul (by decide : Nat.Coprime 2 (3 * 5))).mpr
    refine ⟨Nat.squarefree_two, ?_⟩
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 5)).mpr
      ⟨Nat.prime_three.prime.squarefree, Nat.prime_five.prime.squarefree⟩
  let : IsZGroup G := IsZGroup.of_squarefree hsquarefree
  have hcomm : ∀ a b : G, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  let : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  have hprime : (Nat.card G).Prime := IsSimpleGroup.prime_card
  exact (by decide : ¬ Nat.Prime 30) (hcard ▸ hprime)

end D07.Ch06.NoSimpleOrderThirty
