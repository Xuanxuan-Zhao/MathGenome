import MathGenome.Internal.Specs.D07.Ch02.ElementOrder
import MathGenome.Internal.Specs.D07.Ch02.CyclicModelsIsomorphism
import Mathlib.Algebra.Group.Prod

/-!
Independent statements for `K07.04.order_product_element`
(paper.tex:753–763, chapters/M07.04.tex:94–104).

The pair carries the ordinary coordinatewise group operations. As in the
upstream element-order specification, zero `orderOf` means infinite order.
No finiteness or commutativity of the ambient groups is assumed in the
element-order statements. The finite cyclic model is the upstream model
`Multiplicative (ZMod n)`, whose operation is residue addition. Positive
moduli include one, so trivial factors are included.
-/

namespace Specs.D07.Ch04.OrderProductElement

universe u v

/-- The least common multiple formula for two finite-order elements. -/
def FinitePairOrder : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (x : G) (y : H),
    0 < orderOf x → 0 < orderOf y →
      orderOf (x, y) = Nat.lcm (orderOf x) (orderOf y)

/-- An infinite-order component makes the pair have infinite order. -/
def InfinitePairOrder : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (x : G) (y : H),
    orderOf x = 0 ∨ orderOf y = 0 → orderOf (x, y) = 0

/-- The criterion for arbitrary finite cyclic groups, stated independently
of their choice of models or generators. Group finiteness implies positive
cardinality, including cardinality one. -/
def FiniteCyclicProductIff : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H]
    [Finite G] [Finite H] [IsCyclic G] [IsCyclic H],
    IsCyclic (G × H) ↔ Nat.gcd (Nat.card G) (Nat.card H) = 1

/-- The source's explicit `C_m × C_n` statement for every positive `m,n`. -/
def CyclicModelsProductIff : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    (IsCyclic (Multiplicative (ZMod m) × Multiplicative (ZMod n)) ↔
      Nat.gcd m n = 1)

end Specs.D07.Ch04.OrderProductElement
