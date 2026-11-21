import MathGenome.Internal.Specs.D07.Ch06.CyclicCentralQuotient
import Mathlib.GroupTheory.PGroup

/-!
The cyclic-central-quotient criterion and its prime-square consequence.

Mathlib's criterion writes elements as powers of a lift of a quotient
generator times central elements. It has no finiteness hypothesis. For
prime-square order, the center theorem and subgroup index formula make
the central quotient have order dividing the prime, hence be cyclic.
-/

namespace D07.Ch06.CyclicCentralQuotient

universe u

theorem cyclic_central_quotient_abelian (G : Type u) [Group G]
    (hcyclic : IsCyclic (G ⧸ Subgroup.center G)) :
    ∀ x y : G, x * y = y * x := by
  let : IsCyclic (G ⧸ Subgroup.center G) := hcyclic
  exact (isMulCommutative_of_isCyclic_quotient_center_self G).is_comm.comm

theorem prime_square_abelian (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ 2) :
    ∀ x y : G, x * y = y * x := by
  let : Fact p.Prime := ⟨hp⟩
  exact cyclic_central_quotient_abelian G
    (IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq hcard)

end D07.Ch06.CyclicCentralQuotient
