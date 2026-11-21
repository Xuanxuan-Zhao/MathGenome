import MathGenome.Internal.Specs.D07.Ch06.Cauchy
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
Cauchy's theorem (`K07.06.cauchy`, paper.tex:954–961).

Mathlib's Cauchy theorem proves element existence for arbitrary finite
groups by cyclically rotating tuples whose product is one. The subgroup
conclusion is obtained from the integer powers of that element, whose
cardinality is its order. In particular no commutativity is required.
-/

namespace D07.Ch06.Cauchy

universe u

theorem exists_element_order_eq (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card G) :
    ∃ g : G, orderOf g = p := by
  let : Fact p.Prime := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card' p hdiv

theorem exists_subgroup_card_eq (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p := by
  obtain ⟨g, hg⟩ := exists_element_order_eq G p hp hdiv
  exact ⟨Subgroup.zpowers g, (Nat.card_zpowers g).trans hg⟩

end D07.Ch06.Cauchy
