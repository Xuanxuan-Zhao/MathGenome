import MathGenome.Internal.Specs.D07.Ch02.ElementOrder
import MathGenome.Internal.Specs.D07.Ch02.CyclicDefinition
import Mathlib.SetTheory.Cardinal.NatCard

/-!
Independent statements for `K07.06.cauchy`, paper.tex:954–961.

The ambient group is finite and need not be abelian. Primality and
divisibility are explicit hypotheses. The canonical `orderOf` agrees with
the source's least positive annihilating exponent by the upstream element
order specification; a prime is positive, so its zero/infinite convention
does not enter the conclusion. Subgroup order is its finite cardinality.
No nontriviality hypothesis is imposed on the ambient group.
-/

namespace Specs.D07.Ch06.Cauchy

universe u

/-- Every prime divisor of the order of a finite group is an element order. -/
def ExistsElementOrderEq : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ),
    p.Prime → p ∣ Nat.card G → ∃ g : G, orderOf g = p

/-- The same hypotheses give a subgroup with exactly p elements. -/
def ExistsSubgroupCardEq : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ),
    p.Prime → p ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = p

end Specs.D07.Ch06.Cauchy
