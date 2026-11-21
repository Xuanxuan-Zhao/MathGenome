import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.SetTheory.Cardinal.NatCard

/-!
Independent statements for the prime-power-group step in
`K07.06.sylow_existence` (paper.tex:1021).

The source counts finite groups and assumes that p is prime. No
nontriviality or positivity of either exponent is assumed: k = 0 and
a = 0 are included. Subgroups have the ambient group operations, and
their orders are natural cardinalities of their underlying types.

The second statement applies the first inside a subgroup P of an ambient
finite group G. Taking P to be a largest-prime-power subgroup supplies
the smaller subgroups needed by the parent existence theorem.
-/

namespace Specs.D07.Ch06.SylowExistenceSubgroupsInPrimePowerGroup

universe u

/-- A finite group of order p^a has subgroups of every order p^k for k ≤ a. -/
def ExistsSubgroupCardPow : Prop :=
  ∀ (P : Type u) [Group P] [Finite P] (p a k : ℕ),
    p.Prime → Nat.card P = p ^ a → k ≤ a →
      ∃ H : Subgroup P, Nat.card H = p ^ k

/-- The subgroup found inside P, regarded as a subgroup of G, lies in P. -/
def ExistsSubgroupLECardPow : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a k : ℕ) (P : Subgroup G),
    p.Prime → Nat.card P = p ^ a → k ≤ a →
      ∃ H : Subgroup G, H ≤ P ∧ Nat.card H = p ^ k

end Specs.D07.Ch06.SylowExistenceSubgroupsInPrimePowerGroup
