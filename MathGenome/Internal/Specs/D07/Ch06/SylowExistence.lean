import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.SetTheory.Cardinal.NatCard

/-!
Independent statements for `K07.06.sylow_existence`, paper.tex:1008–1022.

The chapter assumes that the ambient group is finite and that `p` is prime.
Orders are the cardinalities of the group and the underlying subgroup types.
The exponents are arbitrary natural numbers, so zero exponents and trivial
groups are included. The source uses the cardinality definition of a Sylow
subgroup here; its equivalence with maximality is a separate entry.
-/

namespace Specs.D07.Ch06.SylowExistence

universe u

/-- A subgroup realizes the full prime-power factor of the group order. -/
def LargestPrimePowerExistence : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
      ∃ H : Subgroup G, Nat.card H = p ^ a

/-- Every prime power dividing the finite group order is a subgroup order. -/
def PrimePowerExistence : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p k : ℕ),
    p.Prime → p ^ k ∣ Nat.card G →
      ∃ H : Subgroup G, Nat.card H = p ^ k

end Specs.D07.Ch06.SylowExistence
