import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.SetTheory.Cardinal.Finite

/-!
Independent statements for `K07.06.cyclic_central_quotient`
(`paper.tex:990–996`, chapters/M07.06.tex:41–47).

The first statement applies to every group: cyclicity means generation by
integer powers, and neither the group nor its central quotient is assumed
finite or nontrivial. The second statement concerns finite groups of order
the square of a prime. Both conclusions refer to the given multiplication.
-/

namespace Specs.D07.Ch06.CyclicCentralQuotient

universe u

/-- A cyclic quotient by the center forces all elements to commute. -/
def CyclicCentralQuotientAbelian : Prop :=
  ∀ (G : Type u) [Group G],
    IsCyclic (G ⧸ Subgroup.center G) → ∀ x y : G, x * y = y * x

/-- Every finite group of prime-square order is abelian. -/
def PrimeSquareAbelian : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ),
    p.Prime → Nat.card G = p ^ 2 → ∀ x y : G, x * y = y * x

end Specs.D07.Ch06.CyclicCentralQuotient
