import MathGenome.Internal.Specs.D07.Ch01.SubgroupDefinitionTest
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.SetTheory.Cardinal.NatCard

/-!
Independent specification of the largest-prime-power assertion of
`K07.06.sylow_existence` (paper.tex:1008–1022).

The ambient group is finite, `p` is prime, and `a` may be zero. The
cardinality hypothesis is the source's factorization `|G| = p^a * m`
with `p ∤ m`. The conclusion concerns an ordinary subgroup with the
inherited group operations; no containment or conjugacy is assumed.
-/

namespace Specs.D07.Ch06.SylowExistenceLargestPrimePower

universe u

/-- Existence of a subgroup whose order is the full `p`-power factor. -/
def LargestPrimePowerExistence : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
      ∃ H : Subgroup G, Nat.card H = p ^ a

end Specs.D07.Ch06.SylowExistenceLargestPrimePower
