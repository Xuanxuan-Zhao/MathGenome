import MathGenome.Internal.Specs.D07.Ch06.SylowExistenceLargestPrimePower
import Mathlib.GroupTheory.Sylow

/-!
# Existence of a subgroup of the largest prime-power order

The largest-prime-power assertion of `K07.06.sylow_existence`.
Mathlib's prime-power subgroup existence theorem needs only divisibility
of the group order by the required prime power. The source's factorization
supplies precisely that divisibility. The additional condition `p ∤ m`
identifies this power as the full prime-power factor and is retained in
our statement. There is no positive-exponent restriction, so `a = 0`
and the trivial ambient group are included.
-/

namespace D07.Ch06.SylowExistenceLargestPrimePower

universe u

/-- A finite group of order `p^a * m`, with `p ∤ m`, has a subgroup
of order `p^a`. -/
theorem largest_prime_power_existence (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (_hm : ¬ p ∣ m) : ∃ H : Subgroup G, Nat.card H = p ^ a := by
  letI : Fact p.Prime := ⟨hp⟩
  exact Sylow.exists_subgroup_card_pow_prime p ⟨m, hcard⟩

end D07.Ch06.SylowExistenceLargestPrimePower
