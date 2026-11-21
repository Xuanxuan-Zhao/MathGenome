import MathGenome.Internal.Specs.D07.Ch06.SylowExistence
import MathGenome.Internal.D07.Ch06.SylowExistenceLargestPrimePower
import MathGenome.Internal.D07.Ch06.SylowExistenceSubgroupsInPrimePowerGroup
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Sylow existence and smaller prime-power subgroups

The two conclusions of `K07.06.sylow_existence`, paper.tex:1008–1022.
The first is the accepted largest-prime-power existence theorem. For the
second, factor the positive finite group order as `p^a * m`, with `p ∤ m`.
Coprimality cancels `m` from the given prime-power divisibility, giving
`k ≤ a`. Apply the accepted smaller-subgroup theorem inside the subgroup
of order `p^a`, including its inclusion back into the ambient group.
-/

namespace D07.Ch06.SylowExistence

universe u

theorem largest_prime_power_existence (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) : ∃ H : Subgroup G, Nat.card H = p ^ a :=
  SylowExistenceLargestPrimePower.largest_prime_power_existence G p a m hp hcard hm

theorem prime_power_existence (G : Type u) [Group G] [Finite G]
    (p k : ℕ) (hp : p.Prime) (hdiv : p ^ k ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p ^ k := by
  obtain ⟨a, m, hm, hcard⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := G)).ne' p hp.ne_one
  have hpow : p ^ k ∣ p ^ a :=
    (hp.coprime_pow_of_not_dvd hm).symm.dvd_of_dvd_mul_right (hcard ▸ hdiv)
  have hk : k ≤ a := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpow
  obtain ⟨P, hP⟩ := largest_prime_power_existence G p a m hp hcard hm
  obtain ⟨H, _, hH⟩ :=
    SylowExistenceSubgroupsInPrimePowerGroup.exists_subgroup_le_card_pow
      G p a k P hp hP hk
  exact ⟨H, hH⟩

end D07.Ch06.SylowExistence
