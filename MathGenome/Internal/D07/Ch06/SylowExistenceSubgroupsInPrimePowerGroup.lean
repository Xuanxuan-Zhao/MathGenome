import MathGenome.Internal.Specs.D07.Ch06.SylowExistenceSubgroupsInPrimePowerGroup
import Mathlib.GroupTheory.Sylow

/-!
The prime-power-group step of `K07.06.sylow_existence`, paper.tex:1021.

For k ≤ a, p^k divides p^a. Mathlib's proved finite-group theorem
`Sylow.exists_subgroup_card_pow_prime` then supplies the required subgroup.
Its hypotheses are finiteness, primality, and divisibility, with no
positive-exponent restriction. In particular the trivial group and the
trivial subgroup are covered.

To use the result inside an ambient subgroup, map the resulting subgroup
along the injective subtype homomorphism. This preserves cardinality and
places its image inside the specified subgroup. Thus the parent theorem
can apply this helper to its largest-prime-power subgroup.
-/

namespace D07.Ch06.SylowExistenceSubgroupsInPrimePowerGroup

universe u

theorem exists_subgroup_card_pow (P : Type u) [Group P] [Finite P]
    (p a k : ℕ) (hp : p.Prime) (hP : Nat.card P = p ^ a) (hk : k ≤ a) :
    ∃ H : Subgroup P, Nat.card H = p ^ k := by
  let : Fact p.Prime := ⟨hp⟩
  apply Sylow.exists_subgroup_card_pow_prime p
  rw [hP]
  exact pow_dvd_pow p hk

theorem exists_subgroup_le_card_pow (G : Type u) [Group G] [Finite G]
    (p a k : ℕ) (P : Subgroup G) (hp : p.Prime)
    (hP : Nat.card P = p ^ a) (hk : k ≤ a) :
    ∃ H : Subgroup G, H ≤ P ∧ Nat.card H = p ^ k := by
  obtain ⟨H, hH⟩ := exists_subgroup_card_pow P p a k hp hP hk
  refine ⟨H.map P.subtype, Subgroup.map_subtype_le H, ?_⟩
  rw [Subgroup.card_map_of_injective P.subtype_injective, hH]

end D07.Ch06.SylowExistenceSubgroupsInPrimePowerGroup
