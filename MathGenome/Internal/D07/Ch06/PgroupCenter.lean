import MathGenome.Internal.Specs.D07.Ch06.PgroupCenter
import MathGenome.Internal.D07.Ch06.PgroupDefinition

/-!
The center of a nontrivial finite p-group (`K07.06.pgroup_center`).
The accepted cardinality/elementwise bridge supplies Mathlib's `IsPGroup`.
Its center theorem follows from the conjugation fixed-point congruence.
The center is itself a finite p-group; its nontriviality forces its
p-power cardinality to have positive exponent, yielding divisibility.
-/

namespace D07.Ch06.PgroupCenter

universe u

theorem center_nontrivial (G : Type u) [Group G] [Nontrivial G]
    (p : ℕ) (hp : p.Prime) (hG : PgroupDefinition.FinitePGroup p G) :
    Nontrivial (Subgroup.center G) := by
  let : Finite G := hG.1
  let : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p G :=
    ((PgroupDefinition.finitePGroup_iff_finite_isPGroup G p hp).mp hG).2
  exact hP.center_nontrivial

theorem prime_dvd_card_center (G : Type u) [Group G] [Nontrivial G]
    (p : ℕ) (hp : p.Prime) (hG : PgroupDefinition.FinitePGroup p G) :
    p ∣ Nat.card (Subgroup.center G) := by
  let : Finite G := hG.1
  let : Fact p.Prime := ⟨hp⟩
  let : Nontrivial (Subgroup.center G) := center_nontrivial G p hp hG
  have hP : IsPGroup p G :=
    ((PgroupDefinition.finitePGroup_iff_finite_isPGroup G p hp).mp hG).2
  obtain ⟨n, hn, hcard⟩ :=
    (hP.to_subgroup (Subgroup.center G)).nontrivial_iff_card.mp inferInstance
  rw [hcard]
  exact dvd_pow_self p (ne_of_gt hn)

end D07.Ch06.PgroupCenter
