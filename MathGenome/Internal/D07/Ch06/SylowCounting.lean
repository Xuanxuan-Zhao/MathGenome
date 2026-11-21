import MathGenome.Internal.Specs.D07.Ch06.SylowCounting
import MathGenome.Internal.D07.Ch06.SylowDefinition

/-!
The number of Sylow subgroups (`paper.tex:1048–1058`).
The accepted cardinality/maximality bridge identifies the source's
subgroups of order p^a with Mathlib's `Sylow p G`, with no multiplicities.
We transport the normalizer index and fixed-point congruence results
across this bijection. Divisibility follows from divisibility of the
index of a Sylow subgroup, after cancelling its positive order p^a
in Lagrange's formula to identify that index with m.
-/

namespace D07.Ch06.SylowCounting

universe u

/-- Forgetting the Sylow structure gives exactly the subgroups of order p^a. -/
noncomputable def sylowEquivSubgroupsOfCard (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) :
    Sylow p G ≃ {Q : Subgroup G // Nat.card Q = p ^ a} := by
  let f : Sylow p G → {Q : Subgroup G // Nat.card Q = p ^ a} := fun S =>
    ⟨S.toSubgroup,
      (SylowDefinition.sylow_iff_card G p a m hp hcard hm S.toSubgroup).mp ⟨S, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro S T h
    exact Sylow.ext (congrArg Subtype.val h)
  · intro Q
    obtain ⟨S, hS⟩ :=
      (SylowDefinition.sylow_iff_card G p a m hp hcard hm Q.val).mpr Q.property
    exact ⟨S, Subtype.ext hS⟩

theorem card_subgroups_eq_card_sylow (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) :
    Nat.card {Q : Subgroup G // Nat.card Q = p ^ a} = Nat.card (Sylow p G) :=
  (Nat.card_congr (sylowEquivSubgroupsOfCard G p a m hp hcard hm)).symm

theorem count_eq_index_normalizer (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) (P : Subgroup G) (hP : Nat.card P = p ^ a) :
    Nat.card {Q : Subgroup G // Nat.card Q = p ^ a} =
      (Subgroup.normalizer (P : Set G)).index := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, rfl⟩ := (SylowDefinition.sylow_iff_card G p a m hp hcard hm P).mpr hP
  rw [card_subgroups_eq_card_sylow G p a m hp hcard hm]
  exact S.card_eq_index_normalizer

theorem count_dvd_cofactor (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) :
    Nat.card {Q : Subgroup G // Nat.card Q = p ^ a} ∣ m := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Sylow p G := Classical.choice Sylow.nonempty
  have hS : Nat.card S.toSubgroup = p ^ a :=
    (SylowDefinition.sylow_iff_card G p a m hp hcard hm S.toSubgroup).mp ⟨S, rfl⟩
  have hindex : S.toSubgroup.index = m := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a)
    calc
      p ^ a * S.toSubgroup.index = Nat.card G := by
        rw [← hS]
        exact S.toSubgroup.card_mul_index
      _ = p ^ a * m := hcard
  rw [card_subgroups_eq_card_sylow G p a m hp hcard hm, ← hindex]
  exact S.card_dvd_index

theorem count_modEq_one (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) :
    Nat.ModEq p (Nat.card {Q : Subgroup G // Nat.card Q = p ^ a}) 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [card_subgroups_eq_card_sylow G p a m hp hcard hm]
  exact card_sylow_modEq_one p G

end D07.Ch06.SylowCounting
