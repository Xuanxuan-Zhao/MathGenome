import MathGenome.Internal.Specs.D07.Ch06.SylowNormalIffUnique
import MathGenome.Internal.D07.Ch06.SylowConjugacy
import MathGenome.Internal.D07.Ch04.CharacteristicSubgroups

/-!
Uniqueness, normality, and characteristicity, paper.tex:1060–1068.

The library's normal-to-unique lemma uses conjugacy of Sylow subgroups.
In the reverse direction, uniqueness makes every conjugate equal to the
original subgroup. Likewise automorphisms permute Sylow subgroups, so a
unique one is characteristic. Counting uses the actual finite type of
Sylow subgroups; the cardinality versions use the upstream bridge rather
than assuming that an arbitrary p-subgroup is Sylow.
-/

namespace D07.Ch06.SylowNormalIffUnique

universe u

theorem normal_iff_unique (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (P : Sylow p G) :
    P.toSubgroup.Normal ↔ ∀ Q : Sylow p G, Q = P := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hP Q
    letI := Sylow.unique_of_normal P hP
    exact Subsingleton.elim Q P
  · intro hP
    letI : Subsingleton (Sylow p G) :=
      ⟨fun Q R => (hP Q).trans (hP R).symm⟩
    exact Sylow.normal_of_subsingleton P

theorem normal_iff_count_one (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (P : Sylow p G) :
    P.toSubgroup.Normal ↔ Nat.card (Sylow p G) = 1 := by
  rw [normal_iff_unique G p hp P]
  constructor
  · intro hP
    exact Nat.card_eq_one_iff_exists.mpr ⟨P, hP⟩
  · intro h Q
    exact (Nat.card_eq_one_iff_unique.mp h).1.elim Q P

theorem characteristic_of_normal (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (P : Sylow p G)
    (hP : P.toSubgroup.Normal) : P.toSubgroup.Characteristic := by
  have huniq := (normal_iff_unique G p hp P).mp hP
  letI : Subsingleton (Sylow p G) :=
    ⟨fun Q R => (huniq Q).trans (huniq R).symm⟩
  exact Sylow.characteristic_of_subsingleton P

theorem normal_iff_unique_of_card (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) (P : Subgroup G) (hP : Nat.card P = p ^ a) :
    P.Normal ↔ ∀ Q : Subgroup G, Nat.card Q = p ^ a → Q = P := by
  obtain ⟨S, rfl⟩ := (SylowDefinition.sylow_iff_card G p a m hp hcard hm P).mpr hP
  rw [normal_iff_unique G p hp S]
  constructor
  · intro huniq Q hQ
    obtain ⟨T, rfl⟩ := (SylowDefinition.sylow_iff_card G p a m hp hcard hm Q).mpr hQ
    exact congrArg Sylow.toSubgroup (huniq T)
  · intro huniq T
    apply Sylow.ext
    exact huniq T.toSubgroup
      ((SylowDefinition.sylow_iff_card G p a m hp hcard hm T.toSubgroup).mp ⟨T, rfl⟩)

theorem characteristic_of_normal_of_card (G : Type u) [Group G] [Finite G]
    (p a m : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ p ∣ m) (P : Subgroup G) (hP : Nat.card P = p ^ a)
    (hN : P.Normal) : P.Characteristic := by
  obtain ⟨S, rfl⟩ := (SylowDefinition.sylow_iff_card G p a m hp hcard hm P).mpr hP
  exact characteristic_of_normal G p hp S hN

end D07.Ch06.SylowNormalIffUnique
