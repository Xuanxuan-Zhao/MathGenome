import MathGenome.Internal.Specs.D07.Ch18.MaximalSubgroups

/-!
Maximal proper subgroups and nilpotence (K07.18.maximal_subgroups).

The finite nilpotence equivalences in Mathlib include exactly the
maximal-normal criterion, with no nontriviality hypothesis. For the
prime-power clause, the cardinality hypothesis gives `IsPGroup` and
hence nilpotence. Maximality then gives normality, and Mathlib's
index theorem for nilpotent p-groups gives index p.
-/

namespace D07.Ch18.MaximalSubgroups

universe u

theorem nilpotent_iff_maximal_normal (G : Type u) [Group G] [Finite G] :
    Group.IsNilpotent G ↔ ∀ M : Subgroup G, IsCoatom M → M.Normal := by
  exact Group.isNilpotent_of_finite_tfae.out 1 3

theorem pgroup_maximal_normal_index (G : Type u) [Group G] [Finite G]
    [Nontrivial G] (p a : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ a)
    (M : Subgroup G) (hM : IsCoatom M) : M.Normal ∧ M.index = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hG : IsPGroup p G := IsPGroup.of_card hcard
  let : Group.IsNilpotent G := hG.isNilpotent
  exact ⟨(nilpotent_iff_maximal_normal G).mp inferInstance M hM,
    hG.isCoatom_iff_index_eq_prime.mp hM⟩

end D07.Ch18.MaximalSubgroups
