import MathGenome.Internal.D07.Ch01.SubgroupDefinitionTest
import MathGenome.Internal.Specs.D07.Ch01.SubgroupLattice

/-!
# Intersections and generated subgroups

Formalization of `K07.01.subgroup_lattice`. The canonical subgroup closure
is literally the infimum of all subgroups containing the generating set.
The union criterion uses cancellation in an arbitrary, possibly nonabelian,
group, as in the source proof.
-/

namespace D07.Ch01.SubgroupLattice

universe u

theorem intersection_is_subgroup (G : Type u) [Group G] (A : Set (Subgroup G)) :
    ∃ L : Subgroup G, (L : Set G) = ⋂ H ∈ A, (H : Set G) :=
  ⟨sInf A, Subgroup.coe_sInf A⟩

theorem empty_intersection (G : Type u) [Group G] :
    (⋂ H ∈ (∅ : Set (Subgroup G)), (H : Set G)) = Set.univ := by
  simp

theorem generated_eq_intersection (G : Type u) [Group G] (S : Set G) :
    (Subgroup.closure S : Set G) =
      ⋂ H ∈ {H : Subgroup G | S ⊆ (H : Set G)}, (H : Set G) :=
  rfl

theorem subset_generated (G : Type u) [Group G] (S : Set G) :
    S ⊆ Subgroup.closure S :=
  Subgroup.subset_closure

theorem generated_le_iff (G : Type u) [Group G] (S : Set G) (H : Subgroup G) :
    Subgroup.closure S ≤ H ↔ S ⊆ (H : Set G) :=
  Subgroup.closure_le H

theorem generated_empty (G : Type u) [Group G] :
    (Subgroup.closure (∅ : Set G) : Set G) = {(1 : G)} := by
  rw [Subgroup.closure_empty, Subgroup.coe_bot]

theorem join_eq_generated (G : Type u) [Group G] (H K : Subgroup G) :
    H ⊔ K = Subgroup.closure ((H : Set G) ∪ (K : Set G)) :=
  Subgroup.sup_eq_closure H K

theorem join_le_iff (G : Type u) [Group G] (H K L : Subgroup G) :
    Subgroup.closure ((H : Set G) ∪ (K : Set G)) ≤ L ↔ H ≤ L ∧ K ≤ L := by
  rw [← join_eq_generated G H K]
  exact sup_le_iff

/-- For elements in opposite set differences, their product lies in neither subgroup. -/
theorem product_not_mem_union (G : Type u) [Group G] (H K : Subgroup G)
    (h k : G) (hh : h ∈ H) (hhK : h ∉ K) (hk : k ∈ K) (hkH : k ∉ H) :
    h * k ∉ (H : Set G) ∪ (K : Set G) := by
  intro hp
  rcases hp with hpH | hpK
  · apply hkH
    simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem hh) hpH
  · apply hhK
    simpa only [mul_inv_cancel_right] using K.mul_mem hpK (K.inv_mem hk)

theorem union_is_subgroup_iff (G : Type u) [Group G] (H K : Subgroup G) :
    (∃ L : Subgroup G, (L : Set G) = (H : Set G) ∪ (K : Set G)) ↔
      H ≤ K ∨ K ≤ H := by
  classical
  constructor
  · rintro ⟨L, hL⟩
    by_cases hHK : H ≤ K
    · exact Or.inl hHK
    by_cases hKH : K ≤ H
    · exact Or.inr hKH
    obtain ⟨h, hh, hhK⟩ := Set.not_subset.mp hHK
    obtain ⟨k, hk, hkH⟩ := Set.not_subset.mp hKH
    have hhL : h ∈ L := by
      change h ∈ (L : Set G)
      rw [hL]
      exact Or.inl hh
    have hkL : k ∈ L := by
      change k ∈ (L : Set G)
      rw [hL]
      exact Or.inr hk
    have hp : h * k ∈ (H : Set G) ∪ (K : Set G) := by
      rw [← hL]
      exact L.mul_mem hhL hkL
    exact False.elim (product_not_mem_union G H K h k hh hhK hk hkH hp)
  · rintro (hHK | hKH)
    · exact ⟨K, (Set.union_eq_right.mpr hHK).symm⟩
    · exact ⟨H, (Set.union_eq_left.mpr hKH).symm⟩

theorem incomparable_union_not_subgroup (G : Type u) [Group G] (H K : Subgroup G)
    (hHK : ¬ H ≤ K) (hKH : ¬ K ≤ H) :
    ¬ ∃ L : Subgroup G, (L : Set G) = (H : Set G) ∪ (K : Set G) := by
  intro h
  exact ((union_is_subgroup_iff G H K).mp h).elim hHK hKH

end D07.Ch01.SubgroupLattice
