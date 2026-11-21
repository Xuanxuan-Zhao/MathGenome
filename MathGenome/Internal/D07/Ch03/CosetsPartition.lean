import MathGenome.Internal.D07.Ch01.SubgroupDefinitionTest
import MathGenome.Internal.Specs.D07.Ch03.CosetsPartition

/-!
# Left and right cosets partition a group

K07.03.cosets_partition, paper.tex:574–581. The operations and subgroups
are the canonical ones used in the upstream group and subgroup results.
We use the shared set-valued coset definitions from the independent Specs.
The proof follows the source: subgroup closure proves the relation laws,
solving for the subgroup element identifies each class, and a common member
forces equality of classes. No quotient-group structure is used.
-/

namespace D07.Ch03.CosetsPartition

open Specs.D07.Ch03.CosetsPartition

universe u

theorem left_relation_equivalence (G : Type u) [Group G] (H : Subgroup G) :
    Equivalence (fun x y : G => x⁻¹ * y ∈ H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simpa only [inv_mul_cancel] using H.one_mem
  · intro x y hxy
    simpa only [mul_inv_rev, inv_inv] using H.inv_mem hxy
  · intro x y z hxy hyz
    simpa only [mul_assoc, mul_inv_cancel_left] using H.mul_mem hxy hyz

theorem right_relation_equivalence (G : Type u) [Group G] (H : Subgroup G) :
    Equivalence (fun x y : G => y * x⁻¹ ∈ H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simpa only [mul_inv_cancel] using H.one_mem
  · intro x y hxy
    simpa only [mul_inv_rev, inv_inv] using H.inv_mem hxy
  · intro x y z hxy hyz
    simpa only [mul_assoc, inv_mul_cancel_left] using H.mul_mem hyz hxy

theorem left_class_eq_coset (G : Type u) [Group G] (H : Subgroup G) (x : G) :
    {y : G | x⁻¹ * y ∈ H} = leftCoset H x := by
  ext y
  constructor
  · intro hy
    exact ⟨x⁻¹ * y, hy, by simp⟩
  · rintro ⟨h, hh, rfl⟩
    simpa only [Set.mem_ofPred_eq, SetLike.mem_coe, inv_mul_cancel_left] using hh

theorem right_class_eq_coset (G : Type u) [Group G] (H : Subgroup G) (x : G) :
    {y : G | y * x⁻¹ ∈ H} = rightCoset H x := by
  ext y
  constructor
  · intro hy
    exact ⟨y * x⁻¹, hy, by simp⟩
  · rintro ⟨h, hh, rfl⟩
    simpa only [Set.mem_ofPred_eq, SetLike.mem_coe, mul_inv_cancel_right] using hh

/-- Two classes of any equivalence relation with a common member coincide. -/
private theorem classes_eq_of_common {α : Type*} {r : α → α → Prop}
    (hr : Equivalence r) {x y z : α} (hx : r x z) (hy : r y z) :
    {w | r x w} = {w | r y w} := by
  ext w
  exact ⟨fun hw => hr.trans (hr.trans hy (hr.symm hx)) hw,
    fun hw => hr.trans (hr.trans hx (hr.symm hy)) hw⟩

theorem left_cosets_eq_or_disjoint (G : Type u) [Group G] (H : Subgroup G) (x y : G) :
    leftCoset H x = leftCoset H y ∨ Disjoint (leftCoset H x) (leftCoset H y) := by
  classical
  by_cases h : ∃ z, z ∈ leftCoset H x ∧ z ∈ leftCoset H y
  · obtain ⟨z, hx, hy⟩ := h
    left
    rw [← left_class_eq_coset G H x] at hx ⊢
    rw [← left_class_eq_coset G H y] at hy ⊢
    exact classes_eq_of_common (left_relation_equivalence G H) hx hy
  · right
    exact Set.disjoint_left.mpr (fun z hx hy => h ⟨z, hx, hy⟩)

theorem right_cosets_eq_or_disjoint (G : Type u) [Group G] (H : Subgroup G) (x y : G) :
    rightCoset H x = rightCoset H y ∨ Disjoint (rightCoset H x) (rightCoset H y) := by
  classical
  by_cases h : ∃ z, z ∈ rightCoset H x ∧ z ∈ rightCoset H y
  · obtain ⟨z, hx, hy⟩ := h
    left
    rw [← right_class_eq_coset G H x] at hx ⊢
    rw [← right_class_eq_coset G H y] at hy ⊢
    exact classes_eq_of_common (right_relation_equivalence G H) hx hy
  · right
    exact Set.disjoint_left.mpr (fun z hx hy => h ⟨z, hx, hy⟩)

theorem left_cosets_partition (G : Type u) [Group G] (H : Subgroup G) :
    (∀ x : G, (leftCoset H x).Nonempty) ∧
    (⋃ x : G, leftCoset H x) = Set.univ ∧
    ∀ z : G, ∃! C : Set G, C ∈ Set.range (leftCoset H) ∧ z ∈ C := by
  have self_mem (x : G) : x ∈ leftCoset H x :=
    ⟨1, H.one_mem, mul_one x⟩
  refine ⟨fun x => ⟨x, self_mem x⟩, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, self_mem x⟩
  · intro z
    refine ⟨leftCoset H z, ⟨⟨z, rfl⟩, self_mem z⟩, ?_⟩
    rintro C ⟨⟨x, rfl⟩, hx⟩
    rcases left_cosets_eq_or_disjoint G H x z with heq | hd
    · exact heq
    · exact False.elim (Set.disjoint_left.mp hd hx (self_mem z))

theorem right_cosets_partition (G : Type u) [Group G] (H : Subgroup G) :
    (∀ x : G, (rightCoset H x).Nonempty) ∧
    (⋃ x : G, rightCoset H x) = Set.univ ∧
    ∀ z : G, ∃! C : Set G, C ∈ Set.range (rightCoset H) ∧ z ∈ C := by
  have self_mem (x : G) : x ∈ rightCoset H x :=
    ⟨1, H.one_mem, one_mul x⟩
  refine ⟨fun x => ⟨x, self_mem x⟩, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, self_mem x⟩
  · intro z
    refine ⟨rightCoset H z, ⟨⟨z, rfl⟩, self_mem z⟩, ?_⟩
    rintro C ⟨⟨x, rfl⟩, hx⟩
    rcases right_cosets_eq_or_disjoint G H x z with heq | hd
    · exact heq
    · exact False.elim (Set.disjoint_left.mp hd hx (self_mem z))

end D07.Ch03.CosetsPartition
