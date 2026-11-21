import MathGenome.Internal.D07.Ch01.ElementaryGroupLaws
import MathGenome.Internal.Specs.D07.Ch01.SubgroupDefinitionTest

/-!
# Subgroups and useful tests

Formalization of `K07.01.subgroup_definition_test`. Subgroup carriers are
identified with subsets by equality of sets. The two reverse implications
recover the ambient identity, inverse closure, and product closure in the
order used in the source proof.
-/

namespace D07.Ch01.SubgroupDefinitionTest

universe u

theorem subgroup_iff_closed (G : Type u) [Group G] (s : Set G) :
    (∃ H : Subgroup G, (H : Set G) = s) ↔
      (1 : G) ∈ s ∧
      (∀ x ∈ s, ∀ y ∈ s, x * y ∈ s) ∧
      (∀ x ∈ s, x⁻¹ ∈ s) := by
  constructor
  · rintro ⟨H, rfl⟩
    exact ⟨H.one_mem, fun _ hx _ hy => H.mul_mem hx hy,
      fun _ hx => H.inv_mem hx⟩
  · rintro ⟨h1, hmul, hinv⟩
    exact ⟨{ carrier := s
             one_mem' := h1
             mul_mem' := fun hx hy => hmul _ hx _ hy
             inv_mem' := fun hx => hinv _ hx }, rfl⟩

theorem inherited_group_operations (G : Type u) [Group G] (H : Subgroup G) :
    GroupDefinition.groupAxioms H (· * ·) 1 Inv.inv ∧
      ((1 : H) : G) = 1 ∧
      (∀ x y : H, ((x * y : H) : G) = (x : G) * (y : G)) ∧
      (∀ x : H, ((x⁻¹ : H) : G) = (x : G)⁻¹) :=
  ⟨GroupDefinition.group_laws H, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem subgroup_iff_mul_inv_mem (G : Type u) [Group G] (s : Set G) :
    (∃ H : Subgroup G, (H : Set G) = s) ↔
      s.Nonempty ∧ (∀ x ∈ s, ∀ y ∈ s, x * y⁻¹ ∈ s) := by
  constructor
  · rintro ⟨H, rfl⟩
    exact ⟨⟨1, H.one_mem⟩, fun _ hx _ hy => H.mul_mem hx (H.inv_mem hy)⟩
  · rintro ⟨⟨a, ha⟩, h⟩
    have h1 : (1 : G) ∈ s := by
      simpa only [mul_inv_cancel] using h a ha a ha
    have hinv : ∀ y ∈ s, y⁻¹ ∈ s := by
      intro y hy
      simpa only [one_mul] using h 1 h1 y hy
    apply (subgroup_iff_closed G s).2
    refine ⟨h1, ?_, hinv⟩
    intro x hx y hy
    simpa only [inv_inv] using h x hx y⁻¹ (hinv y hy)

theorem subgroup_iff_inv_mul_mem (G : Type u) [Group G] (s : Set G) :
    (∃ H : Subgroup G, (H : Set G) = s) ↔
      s.Nonempty ∧ (∀ x ∈ s, ∀ y ∈ s, x⁻¹ * y ∈ s) := by
  constructor
  · rintro ⟨H, rfl⟩
    exact ⟨⟨1, H.one_mem⟩, fun _ hx _ hy => H.mul_mem (H.inv_mem hx) hy⟩
  · rintro ⟨⟨a, ha⟩, h⟩
    have h1 : (1 : G) ∈ s := by
      simpa only [inv_mul_cancel] using h a ha a ha
    have hinv : ∀ x ∈ s, x⁻¹ ∈ s := by
      intro x hx
      simpa only [mul_one] using h x hx 1 h1
    apply (subgroup_iff_closed G s).2
    refine ⟨h1, ?_, hinv⟩
    intro x hx y hy
    simpa only [inv_inv] using h x⁻¹ (hinv x hx) y hy

end D07.Ch01.SubgroupDefinitionTest
