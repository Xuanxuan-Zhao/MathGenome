import MathGenome.Internal.D07.Ch03.CosetsPartition
import MathGenome.Internal.Specs.D07.Ch03.CosetBijections

/-!
# Bijections of cosets and coset spaces

K07.03.coset_bijections, paper.tex:583–590. Multiplication and cancellation
give the individual coset equivalences. Inversion of subsets interchanges
left and right cosets and is involutive, giving an equivalence of their
spaces without choosing representatives or giving them group operations.
-/

namespace D07.Ch03.CosetBijections

open Specs.D07.Ch03.CosetsPartition

universe u

theorem left_coset_bijection (G : Type u) [Group G] (H : Subgroup G) (g : G) :
    ∃ e : H ≃ ↥(leftCoset H g),
      (∀ h : H, (e h : G) = g * (h : G)) ∧
      (∀ x : ↥(leftCoset H g), (e.symm x : G) = g⁻¹ * (x : G)) := by
  let e : H ≃ ↥(leftCoset H g) := {
    toFun := fun h => ⟨g * (h : G), ⟨h, h.property, rfl⟩⟩
    invFun := fun x => ⟨g⁻¹ * (x : G), by
      exact (Set.ext_iff.mp
        (CosetsPartition.left_class_eq_coset G H g) (x : G)).mpr x.property⟩
    left_inv := fun h => Subtype.ext (inv_mul_cancel_left g (h : G))
    right_inv := fun x => Subtype.ext (mul_inv_cancel_left g (x : G))
  }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

theorem right_coset_bijection (G : Type u) [Group G] (H : Subgroup G) (g : G) :
    ∃ e : H ≃ ↥(rightCoset H g),
      (∀ h : H, (e h : G) = (h : G) * g) ∧
      (∀ x : ↥(rightCoset H g), (e.symm x : G) = (x : G) * g⁻¹) := by
  let e : H ≃ ↥(rightCoset H g) := {
    toFun := fun h => ⟨(h : G) * g, ⟨h, h.property, rfl⟩⟩
    invFun := fun x => ⟨(x : G) * g⁻¹, by
      exact (Set.ext_iff.mp
        (CosetsPartition.right_class_eq_coset G H g) (x : G)).mpr x.property⟩
    left_inv := fun h => Subtype.ext (mul_inv_cancel_right (h : G) g)
    right_inv := fun x => Subtype.ext (inv_mul_cancel_right (x : G) g)
  }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

/-- Inversion of a left coset is the right coset with inverse representative. -/
theorem inv_image_left_coset (G : Type u) [Group G] (H : Subgroup G) (g : G) :
    Inv.inv '' leftCoset H g = rightCoset H g⁻¹ := by
  ext x
  constructor
  · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h⁻¹, H.inv_mem hh, (mul_inv_rev g h).symm⟩
  · rintro ⟨h, hh, rfl⟩
    refine ⟨g * h⁻¹, ⟨h⁻¹, H.inv_mem hh, rfl⟩, ?_⟩
    simp only [mul_inv_rev, inv_inv]

/-- Inversion of a right coset is the left coset with inverse representative. -/
theorem inv_image_right_coset (G : Type u) [Group G] (H : Subgroup G) (g : G) :
    Inv.inv '' rightCoset H g = leftCoset H g⁻¹ := by
  ext x
  constructor
  · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h⁻¹, H.inv_mem hh, (mul_inv_rev h g).symm⟩
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h⁻¹ * g, ⟨h⁻¹, H.inv_mem hh, rfl⟩, ?_⟩
    simp only [mul_inv_rev, inv_inv]

theorem coset_spaces_bijection (G : Type u) [Group G] (H : Subgroup G) :
    ∃ e : ↥(Set.range (leftCoset H)) ≃ ↥(Set.range (rightCoset H)),
      (∀ C, (e C : Set G) = Inv.inv '' (C : Set G)) ∧
      (∀ D, (e.symm D : Set G) = Inv.inv '' (D : Set G)) := by
  let e : ↥(Set.range (leftCoset H)) ≃ ↥(Set.range (rightCoset H)) := {
    toFun := fun C => ⟨Inv.inv '' (C : Set G), by
      obtain ⟨g, hg⟩ := C.property
      exact ⟨g⁻¹, by rw [← hg, inv_image_left_coset]⟩⟩
    invFun := fun D => ⟨Inv.inv '' (D : Set G), by
      obtain ⟨g, hg⟩ := D.property
      exact ⟨g⁻¹, by rw [← hg, inv_image_right_coset]⟩⟩
    left_inv := fun C => Subtype.ext (by
      simp only [Set.image_image, inv_inv, Set.image_id'])
    right_inv := fun D => Subtype.ext (by
      simp only [Set.image_image, inv_inv, Set.image_id'])
  }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

end D07.Ch03.CosetBijections
