import MathGenome.Internal.D07.Ch01.KernelImage
import MathGenome.Internal.D07.Ch03.CosetBijections
import MathGenome.Internal.Specs.D07.Ch03.HomFiberCounting
import Mathlib.GroupTheory.Index

/-!
# Fibres and kernel counting

K07.03.hom_fiber_counting, paper.tex:619–626. For a point `a` over `h`,
`f x = h` is equivalent to `a⁻¹ * x ∈ ker f` and to `x * a⁻¹ ∈ ker f`.
The shared coset descriptions then identify the whole fibre as a subset.
The finite counting formulas use Mathlib's kernel–range counting theorem,
with the finite-domain hypothesis kept explicitly in the public statements.
-/

namespace D07.Ch03.HomFiberCounting

open Specs.D07.Ch03.CosetsPartition

universe u v

theorem fiber_eq_cosets (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) (h : H) (a : G) (ha : f a = h) :
    {x : G | f x = h} = leftCoset f.ker a ∧
    {x : G | f x = h} = rightCoset f.ker a := by
  constructor
  · rw [← CosetsPartition.left_class_eq_coset G f.ker a]
    ext x
    change f x = h ↔ f (a⁻¹ * x) = 1
    rw [map_mul, map_inv, inv_mul_eq_one, ha, eq_comm]
  · rw [← CosetsPartition.right_class_eq_coset G f.ker a]
    ext x
    change f x = h ↔ f (x * a⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one, ha]

theorem nonempty_fiber_is_coset (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) (h : H) (hne : ({x : G | f x = h} : Set G).Nonempty) :
    ∃ a : G, f a = h ∧
      {x : G | f x = h} = leftCoset f.ker a ∧
      {x : G | f x = h} = rightCoset f.ker a := by
  obtain ⟨a, ha⟩ := hne
  exact ⟨a, ha, fiber_eq_cosets G H f h a ha⟩

theorem fiber_bijection (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) (h : H) (a : G) (ha : f a = h) :
    ∃ e : f.ker ≃ ↥({x : G | f x = h} : Set G),
      (∀ k : f.ker, (e k : G) = a * (k : G)) ∧
      (∀ x : ↥({x : G | f x = h} : Set G),
        (e.symm x : G) = a⁻¹ * (x : G)) := by
  let e : f.ker ≃ ↥({x : G | f x = h} : Set G) := {
    toFun := fun k => ⟨a * (k : G), by
      change f (a * (k : G)) = h
      rw [map_mul, MonoidHom.mem_ker.mp k.property, mul_one, ha]⟩
    invFun := fun x => ⟨a⁻¹ * (x : G), by
      change f (a⁻¹ * (x : G)) = 1
      rw [map_mul, map_inv, ha, x.property, inv_mul_cancel]⟩
    left_inv := fun k => Subtype.ext (inv_mul_cancel_left a (k : G))
    right_inv := fun x => Subtype.ext (mul_inv_cancel_left a (x : G))
  }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

theorem card_domain (G : Type u) (H : Type v) [Group G] [Group H] [Finite G]
    (f : G →* H) : Nat.card G = Nat.card f.ker * Nat.card f.range :=
  (Subgroup.card_ker_mul_card_range f).symm

theorem card_domain_of_surjective (G : Type u) (H : Type v)
    [Group G] [Group H] [Finite G] (f : G →* H) (hf : Function.Surjective f) :
    Nat.card G = Nat.card f.ker * Nat.card H :=
  (Subgroup.card_ker_mul_card_of_surjective hf).symm

end D07.Ch03.HomFiberCounting
