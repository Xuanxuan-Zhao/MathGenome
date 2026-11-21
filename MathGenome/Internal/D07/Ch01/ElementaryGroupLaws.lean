import MathGenome.Internal.D07.Ch01.GroupDefinition
import MathGenome.Internal.Specs.D07.Ch01.ElementaryGroupLaws
import Mathlib.Algebra.Group.Basic

/-!
# Cancellation and inverses

The elementary laws of `K07.01.elementary_group_laws` for an arbitrary group,
with the same canonical structure as `GroupDefinition.GroupStructure`.
-/

namespace D07.Ch01.ElementaryGroupLaws

universe u

theorem identity_unique (G : Type u) [Group G] :
    ∃! e : G, (∀ x : G, e * x = x) ∧ (∀ x : G, x * e = x) := by
  refine ⟨1, ⟨one_mul, mul_one⟩, ?_⟩
  intro e he
  exact (mul_one e).symm.trans (he.1 1)

theorem inverse_unique (G : Type u) [Group G] (x : G) :
    ∃! y : G, x * y = 1 ∧ y * x = 1 := by
  refine ⟨x⁻¹, ⟨mul_inv_cancel x, inv_mul_cancel x⟩, ?_⟩
  intro y hy
  exact eq_inv_of_mul_eq_one_right hy.1

theorem left_multiplication_bijective (G : Type u) [Group G] (a : G) :
    Function.Bijective (fun x : G => a * x) :=
  ⟨fun _ _ h => mul_left_cancel h, mul_left_surjective a⟩

theorem right_multiplication_bijective (G : Type u) [Group G] (a : G) :
    Function.Bijective (fun x : G => x * a) :=
  ⟨fun _ _ h => mul_right_cancel h, mul_right_surjective a⟩

theorem left_cancellation (G : Type u) [Group G] (a x y : G)
    (h : a * x = a * y) : x = y :=
  mul_left_cancel h

theorem right_cancellation (G : Type u) [Group G] (a x y : G)
    (h : x * a = y * a) : x = y :=
  mul_right_cancel h

theorem product_inverse (G : Type u) [Group G] (x y : G) :
    (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  mul_inv_rev x y

theorem inverse_inverse (G : Type u) [Group G] (x : G) : (x⁻¹)⁻¹ = x :=
  inv_inv x

end D07.Ch01.ElementaryGroupLaws
