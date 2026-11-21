import MathGenome.Internal.Specs.D05.M11.Radicals
import MathGenome.Internal.D05.M03.Kernel
import MathGenome.Internal.D05.M07.Dual
import MathGenome.Internal.D05.M11.FormMatrix
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FinCases

/-! Left and right radicals, their coordinate kernels, and the nonsymmetric
counterexample of K05.11.radicals. No restriction on characteristic is used. -/
namespace D05.M11.Radicals

open Module Matrix
open Specs.D05.M11.Radicals

/-- The left radical is the kernel of the form curried into the algebraic dual. -/
def leftRadical {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : Submodule K V := LinearMap.ker B

/-- The right radical is the corresponding kernel with the slots interchanged. -/
def rightRadical {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : Submodule K V := LinearMap.ker B.flip

theorem mem_leftRadical : Specs.D05.M11.Radicals.mem_leftRadical := by
  intro K V _ _ _ B x
  change B x = 0 ↔ ∀ y, B x y = 0
  exact LinearMap.ext_iff

theorem mem_rightRadical : Specs.D05.M11.Radicals.mem_rightRadical := by
  intro K V _ _ _ B y
  change B.flip y = 0 ↔ ∀ x, B.flip y x = 0
  exact LinearMap.ext_iff

theorem leftRadical_eq_kernel : Specs.D05.M11.Radicals.leftRadical_eq_kernel := by
  intro K V _ _ _ B
  rfl

theorem rightRadical_eq_kernel : Specs.D05.M11.Radicals.rightRadical_eq_kernel := by
  intro K V _ _ _ B
  rfl

theorem right_coordinate_membership : Specs.D05.M11.Radicals.right_coordinate_membership := by
  intro K V _ _ _ n b B x
  rw [mem_rightRadical]
  change (∀ y, B y x = 0) ↔
    Specs.D05.M11.FormMatrix.formMatrix_value b B *ᵥ
      Specs.D05.M04.Coordinates.coordinates_value b x = 0
  constructor
  · intro h
    apply dotProduct_eq_zero
    intro z
    rw [dotProduct_comm]
    have hz := h ((Specs.D05.M04.Coordinates.coordinates_value b).symm z)
    rw [D05.M11.FormMatrix.coordinate_evaluation b B] at hz
    simpa only [LinearEquiv.apply_symm_apply] using hz
  · intro h y
    rw [D05.M11.FormMatrix.coordinate_evaluation b B, h, dotProduct_zero]

theorem left_coordinate_membership : Specs.D05.M11.Radicals.left_coordinate_membership := by
  intro K V _ _ _ n b B x
  rw [mem_leftRadical]
  change (∀ y, B x y = 0) ↔
    (Specs.D05.M11.FormMatrix.formMatrix_value b B)ᵀ *ᵥ
      Specs.D05.M04.Coordinates.coordinates_value b x = 0
  constructor
  · intro h
    apply dotProduct_eq_zero
    intro z
    rw [dotProduct_comm, dotProduct_transpose_mulVec]
    have hz := h ((Specs.D05.M04.Coordinates.coordinates_value b).symm z)
    rw [D05.M11.FormMatrix.coordinate_evaluation b B] at hz
    simpa only [LinearEquiv.apply_symm_apply] using hz
  · intro h y
    rw [D05.M11.FormMatrix.coordinate_evaluation b B, ← dotProduct_transpose_mulVec,
      h, dotProduct_zero]

theorem left_coordinates : Specs.D05.M11.Radicals.left_coordinates := by
  intro K V _ _ _ n b B
  ext z
  rw [Submodule.mem_map_equiv, left_coordinate_membership b B]
  simp only [LinearEquiv.apply_symm_apply]

theorem right_coordinates : Specs.D05.M11.Radicals.right_coordinates := by
  intro K V _ _ _ n b B
  ext z
  rw [Submodule.mem_map_equiv, right_coordinate_membership b B]
  simp only [LinearEquiv.apply_symm_apply]

theorem example_evaluation : Specs.D05.M11.Radicals.example_evaluation := by
  intro K _ x y
  simp [exampleForm, exampleMatrix, Matrix.toBilin'_apply, Fin.sum_univ_two]

private theorem example_left_membership (K : Type*) [Field K] (x : Fin 2 → K) :
    x ∈ leftRadical_value (exampleForm K) ↔ x 0 = 0 := by
  rw [mem_leftRadical]
  constructor
  · intro h
    have hz := h (Pi.single (1 : Fin 2) (1 : K))
    rw [example_evaluation K] at hz
    simpa using hz
  · intro h y
    rw [example_evaluation, h, zero_mul]

private theorem example_right_membership (K : Type*) [Field K] (x : Fin 2 → K) :
    x ∈ rightRadical_value (exampleForm K) ↔ x 1 = 0 := by
  rw [mem_rightRadical]
  constructor
  · intro h
    have hz := h (Pi.single (0 : Fin 2) (1 : K))
    rw [example_evaluation K] at hz
    simpa using hz
  · intro h y
    rw [example_evaluation, h, mul_zero]

theorem example_left_radical : Specs.D05.M11.Radicals.example_left_radical := by
  intro K _
  constructor
  · ext x
    exact example_left_membership K x
  · ext x
    rw [example_left_membership, Submodule.mem_span_singleton]
    constructor
    · intro hx
      refine ⟨x 1, ?_⟩
      funext i
      fin_cases i <;> simp [hx]
    · rintro ⟨a, rfl⟩
      simp

theorem example_right_radical : Specs.D05.M11.Radicals.example_right_radical := by
  intro K _
  constructor
  · ext x
    exact example_right_membership K x
  · ext x
    rw [example_right_membership, Submodule.mem_span_singleton]
    constructor
    · intro hx
      refine ⟨x 0, ?_⟩
      funext i
      fin_cases i <;> simp [hx]
    · rintro ⟨a, rfl⟩
      simp

theorem example_radicals_ne : Specs.D05.M11.Radicals.example_radicals_ne := by
  intro K _ heq
  have h : Pi.single (1 : Fin 2) (1 : K) ∈ leftRadical_value (exampleForm K) :=
    (example_left_membership K _).mpr (by simp)
  rw [heq] at h
  have hzero := (example_right_membership K _).mp h
  simp at hzero

theorem radicals_eq_of_symmetric : Specs.D05.M11.Radicals.radicals_eq_of_symmetric := by
  intro K V _ _ _ B hB
  ext x
  rw [mem_leftRadical, mem_rightRadical]
  simp only [hB.eq x]

theorem radicals_eq_of_alternating : Specs.D05.M11.Radicals.radicals_eq_of_alternating := by
  intro K V _ _ _ B hB
  ext x
  rw [mem_leftRadical, mem_rightRadical]
  constructor
  · intro h y
    rw [← hB.neg_eq x y, h y, neg_zero]
  · intro h y
    rw [← hB.neg_eq y x, h y, neg_zero]

end D05.M11.Radicals
