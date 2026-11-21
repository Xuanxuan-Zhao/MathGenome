import MathGenome.Internal.D05.M01.System
import MathGenome.Internal.D05.M03.Kernel
import MathGenome.Internal.Specs.D05.M01.AffineSolutions

/-! K05.01.affine_solutions: all solutions of a finite system form either the
empty set or the translate of its canonical kernel by any particular solution. -/
namespace D05.M01.AffineSolutions

open scoped Matrix
open D05.M01.System

universe u

theorem solution_iff_sub_zero : AffineSolutionsSpec.solution_iff_sub_zero.{u} := by
  intro K _ m n A b x₀ x h₀
  change A *ᵥ x₀ = b at h₀
  change A *ᵥ x = b ↔ A *ᵥ (x - x₀) = 0
  rw [Matrix.mulVec_sub, h₀, sub_eq_zero]

theorem solution_iff_sub_mem_kernel :
    AffineSolutionsSpec.solution_iff_sub_mem_kernel.{u} := by
  intro K _ m n A b x₀ x h₀
  exact solution_iff_sub_zero A b x₀ x h₀

theorem solutions_eq_translate_kernel :
    AffineSolutionsSpec.solutions_eq_translate_kernel.{u} := by
  intro K _ m n A b x₀ h₀
  ext x
  constructor
  · intro hx
    refine ⟨x - x₀, (solution_iff_sub_mem_kernel A b x₀ x h₀).mp hx, ?_⟩
    simpa only [← add_sub_assoc] using add_sub_cancel_left x₀ x
  · rintro ⟨z, hz, rfl⟩
    apply (solution_iff_sub_mem_kernel A b x₀ (x₀ + z) h₀).mpr
    change A *ᵥ z = 0 at hz
    change A *ᵥ (x₀ + z - x₀) = 0
    rwa [add_sub_cancel_left]

theorem solutions_eq_empty_iff : AffineSolutionsSpec.solutions_eq_empty_iff.{u} := by
  intro K _ m n A b
  constructor
  · intro h ⟨x, hx⟩
    have : x ∈ (∅ : Set (Fin n → K)) := by
      rw [← h]
      exact hx
    exact this
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact h ⟨x, hx⟩

theorem homogeneous_solutions_eq_kernel :
    AffineSolutionsSpec.homogeneous_solutions_eq_kernel.{u} := by
  intro K _ m n A
  rfl

theorem zero_mem_solutions_iff : AffineSolutionsSpec.zero_mem_solutions_iff.{u} := by
  intro K _ m n A b
  change A *ᵥ 0 = b ↔ b = 0
  rw [Matrix.mulVec_zero, eq_comm]

theorem solutions_subspace_iff_rhs_zero :
    AffineSolutionsSpec.solutions_subspace_iff_rhs_zero.{u} := by
  intro K _ m n A b
  constructor
  · rintro ⟨S, hS⟩
    apply (zero_mem_solutions_iff A b).mp
    rw [← hS]
    exact S.zero_mem
  · rintro rfl
    exact ⟨D05.M03.Kernel.kernel K (Fin n → K) (Fin m → K) A.mulVecLin,
      (homogeneous_solutions_eq_kernel A).symm⟩

theorem solutions_subspace_iff_contains_zero :
    AffineSolutionsSpec.solutions_subspace_iff_contains_zero.{u} := by
  intro K _ m n A b _
  rw [solutions_subspace_iff_rhs_zero A b, zero_mem_solutions_iff A b]

end D05.M01.AffineSolutions
