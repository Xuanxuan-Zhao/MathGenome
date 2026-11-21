import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.StandardPresentation
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.InvertibleMinor
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! The invertible-minor criterion, with bases for the specified classes and
differentials, over arbitrary commutative rings (SM-04). -/
namespace AdvCommAlg.Smooth

universe u v
noncomputable section
open Specs.AdvCommAlg.Smooth
open Specs.AdvCommAlg.Smooth.InvertibleMinor

/-- The standard smooth witness retains the original presentation. -/
theorem presentation_smooth : presentationSmooth.{u,v} := by
  intro A B _ _ _ n c P hP
  obtain ⟨Q, _⟩ := (presentation_standard_smooth_iff_submersive P).mp hP
  let := Q.isStandardSmooth
  exact (inferInstance : Algebra.Smooth A B)

/-- The library basis is on the relation classes themselves. -/
theorem relation_basis : relationBasis.{u,v} := by
  intro A B _ _ _ n c P hP
  obtain ⟨Q, hQ⟩ := (presentation_standard_smooth_iff_submersive P).mp hP
  subst P
  exact ⟨Q.basisCotangent, Q.basisCotangent_apply⟩

/-- The last n-c indices complement the initial c indices, including the
cases in which either part is empty. -/
theorem trailingVariable_isCompl {n c : ℕ} (h : c ≤ n) :
    IsCompl (Set.range (trailingVariable h)) (Set.range (Fin.castLE h)) := by
  have hr : Set.range (trailingVariable h) = (Set.range (Fin.castLE h))ᶜ := by
    ext i
    simp only [Set.mem_range, Set.mem_compl_iff]
    constructor
    · rintro ⟨j, rfl⟩ ⟨k, hk⟩
      have hv := congrArg Fin.val hk
      dsimp [trailingVariable] at hv
      omega
    · intro hi
      have hc : c ≤ i.val := by
        by_contra hci
        exact hi ⟨⟨i.val, by omega⟩, by apply Fin.ext; rfl⟩
      exact ⟨⟨i.val - c, by omega⟩, by apply Fin.ext; dsimp [trailingVariable]; omega⟩
  rw [hr]
  exact IsCompl.symm isCompl_compl

/-- Projecting along the invertible block gives a basis on exactly the
remaining variable differentials, in their original order. -/
theorem ordered_differential_basis : orderedDifferentialBasis.{u,v} := by
  intro A B _ _ _ n c P h hu
  let Q₀ : Algebra.PreSubmersivePresentation A B (Fin n) (Fin c) :=
    { P with map := Fin.castLE h, map_inj := Fin.castLE_injective h }
  have hj : IsUnit Q₀.jacobian := by
    rw [selected_minor_jacobian Q₀]
    exact hu
  let Q : Algebra.SubmersivePresentation A B (Fin n) (Fin c) :=
    { Q₀ with jacobian_isUnit := hj }
  have hi : Function.Injective (trailingVariable h) := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp [trailingVariable] at hv
    omega
  exact ⟨Q.basisKaehlerOfIsCompl hi (trailingVariable_isCompl h),
    Q.basisKaehlerOfIsCompl_apply hi (trailingVariable_isCompl h)⟩

end
end AdvCommAlg.Smooth
