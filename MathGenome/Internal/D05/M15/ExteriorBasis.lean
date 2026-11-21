import MathGenome.Internal.Specs.D05.M15.ExteriorBasis
import MathGenome.Internal.D05.M15.Exterior
import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.D05.M05.DetUniqueness
import MathGenome.Internal.D05.Foundations.SubsetCount
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! K05.15.exterior_basis: increasing wedge bases of the canonical homogeneous
parts, their determinant coordinates, dimensions, and boundary degrees. -/

noncomputable section
namespace D05.M15.ExteriorBasis

open Specs.D05.M15.ExteriorBasis

/-- Mathlib's subset-indexed family uses the same increasing enumeration. -/
theorem increasingWedge_eq_family {K V I : Type*}
    [Field K] [AddCommGroup V] [Module K V] [LinearOrder I]
    (b : Module.Basis I K V) (p : ℕ) :
    increasingWedge b p = exteriorPower.ιMulti_family K p b := rfl

theorem increasing_wedges_basis : Specs.D05.M15.ExteriorBasis.increasing_wedges_basis := by
  intro K V I _ _ _ _ b p
  exact ⟨b.exteriorPower p, exteriorPower.basis_apply K p b⟩

theorem increasing_wedges_independent :
    Specs.D05.M15.ExteriorBasis.increasing_wedges_independent := by
  intro K V I _ _ _ _ b p
  rw [increasingWedge_eq_family]
  exact exteriorPower.ιMulti_family_linearIndependent_ofBasis K p b

theorem increasing_wedges_span : Specs.D05.M15.ExteriorBasis.increasing_wedges_span := by
  intro K V I _ _ _ _ b p
  rw [increasingWedge_eq_family]
  exact exteriorPower.ιMulti_family_span_of_span K b.span_eq

theorem determinant_coordinates : Specs.D05.M15.ExteriorBasis.determinant_coordinates := by
  intro K V I _ _ _ _ b p s
  classical
  refine ⟨exteriorPower.ιMultiDual K p b s, ?_, ?_⟩
  · intro x
    rw [exteriorPower.ιMultiDual_apply_ιMulti]
    exact Matrix.det_transpose _
  · intro t
    rw [increasingWedge_eq_family]
    by_cases h : s = t
    · subst t
      simpa using exteriorPower.ιMultiDual_apply_diag K p b s
    · rw [ite_eq_right h]
      exact exteriorPower.ιMultiDual_apply_nondiag K p b s t h

theorem dimension_of_finite_basis :
    Specs.D05.M15.ExteriorBasis.dimension_of_finite_basis := by
  intro K V _ _ _ n b p
  classical
  rw [Module.finrank_eq_card_basis (b.exteriorPower p)]
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card]
  simp

theorem dimension : Specs.D05.M15.ExteriorBasis.dimension := by
  intro K V _ _ _ _ p
  exact exteriorPower.finrank_eq K V p

theorem degree_zero_unit_basis : Specs.D05.M15.ExteriorBasis.degree_zero_unit_basis := by
  intro K V _ _ _
  let B := (Pi.basisFun K (Fin 1)).map
    ((LinearEquiv.funUnique (Fin 1) K K).trans (exteriorPower.zeroEquiv K V).symm)
  refine ⟨B, ?_⟩
  simp [B, exteriorPower.zeroEquiv_symm_apply, exteriorPower.ιMulti_apply_coe,
    _root_.ExteriorAlgebra.ιMulti_zero_apply]

theorem above_dimension : Specs.D05.M15.ExteriorBasis.above_dimension := by
  intro K V _ _ _ n b p hp
  have h := exteriorPower.subsingleton_of_span_eq_top_of_card_lt (R := K) b b.span_eq p
    (by simpa using hp)
  exact Submodule.subsingleton_iff_eq_bot.mp h

end D05.M15.ExteriorBasis
