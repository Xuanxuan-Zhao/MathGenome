import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.LiftFromQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.SquareJacobianCriterion
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Localization.BaseChange

/-! ET-19: lifting an étale algebra through an arbitrary quotient of its base.
Lift a square presentation and invert its Jacobian. Base change recovers the
original presentation, where that Jacobian was already invertible. -/
namespace AdvCommAlg.Etale

universe u v
noncomputable section

open TensorProduct

/-- Inverting the Jacobian of a square presentation makes it étale. -/
theorem etale_localization_jacobian {A Q : Type*} [CommRing A] [CommRing Q]
    [Algebra A Q] {n : ℕ}
    (P : Algebra.PreSubmersivePresentation A Q (Fin n) (Fin n)) :
    Algebra.Etale A (Localization.Away P.jacobian) := by
  let B := Localization.Away P.jacobian
  let L := Algebra.PreSubmersivePresentation.localizationAway B P.jacobian
  let T : Algebra.SubmersivePresentation A B (Unit ⊕ Fin n) (Unit ⊕ Fin n) :=
    { L.comp P with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
          (IsLocalization.Away.algebraMap_isUnit P.jacobian) }
  exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    (T.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension]))

/-- Every étale algebra over an arbitrary quotient of the base is the base
change of an étale algebra over the base. -/
theorem lift_from_quotient : Specs.AdvCommAlg.Etale.liftFromQuotient.{u,v} := by
  intro A _ I Bbar _ _ het
  let : Algebra A Bbar := ((algebraMap (A ⧸ I) Bbar).comp (Ideal.Quotient.mk I)).toAlgebra
  let : IsScalarTower A (A ⧸ I) Bbar := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨n, P, hP⟩ := (etale_iff_square_presentation (A ⧸ I) Bbar).mp het
  let S : Algebra.SubmersivePresentation (A ⧸ I) Bbar (Fin n) (Fin n) :=
    { toPresentation := P
      map := id
      map_inj := Function.injective_id
      jacobian_isUnit := by
        rw [jacobian_eq_full_determinant _ rfl]
        exact hP }
  let : Algebra.SubmersivePresentation.HasCoeffs S A := ⟨by
    intro x _
    exact Ideal.Quotient.mk_surjective x⟩
  let : Algebra.Presentation.HasCoeffs S.toPresentation A := ⟨by
    intro x _
    exact Ideal.Quotient.mk_surjective x⟩
  let Q := S.toPresentation.ModelOfHasCoeffs A
  let P₀ := S.toPreSubmersivePresentation.ofHasCoeffs A
  let δ : Q := P₀.jacobian
  let B := Localization.Away δ
  let e : (A ⧸ I) ⊗[A] Q ≃ₐ[A ⧸ I] Bbar := S.toPresentation.tensorModelOfHasCoeffsEquiv A
  have heδ : e ((1 : A ⧸ I) ⊗ₜ[A] δ) = S.jacobian := by
    classical
    let : Fintype (Fin n) := Fintype.ofFinite _
    let : DecidableEq (Fin n) := Classical.decEq _
    change e (1 ⊗ₜ[A] P₀.jacobian) = _
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det P₀]
    simp only [P₀, Algebra.PreSubmersivePresentation.ofHasCoeffs_algebra_algebraMap_apply]
    change e (1 ⊗ₜ[A] (Ideal.Quotient.mk _ (S.jacobianOfHasCoeffs A))) = _
    change algebraMap (A ⧸ I) Bbar 1 *
      MvPolynomial.aeval S.val (S.jacobianOfHasCoeffs A) = S.jacobian
    rw [map_one, one_mul, S.aeval_jacobianOfHasCoeffs A]
  have hδ : IsUnit ((1 : A ⧸ I) ⊗ₜ[A] δ) := by
    apply (isUnit_map_iff e _).mp
    rw [heδ]
    exact S.jacobian_isUnit
  let e₁ := IsLocalization.Away.tensorProductEquivTMulRight A (A ⧸ I) δ B
  let e₂ := (IsLocalization.atUnit _ ((1 : A ⧸ I) ⊗ₜ[A] δ) hδ
    (S := Localization.Away ((1 : A ⧸ I) ⊗ₜ[A] δ))).symm.restrictScalars (A ⧸ I)
  exact ⟨B, inferInstance, inferInstance, etale_localization_jacobian P₀,
    ⟨e₁.trans (e₂.trans e)⟩⟩

end
end AdvCommAlg.Etale
