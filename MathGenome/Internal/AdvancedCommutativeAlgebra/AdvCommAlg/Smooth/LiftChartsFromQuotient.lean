import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.LocalStandardCover
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.LiftChartsFromQuotient
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Localization.BaseChange

namespace AdvCommAlg.Smooth

universe u v w
noncomputable section
open scoped TensorProduct

/-- Lift a standard smooth algebra across an arbitrary surjection of bases.
The lift is the quotient by lifted equations, localized at its Jacobian. -/
theorem exists_standardSmooth_model_of_surjective
    (A : Type u) (R : Type v) (B : Type w)
    [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra R B]
    (hsurj : Function.Surjective (algebraMap A R))
    (hstd : Algebra.IsStandardSmooth R B) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Algebra.IsStandardSmooth A D ∧ Nonempty (R ⊗[A] D ≃ₐ[R] B) := by
  classical
  letI : Algebra A B := Algebra.compHom B (algebraMap A R)
  let : IsScalarTower A R B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hstd.out
  let := hσ
  let := hι
  letI : Fintype σ := Fintype.ofFinite σ
  let : P.HasCoeffs A := ⟨fun _ _ => hsurj _⟩
  -- Lift all coefficients through the surjection, without assuming it injective.
  let M := P.ModelOfHasCoeffs A
  let Q := P.toPreSubmersivePresentation.ofHasCoeffs A
  let D := Localization.Away Q.jacobian
  have hunit : IsUnit (algebraMap M D Q.jacobian) :=
    IsLocalization.Away.algebraMap_isUnit Q.jacobian
  -- Adjoining the inverse contributes a second Jacobian factor, so the
  -- enlarged presentation has unit Jacobian.
  let Q' : Algebra.SubmersivePresentation A D (Unit ⊕ ι) (Unit ⊕ σ) :=
    { (Algebra.PreSubmersivePresentation.localizationAway D Q.jacobian).comp Q with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
        exact hunit.mul hunit }
  -- Base change recovers the original equations. Its Jacobian was already
  -- a unit, so the extra localization disappears after base change.
  let e := P.tensorModelOfHasCoeffsEquiv A
  have he : e ((1 : R) ⊗ₜ[A] Q.jacobian) = P.jacobian := by
    rw [Q.jacobian_eq_jacobiMatrix_det]
    change e ((1 : R) ⊗ₜ[A] (Ideal.Quotient.mk _ (P.jacobianOfHasCoeffs A))) = _
    simp [e]
  have hu : IsUnit ((1 : R) ⊗ₜ[A] Q.jacobian) := by
    apply (isUnit_map_iff e _).mp
    rw [he]
    exact P.jacobian_isUnit
  let f : R ⊗[A] D ≃ₐ[R] Localization.Away ((1 : R) ⊗ₜ[A] Q.jacobian) :=
    IsLocalization.Away.tensorProductEquivTMulRight A R Q.jacobian D
  let k : R ⊗[A] M ≃ₐ[R] Localization.Away ((1 : R) ⊗ₜ[A] Q.jacobian) :=
    (IsLocalization.atUnit (R ⊗[A] M)
      (Localization.Away ((1 : R) ⊗ₜ[A] Q.jacobian))
      ((1 : R) ⊗ₜ[A] Q.jacobian) hu).restrictScalars R
  exact ⟨D, inferInstance, inferInstance, Q'.isStandardSmooth, ⟨f.trans (k.symm.trans e)⟩⟩

/-- The finite principal cover, together with a standard smooth lift of every chart. -/
theorem exists_finite_lifted_standardSmooth_cover :
    Specs.AdvCommAlg.Smooth.LiftChartsFromQuotient.finiteLiftedStandardCover.{u,v} := by
  intro A _ J C _ _ hs
  obtain ⟨s, hs, hstd⟩ := exists_finite_standardSmooth_cover (A ⧸ J) C hs
  refine ⟨s, hs, ?_⟩
  intro g hg
  exact ⟨hstd g hg,
    exists_standardSmooth_model_of_surjective A (A ⧸ J) (Localization.Away g)
      Ideal.Quotient.mk_surjective (hstd g hg)⟩

end
end AdvCommAlg.Smooth
