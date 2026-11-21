import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.StandardPresentation
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.ElementaryStandardExamples

namespace AdvCommAlg.Smooth.Elementary

universe u
noncomputable section
open MvPolynomial Specs.AdvCommAlg.Smooth
open Specs.AdvCommAlg.Smooth.Elementary

theorem polynomial_example : polynomialExample.{u} := by
  intro A _ n
  refine ⟨AdvCommAlg.Smooth.empty_presentation _, ?_, ?_, inferInstance⟩
  · simp [polynomialPresentation]
  · intro i
    rfl

theorem inverse_identification : inverseIdentification.{u} := by
  intro A _ a
  refine ⟨IsLocalization.Away.mvPolynomialQuotientEquiv (Localization.Away a) a, ?_⟩
  simp

theorem inverse_generator : inverseGenerator.{u} := by
  intro A _ a i
  let e := IsLocalization.Away.mvPolynomialQuotientEquiv (Localization.Away a) a
  change e.symm (IsLocalization.Away.invSelf a) = Ideal.Quotient.mk _ (X ())
  apply e.injective
  simp [e]

theorem inverse_equation : inverseEquation.{u} := by
  intro A _ a j
  simp [inversePresentation, Algebra.Presentation.reindex,
    show finOneEquiv.symm () = (0 : Fin 1) from Subsingleton.elim _ _]

theorem inverse_minor : inverseMinor.{u} := by
  intro A _ a
  rw [Matrix.det_fin_one]
  rw [AdvCommAlg.Smooth.selected_minor_entries]
  rw [inverse_equation]
  simp

theorem inverse_unit : inverseUnit.{u} := by
  intro A _ a
  let e := IsLocalization.Away.mvPolynomialQuotientEquiv (Localization.Away a) a
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a
  have h' : IsUnit (e.symm (algebraMap A (Localization.Away a) a)) :=
    h.map e.symm.toMonoidHom
  rw [e.symm.commutes] at h'
  exact h'

theorem inverse_example : inverseExample.{u} := by
  intro A _ a
  have h : presentationStandardSmooth (inversePresentation A a) := by
    refine ⟨Function.Embedding.refl _, ?_⟩
    rw [inverse_minor]
    exact inverse_unit A a
  refine ⟨h, ?_, ?_⟩
  · simp [Algebra.Presentation.dimension]
  · obtain ⟨Q, hQ⟩ :=
      (AdvCommAlg.Smooth.presentation_standard_smooth_iff_submersive _).mp h
    apply Q.isStandardSmoothOfRelativeDimension
    simp [Algebra.Presentation.dimension]

theorem inverse_zero : inverseZero.{u} := by
  intro A _
  have h := inverse_unit A (0 : A)
  apply subsingleton_of_zero_eq_one
  exact isUnit_zero_iff.mp (show IsUnit (0 : InverseQuotient A 0) from by
    simpa only [map_zero] using h)

end
end AdvCommAlg.Smooth.Elementary
