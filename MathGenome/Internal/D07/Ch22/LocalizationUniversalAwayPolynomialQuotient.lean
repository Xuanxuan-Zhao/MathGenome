import MathGenome.Internal.Specs.D07.Ch22.LocalizationUniversalAwayPolynomialQuotient

/-!
The principal localization presentation, paper.tex:7115–7124.
Mathlib's `awayEquivAdjoin` constructs the two maps by localization lifting and
polynomial evaluation followed by quotient lifting. Its inverse laws follow
from the uniqueness parts of those universal properties. `AdjoinRoot` is
literally the quotient used in the specification, not a field extension.
-/

universe u

namespace D07.Ch22.LocalizationUniversalAwayPolynomialQuotient

open Polynomial
open Specs.D07.Ch22.LocalizationUniversalAwayPolynomialQuotient

noncomputable def presentationEquiv : EquivalenceType.{u} :=
  fun _ _ f => Localization.awayEquivAdjoin f

theorem evaluationFormula : EvaluationFormula.{u} := by
  intro R _ f p
  rfl

theorem inverseGenerator : InverseGenerator.{u} := by
  intro R _ f
  apply (equivalenceValue R f).symm.injective
  rw [AlgEquiv.symm_apply_apply, evaluationFormula]
  exact Polynomial.aeval_X _ |>.symm

theorem coefficientFormulas : CoefficientFormulas.{u} := by
  intro R _ f a
  constructor
  · exact (equivalenceValue R f).commutes a
  · rw [evaluationFormula]
    exact Polynomial.aeval_C _ _

theorem quotientInverse : QuotientInverse.{u} := by
  intro R _ f
  have h : algebraMap R (Presentation R f) f * quotientMap f X = 1 :=
    AdjoinRoot.root_isInv f
  exact ⟨h, (mul_comm _ _).trans h⟩

theorem universalMaps : UniversalMaps.{u} := by
  intro R _ f
  constructor
  · intro h hh
    apply Ideal.Quotient.algHom_ext R
    apply Polynomial.algHom_ext
    change h (quotientMap f X) = (equivalenceValue R f).symm (quotientMap f X)
    rw [hh, evaluationFormula, Polynomial.aeval_X]
  · intro h
    exact (IsLocalization.algHom_subsingleton (Submonoid.powers f)).elim _ _

theorem inverseComposites : InverseComposites.{u} := by
  intro R _ f
  constructor
  · exact (IsLocalization.algHom_subsingleton (Submonoid.powers f)).elim _ _
  · exact (AdjoinRoot.algHom_subsingleton (r := f)).elim _ _

theorem nilpotentCase : NilpotentCase.{u} := by
  intro R _ f hf
  have hL : Subsingleton (Localization.Away f) :=
    (IsLocalization.subsingleton_iff (M := Submonoid.powers f)).mpr hf
  refine ⟨hL, ?_⟩
  exact ⟨fun x y => (equivalenceValue R f).symm.injective (hL.elim _ _)⟩

theorem zeroRingCase : ZeroRingCase.{u} := by
  intro R _ _ f
  apply nilpotentCase R f
  exact ⟨1, Subsingleton.elim _ _⟩

end D07.Ch22.LocalizationUniversalAwayPolynomialQuotient
