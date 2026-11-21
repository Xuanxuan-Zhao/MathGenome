import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.QuotientsAndIdempotents
import Mathlib.RingTheory.Ideal.IdempotentFG

namespace AdvCommAlg.Etale

universe u

open Specs.AdvCommAlg.Etale.Quotients

/-- Formal étaleness of a quotient is exactly idempotence of its ideal. -/
theorem formallyEtale_quotient_iff : formallyEtaleQuotient.{u} := by
  intro A _ I
  rw [FormalLifting.formallyEtale_iff]
  simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, IsIdempotentElem, sq] using
    (Algebra.FormallyEtale.iff_of_surjective
      (R := A) (S := A ⧸ I) Ideal.Quotient.mk_surjective)

/-- Finite presentation of a quotient forces finite generation of its kernel. -/
theorem finitePresentation_quotient_iff : finitePresentationQuotient.{u} := by
  intro A _ I
  constructor
  · intro h
    let := h
    simpa only [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] using
      (Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ A I)
        Ideal.Quotient.mk_surjective)
  · intro h
    exact Algebra.FinitePresentation.quotient h

/-- An étale quotient has a single idempotent generator, and conversely. -/
theorem etale_quotient_iff : etaleQuotient.{u} := by
  intro A _ I
  rw [etale_iff, finitePresentation_quotient_iff, formallyEtale_quotient_iff]
  constructor
  · rintro ⟨hfg, hid⟩
    exact (I.isIdempotentElem_iff_of_fg hfg).mp (by simpa only [IsIdempotentElem, sq] using hid)
  · rintro ⟨e, he, rfl⟩
    refine ⟨Submodule.fg_span_singleton e, ?_⟩
    simp only [sq, Ideal.span_singleton_mul_span_singleton, he]

/-- The canonical A-algebra isomorphism A/I ≃ A[1/(1-e)]. -/
noncomputable def quotientLocalization : quotientLocalizationType.{u} :=
  quotientLocalizationValue

/-- The canonical isomorphism sends the class of a to the localization image of a. -/
theorem quotientLocalization_apply : quotientLocalizationApply.{u} := by
  intro A _ I e he hI a
  exact (quotientLocalizationValue A I e he hI).commutes a

end AdvCommAlg.Etale
