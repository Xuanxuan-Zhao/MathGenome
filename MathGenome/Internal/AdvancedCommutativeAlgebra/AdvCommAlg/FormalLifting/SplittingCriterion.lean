import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.SplittingCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Conormal

namespace AdvCommAlg.FormalLifting.SplittingCriterion

universe u v w
noncomputable section

open Specs.AdvCommAlg.Differentials
open Specs.AdvCommAlg.FormalLifting.SplittingCriterion
open TensorProduct

variable {A : Type u} {P : Type v} {B : Type w}
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]

/-- The upstream right exact sequence turns a retraction into a split short
exact sequence, including injectivity at the left term. -/
lemma splitConormal_iff_retraction (h : Function.Surjective (algebraMap P B)) :
    SplitConormal A P B h ↔
      ∃ ρ : (conormalExtension A P B h).CotangentSpace →ₗ[B]
          (conormalExtension A P B h).Cotangent,
        ρ.comp (conormalExtension A P B h).cotangentComplex = LinearMap.id := by
  constructor
  · intro H
    exact H.2.2.2
  · rintro ⟨ρ, hρ⟩
    have hi : Function.Injective (conormalMapValue A P B h) :=
      (show Function.LeftInverse ρ (conormalMapValue A P B h) from
        fun x => LinearMap.congr_fun hρ x).injective
    obtain ⟨he, hs⟩ := AdvCommAlg.Differentials.conormal_exact A P B h
    exact ⟨hi, he, hs, ρ, hρ⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A section gives the retraction on the shared conormal object. Mathlib's
section correspondence is P-linear on the ordinary ideal cotangent; we
transport along the canonical quotient bridge and descend scalars to B. -/
theorem section_implies_split : sectionImpliesSplit.{u,v,w} := by
  intro A P B _ _ _ _ _ _ _ h hs
  obtain ⟨s, hs⟩ := hs
  let E := conormalExtension A P B h
  let l := (retractionKerCotangentToTensorEquivSection (R := A) h).symm ⟨s, hs⟩
  let e := E.cotangentEquivCotangentKer.symm
  let ρ : (B ⊗[P] KaehlerDifferential A P) →ₗ[P] E.Cotangent := e.comp l.1
  let ρB := ρ.extendScalarsOfSurjective h
  apply (splitConormal_iff_retraction h).mpr
  refine ⟨ρB, ?_⟩
  exact LinearMap.ext (DFunLike.congr_fun l.2 : _)

/-- The three conditions of FL-07, retaining arbitrary formally smooth P. -/
theorem splitting_criterion : splittingCriterion.{u,v,w} := by
  intro A P B _ _ _ _ _ _ _ h hP
  let : Algebra.FormallySmooth A P := (formallySmooth_iff A P).mp hP
  let : Algebra.FormallySmooth A (conormalExtension A P B h).Ring :=
    (formallySmooth_iff A P).mp hP
  constructor
  · exact (formallySmooth_iff A B).trans
      (Algebra.FormallySmooth.iff_split_surjection (IsScalarTower.toAlgHom A P B) h)
  · exact ((formallySmooth_iff A B).trans
      (conormalExtension A P B h).formallySmooth_iff_split_injection).trans
        (splitConormal_iff_retraction h).symm

end
end AdvCommAlg.FormalLifting.SplittingCriterion
