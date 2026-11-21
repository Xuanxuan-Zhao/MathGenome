import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.FieldAlgebraClassification
import Mathlib.RingTheory.Etale.Field

/-! ET-11: the field case. The finiteness and reducedness theorems apply
to formally unramified essentially finite-type algebras. A vector space is
free, so no additional freeness hypothesis on the algebra is necessary.
-/
namespace AdvCommAlg.Etale

universe u v

open Specs.AdvCommAlg.Etale.FieldAlgebraClassification

theorem finite_reduced_of_omega_zero : finiteReducedOfOmegaZero.{u,v} := by
  intro K B _ _ _ _ hΩ
  let : Algebra.FormallyUnramified K B := ⟨hΩ⟩
  exact ⟨Algebra.FormallyUnramified.finite_of_free K B,
    Algebra.FormallyUnramified.isReduced_of_field K B⟩

theorem omega_zero_iff_etale : omegaZeroIffEtale.{u,v} := by
  intro K B _ _ _ _
  change Subsingleton (KaehlerDifferential K B) ↔ Algebra.Etale K B
  constructor
  · intro hΩ
    let : Algebra.FormallyUnramified K B := ⟨hΩ⟩
    exact ⟨Algebra.FormallyEtale.of_formallyUnramified_of_field K B,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  · intro hE
    let := hE
    exact Algebra.FormallyUnramified.subsingleton_kaehlerDifferential

theorem etale_iff_finite_separable_product : etaleIffFiniteSeparableProduct.{u,v} := by
  intro K B _ _ _ _
  exact Algebra.Etale.iff_exists_algEquiv_prod K B

/-- With an empty index, the required field and algebra structures are vacuous.
The algebra equivalence is the unique equivalence between two zero rings. -/
theorem empty_product : emptyProduct.{u,v} := by
  intro K B _ _ _ _
  have hprod : FiniteSeparableProduct K B := by
    refine ⟨PEmpty.{v+1}, inferInstance, (fun _ => B), (fun i => i.elim),
      (fun i => i.elim), ?_, (fun i => i.elim)⟩
    exact default
  exact ⟨(Algebra.Etale.iff_exists_algEquiv_prod K B).mpr hprod, hprod⟩

end AdvCommAlg.Etale
