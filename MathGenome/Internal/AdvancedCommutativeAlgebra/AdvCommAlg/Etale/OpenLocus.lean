import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.OpenLocus
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.StandardAndPointwiseDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.PointwiseCriterion

/-! ET-04, the étale locus. We compare the principal-neighborhood
definition with prime-local formal étaleness before applying the canonical
locus identities. In particular, the support below uses the entire
localization of Ω, rather than its fiber at the residue field. -/
namespace AdvCommAlg.Etale

universe u v

open Specs.AdvCommAlg.Etale.OpenLocus

theorem neighborhood_iff_isEtaleAt : neighborhoodIffIsEtaleAt.{u,v} := by
  intro A B _ _ _ _ q
  constructor
  · rintro ⟨b, hb, he⟩
    exact (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr he)
      (show q ∈ PrimeSpectrum.basicOpen b from hb)
  · intro h
    let : Algebra.IsEtaleAt A q.asIdeal := h
    exact Algebra.exists_etale_of_isEtaleAt q.asIdeal

theorem neighborhood_iff_formal : neighborhoodIffFormal.{u,v} := by
  intro A B _ _ _ _ q
  exact (neighborhood_iff_isEtaleAt A B q).trans
    (FormalLifting.formallyEtale_iff A (Localization.AtPrime q.asIdeal)).symm

theorem etaleLocus_eq_mathlib : locusEqMathlib.{u,v} := by
  intro A B _ _ _ _
  exact Set.ext fun q => neighborhood_iff_isEtaleAt A B q

theorem isOpen_etaleLocus : isOpenEtaleLocus.{u,v} := by
  intro A B _ _ _ _
  rw [etaleLocus_eq_mathlib A B]
  exact Algebra.isOpen_etaleLocus

private theorem smoothLocus_eq_mathlib (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] :
    Specs.AdvCommAlg.Smooth.smoothLocusValue A B = Algebra.smoothLocus A B := by
  apply Set.ext
  intro q
  exact (Smooth.neighborhood_iff_formal A B q).trans
    (FormalLifting.formallySmooth_iff A (Localization.AtPrime q.asIdeal))

theorem etaleLocus_eq_smoothLocus_diff_support : locusEqSmoothDiffSupport.{u,v} := by
  intro A B _ _ _ _
  rw [etaleLocus_eq_mathlib A B, smoothLocus_eq_mathlib A B,
    Algebra.etaleLocus_eq_unramifiedLocus_inter_smoothLocus,
    Algebra.unramifiedLocus_eq_compl_support]
  ext q
  exact and_comm

theorem differential_support_iff : differentialSupportIff.{u,v} := by
  intro A B _ _ _ q
  exact Iff.rfl

end AdvCommAlg.Etale
