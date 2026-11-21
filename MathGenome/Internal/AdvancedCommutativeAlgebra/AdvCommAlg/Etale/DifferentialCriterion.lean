import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.DifferentialCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.UnramifiedCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.SplittingCriterion

/-! The differential characterization of étaleness (ET-02). -/
namespace AdvCommAlg.Etale

universe u v w
noncomputable section

open Specs.AdvCommAlg.Differentials
open Specs.AdvCommAlg.Etale

theorem etale_iff_smooth_and_subsingleton_omega : etaleIffSmoothOmega.{u,v} := by
  intro A B _ _ _
  change Algebra.Etale A B ↔ Algebra.Smooth A B ∧ Subsingleton (KaehlerDifferential A B)
  rw [Algebra.Etale.iff_formallyUnramified_and_smooth]
  constructor
  · rintro ⟨hu, hs⟩
    exact ⟨hs, hu.subsingleton_kaehlerDifferential⟩
  · rintro ⟨hs, hΩ⟩
    exact ⟨⟨hΩ⟩, hs⟩

/-- For any formally smooth presenting algebra, the split conormal sequence
and vanishing of its cokernel are equivalent to invertibility of its left map. -/
theorem etale_iff_conormal_bijective (A : Type u) (P : Type v) (B : Type w)
    [CommRing A] [CommRing P] [CommRing B]
    [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
    (h : Function.Surjective (algebraMap P B))
    (hP : FormalLifting.FormallySmooth A P) :
    Etale A B ↔ Algebra.FinitePresentation A B ∧
      Function.Bijective (conormalMapValue A P B h) := by
  obtain ⟨he, hs⟩ := Differentials.conormal_exact A P B h
  have hsplit := (FormalLifting.SplittingCriterion.splitting_criterion A P B h hP).2
  constructor
  · intro hE
    obtain ⟨hsm, hΩ⟩ := (etale_iff_smooth_and_subsingleton_omega A B).mp hE
    obtain ⟨hfp, hfs⟩ := (Smooth.smooth_iff A B).mp hsm
    have hinj := (hsplit.mp hfs).1
    exact ⟨hfp, hinj, fun x => (he x).mp (hΩ.elim _ _)⟩
  · rintro ⟨hfp, hbij⟩
    let e := LinearEquiv.ofBijective (conormalMapValue A P B h) hbij
    have hfs : FormalLifting.FormallySmooth A B := hsplit.mpr
      ⟨hbij.1, he, hs, e.symm.toLinearMap, by ext x; exact e.symm_apply_apply x⟩
    have hΩ : Subsingleton (KaehlerDifferential A B) := by
      suffices hz : ∀ x : KaehlerDifferential A B, x = 0 from
        ⟨fun x y => (hz x).trans (hz y).symm⟩
      intro x
      obtain ⟨y, rfl⟩ := hs x
      obtain ⟨z, rfl⟩ := hbij.2 y
      exact he.apply_apply_eq_zero z
    exact (etale_iff_smooth_and_subsingleton_omega A B).mpr
      ⟨(Smooth.smooth_iff A B).mpr ⟨hfp, hfs⟩, hΩ⟩

theorem polynomial_presentation_criterion : polynomialPresentationCriterion.{u,v,w} := by
  intro A B ι _ _ _ π hπ
  letI : Algebra (MvPolynomial ι A) B := π.toRingHom.toAlgebra
  letI : IsScalarTower A (MvPolynomial ι A) B := IsScalarTower.of_algHom π
  exact etale_iff_conormal_bijective A (MvPolynomial ι A) B hπ
    ((FormalLifting.formallySmooth_iff A (MvPolynomial ι A)).mpr inferInstance)

theorem etale_iff_exists_conormal_iso : etaleIffExistsConormalIso.{u,v} := by
  intro A B _ _ _
  constructor
  · intro hE
    letI : Algebra.Etale A B := hE
    obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType A B)
    exact ⟨inferInstance, n, π, hπ,
      ((polynomial_presentation_criterion A B (Fin n) π hπ).mp hE).2⟩
  · rintro ⟨hfp, n, π, hπ, hi⟩
    exact (polynomial_presentation_criterion A B (Fin n) π hπ).mpr ⟨hfp, hi⟩

theorem etale_iff_every_conormal_iso : etaleIffEveryConormalIso.{u,v,w} := by
  intro A B _ _ _
  constructor
  · intro hE
    exact ⟨((etale_iff A B).mp hE).1, fun ι π hπ =>
      ((polynomial_presentation_criterion A B ι π hπ).mp hE).2⟩
  · rintro ⟨hfp, hall⟩
    letI : Algebra.FinitePresentation A B := hfp
    obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType A B)
    -- Raise the finite variable type to the independently quantified universe.
    let e := MvPolynomial.renameEquiv A (Equiv.ulift : ULift.{w} (Fin n) ≃ Fin n)
    let π' := π.comp e.toAlgHom
    have hπ' : Function.Surjective π' := hπ.comp e.surjective
    exact (polynomial_presentation_criterion A B (ULift.{w} (Fin n)) π' hπ').mpr
      ⟨hfp, hall _ π' hπ'⟩

end
end AdvCommAlg.Etale
