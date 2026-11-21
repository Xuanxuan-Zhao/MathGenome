import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.LocusDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.PointwiseCriterion
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Localization.Algebra

/-! The pointwise criterion in SM-07, including comparison with the
presentation localized at the inverse image prime. -/
namespace AdvCommAlg.Smooth

universe u v w z
noncomputable section
open TensorProduct
open Algebra.Extension
open Specs.AdvCommAlg.Differentials
open Specs.AdvCommAlg.Smooth.PointwiseCriterion

/-- The neighborhood definition agrees with the prime-local lifting property. -/
theorem neighborhood_iff_formal : neighborhoodIffFormal.{u,v} := by
  intro A B _ _ _ _ q
  rw [FormalLifting.formallySmooth_iff A (Localization.AtPrime q.asIdeal)]
  constructor
  · rintro ⟨g, hg, hs⟩
    exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hs)
      (show q ∈ PrimeSpectrum.basicOpen g from hg)
  · intro h
    have : Algebra.IsSmoothAt A q.asIdeal := h
    exact Algebra.IsSmoothAt.exists_notMem_smooth A q.asIdeal

section Comparison
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  (E : Algebra.Extension.{w} A B) (q : PrimeSpectrum B)

/-- Localization of the kernel is the kernel of the localized surjection. -/
lemma localPresentation_kernel_isBaseChange :
    IsBaseChange (localPresentation E q).Ring ((localizationHom E q).mapKer rfl) := by
  let M := q.asIdeal.primeCompl.comap (algebraMap E.Ring B)
  have hM : M.map (algebraMap E.Ring B) = q.asIdeal.primeCompl :=
    Submonoid.map_comap_eq_of_surjective E.algebraMap_surjective _
  have : IsLocalizedModule M ((localizationHom E q).mapKer rfl) := by
    convert RingHom.toKerIsLocalization_isLocalizedModule
      (S := (localPresentation E q).Ring) (Localization.AtPrime q.asIdeal)
        (algebraMap E.Ring B) hM using 1 <;> rfl
  exact IsLocalizedModule.isBaseChange M (localPresentation E q).Ring _

/-- The canonical comparison on the left term, I/I². -/
def localConormalEquiv :
    (Localization.AtPrime q.asIdeal ⊗[B] E.Cotangent) ≃ₗ[Localization.AtPrime q.asIdeal]
      (localPresentation E q).Cotangent :=
  Algebra.Extension.tensorCotangent (localizationHom E q) rfl
    (localPresentation_kernel_isBaseChange E q)

/-- The canonical differential-localization comparison on the middle term. -/
def localMiddleEquiv :
    (Localization.AtPrime q.asIdeal ⊗[B] E.CotangentSpace) ≃ₗ[Localization.AtPrime q.asIdeal]
      (localPresentation E q).CotangentSpace :=
  Algebra.Extension.tensorCotangentSpaceOfFormallyEtale (localizationHom E q)
    (RingHom.formallyEtale_algebraMap.mpr
      (Algebra.FormallyEtale.of_isLocalization
        (Rₘ := (localPresentation E q).Ring)
        (q.asIdeal.primeCompl.comap (algebraMap E.Ring B))))

lemma localConormalEquiv_tmul (t : Localization.AtPrime q.asIdeal) (x : E.Cotangent) :
    localConormalEquiv E q (t ⊗ₜ[B] x) = t • Cotangent.map (localizationHom E q) x := rfl

lemma localMiddleEquiv_tmul (t : Localization.AtPrime q.asIdeal) (x : E.CotangentSpace) :
    localMiddleEquiv E q (t ⊗ₜ[B] x) = t • CotangentSpace.map (localizationHom E q) x := rfl

/-- The square commutes on ideal classes, hence on the localized conormal. -/
lemma local_conormal_square :
    (localMiddleEquiv E q).toLinearMap.comp (localizedConormalMap E q) =
      (localPresentation E q).cotangentComplex.comp (localConormalEquiv E q).toLinearMap := by
  ext x
  change localMiddleEquiv E q (localizedConormalMap E q (1 ⊗ₜ[B] x)) =
    (localPresentation E q).cotangentComplex (localConormalEquiv E q (1 ⊗ₜ[B] x))
  simp only [localizedConormalMap, LinearMap.baseChange_tmul,
    localMiddleEquiv_tmul, localConormalEquiv_tmul,
    map_smul, CotangentSpace.map_cotangentComplex]

/-- Retractions transport in both directions across the comparison square. -/
lemma hasLocalRetraction_iff :
    HasLocalRetraction E q ↔
      ∃ ρ : (localPresentation E q).CotangentSpace →ₗ[Localization.AtPrime q.asIdeal]
          (localPresentation E q).Cotangent,
        ρ.comp (localPresentation E q).cotangentComplex = LinearMap.id := by
  let eL := localConormalEquiv E q
  let eF := localMiddleEquiv E q
  have hcomm (x) : eF (localizedConormalMap E q x) =
      (localPresentation E q).cotangentComplex (eL x) :=
    LinearMap.congr_fun (local_conormal_square E q) x
  constructor
  · rintro ⟨ρ, hρ⟩
    refine ⟨eL.toLinearMap.comp (ρ.comp eF.symm.toLinearMap), ?_⟩
    apply LinearMap.ext
    intro x
    change eL (ρ (eF.symm ((localPresentation E q).cotangentComplex x))) = x
    have hx : eF.symm ((localPresentation E q).cotangentComplex x) =
        localizedConormalMap E q (eL.symm x) := by
      apply eF.injective
      rw [eF.apply_symm_apply, hcomm, eL.apply_symm_apply]
    rw [hx, show ρ (localizedConormalMap E q (eL.symm x)) = eL.symm x from
      LinearMap.congr_fun hρ (eL.symm x), eL.apply_symm_apply]
  · rintro ⟨ρ, hρ⟩
    refine ⟨eL.symm.toLinearMap.comp (ρ.comp eF.toLinearMap), ?_⟩
    apply LinearMap.ext
    intro x
    change eL.symm (ρ (eF (localizedConormalMap E q x))) = x
    rw [hcomm, show ρ ((localPresentation E q).cotangentComplex (eL x)) = eL x from
      LinearMap.congr_fun hρ (eL x), eL.symm_apply_apply]

/-- FL-07 for P_Q → B_q, transported to the original localized conormal map. -/
lemma formal_iff_localRetraction [Algebra.FormallySmooth A E.Ring] :
    Specs.AdvCommAlg.FormalLifting.formallySmoothValue A (Localization.AtPrime q.asIdeal) ↔
      HasLocalRetraction E q := by
  have : Algebra.FormallySmooth E.Ring (localPresentation E q).Ring :=
    Algebra.FormallySmooth.of_isLocalization
      (q.asIdeal.primeCompl.comap (algebraMap E.Ring B))
  have : Algebra.FormallySmooth A (localPresentation E q).Ring :=
    Algebra.FormallySmooth.comp A E.Ring (localPresentation E q).Ring
  exact (FormalLifting.formallySmooth_iff A (Localization.AtPrime q.asIdeal)).trans
    ((localPresentation E q).formallySmooth_iff_split_injection.trans
      (hasLocalRetraction_iff E q).symm)

end Comparison

/-- The actual localized presentation at Q gives exactly the localized map. -/
theorem localization_comparison : localizationComparison.{u,v,w} := by
  intro A B _ _ _ E q
  refine ⟨rfl, localConormalEquiv E q, localMiddleEquiv E q, ?_, ?_, local_conormal_square E q⟩
  · intro t f
    exact localConormalEquiv_tmul E q t (Cotangent.mk f)
  · intro t b p
    rw [localMiddleEquiv_tmul, CotangentSpace.map_tmul]
    rfl

/-- Formal smoothness at q is equivalent to a B_q-linear left inverse, for
any given finite polynomial presentation, including the empty one. -/
theorem formal_iff_retraction : formalIffRetraction.{u,v} := by
  intro A B _ _ _ _ n _ _ h q
  let E := conormalExtension A (MvPolynomial (Fin n) A) B h
  have : Algebra.FormallySmooth A E.Ring :=
    inferInstanceAs (Algebra.FormallySmooth A (MvPolynomial (Fin n) A))
  exact formal_iff_localRetraction E q

/-- The three conditions of SM-07 hold for every finite presentation. -/
theorem pointwise_criterion : pointwiseCriterion.{u,v} := by
  intro A B _ _ _ _ n _ _ h q
  exact ⟨neighborhood_iff_formal A B q,
    (neighborhood_iff_formal A B q).trans (formal_iff_retraction A B n h q)⟩

/-- The condition depends only on B/A and q, even among arbitrary formally
smooth presenting algebras, hence among all finite polynomial presentations. -/
theorem presentation_independent : presentationIndependent.{u,v,w,z} := by
  intro A B _ _ _ E F _ _ q
  exact (formal_iff_localRetraction E q).symm.trans (formal_iff_localRetraction F q)

end
end AdvCommAlg.Smooth
