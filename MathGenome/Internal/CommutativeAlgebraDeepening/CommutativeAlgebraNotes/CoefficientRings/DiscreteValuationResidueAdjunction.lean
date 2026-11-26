import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.DiscreteValuationResidueAdjunction
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.Polynomial.Basic

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing Polynomial

private theorem dvr_of_maximalIdeal_eq_span {S : Type*} [CommRing S] [IsDomain S]
    [IsLocalRing S] [IsNoetherianRing S] {t : S} (ht : t ≠ 0)
    (hm : maximalIdeal S = Ideal.span {t}) : IsDiscreteValuationRing S := by
  have hn : maximalIdeal S ≠ ⊥ := fun h ↦ ht (Ideal.span_singleton_eq_bot.mp (hm.symm.trans h))
  have hprincipal : (maximalIdeal S).IsPrincipal := ⟨t, hm⟩
  exact ((IsDiscreteValuationRing.TFAE S (isField_iff_maximalIdeal_eq.not.mpr hn)).out 5 1).mp
    hprincipal

private theorem isLocalHom_of_uniformizer {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) {t : R}
    (hR : maximalIdeal R = Ideal.span {t}) (hS : f t ∈ maximalIdeal S) :
    IsLocalHom f := by
  apply ((local_hom_TFAE f).out 3 1).mp
  rw [hR, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
  exact hS

private theorem isLocalRing_of_integral_map_maximal {R S : Type*}
    [CommRing R] [IsLocalRing R] [CommRing S] (f : R →+* S) (hf : f.IsIntegral)
    (hmax : ((maximalIdeal R).map f).IsMaximal) : IsLocalRing S := by
  refine IsLocalRing.of_unique_max_ideal ⟨_, hmax, fun M hM ↦ ?_⟩
  have hcomap := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal f hf M
  exact (hmax.eq_of_le hM.ne_top (Ideal.map_le_iff_le_comap.mpr
    (le_of_eq (eq_maximalIdeal hcomap).symm))).symm

/-- The single-generator step in constructing a DVR with a prescribed residue field. -/
theorem discreteValuationResidueAdjunction : Specs.discreteValuationResidueAdjunctionType := by
  classical
  intro p hp D _ _ _ hD K _ _ e L _ _ a ha
  let r : D →+* K := e.toRingHom.comp (residue D)
  have hr : Function.Surjective r := e.surjective.comp residue_surjective
  have hrker : RingHom.ker r = maximalIdeal D := by
    rw [RingHom.ker_comp_of_injective _ e.injective, ker_residue]
  have hpD : (p : D) ≠ 0 := fun h ↦ IsDiscreteValuationRing.not_a_field D <| by
    rw [hD, h, Ideal.span_singleton_eq_bot.mpr rfl]
  by_cases halg : IsIntegral K a
  · obtain ⟨g, hg, hdeg, hmonic⟩ := lifts_and_natDegree_eq_and_monic
      (mem_lifts_of_surjective hr (minpoly K a)) (minpoly.monic halg)
    -- The monic lift is irreducible because its reduction is irreducible.
    have hgirr : Irreducible g := by
      apply Monic.irreducible_of_irreducible_map r g hmonic
      rw [hg]
      exact minpoly.irreducible halg
    let S := AdjoinRoot g
    let f : D →+* S := AdjoinRoot.of g
    let : IsDomain S := AdjoinRoot.isDomain_of_prime (irreducible_iff_prime.mp hgirr)
    have hf : Function.Injective f :=
      AdjoinRoot.of.injective_of_monic_of_degree_pos hmonic
        (natDegree_pos_iff_degree_pos.mp (by rw [hdeg]; exact minpoly.natDegree_pos halg))
    let I := (maximalIdeal D).map f
    let π := AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal D) g
    have hredPoly : Associated ((g.map (residue D)).map e.toRingHom) (minpoly K a) :=
      Associated.of_eq ((map_map (residue D) e.toRingHom g).trans hg)
    let eB := AdjoinRoot.mapRingEquiv e (g.map (residue D)) (minpoly K a) hredPoly
    let eQ : S ⧸ I ≃+* AdjoinRoot (minpoly K a) := π.trans eB
    let eL : AdjoinRoot (minpoly K a) ≃ₐ[K] L :=
      (IntermediateField.adjoinRootEquivAdjoin K halg).trans
        ((IntermediateField.equivOfEq ha).trans IntermediateField.topEquiv)
    let E : S ⧸ I ≃+* L := eQ.trans eL.toRingEquiv
    -- Integrality forces every maximal ideal upstairs to contain the extended ideal.
    have hI : I.IsMaximal := Ideal.Quotient.maximal_of_isField I (E.isField (Field.toIsField L))
    let : IsLocalRing S := isLocalRing_of_integral_map_maximal f
      (AdjoinRoot.isIntegral_of_monic hmonic).isIntegral hI
    have hIS : I = maximalIdeal S := eq_maximalIdeal hI
    have hS : maximalIdeal S = Ideal.span {(p : S)} := by
      rw [← hIS]
      change (maximalIdeal D).map f = _
      rw [hD, Ideal.map_span, Set.image_singleton, map_natCast]
    have hpS : (p : S) ≠ 0 := by
      intro h
      apply hpD
      apply hf
      simpa using h
    let : IsDiscreteValuationRing S := dvr_of_maximalIdeal_eq_span hpS hS
    have hlocal : IsLocalHom f := isLocalHom_of_uniformizer f hD
      (by rw [map_natCast, hS]; exact Ideal.mem_span_singleton_self _)
    refine ⟨S, inferInstance, inferInstance, inferInstance, f, hlocal, hf, hS,
      (Ideal.quotEquivOfEq hIS.symm).trans E, ?_⟩
    apply RingHom.ext
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    change E (Ideal.Quotient.mk I (f x)) = _
    change eL (eQ (Ideal.Quotient.mk I (f x))) = _
    have hπ : π (Ideal.Quotient.mk I (f x)) =
        AdjoinRoot.of (g.map (residue D)) (residue D x) := by
      have hred :=
        AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of (maximalIdeal D) g (C x)
      rw [map_C] at hred
      exact hred
    have hq : eQ (Ideal.Quotient.mk I (f x)) =
        algebraMap K (AdjoinRoot (minpoly K a)) (e (residue D x)) := by
      change eB (π (Ideal.Quotient.mk I (f x))) = _
      calc
        _ = eB (AdjoinRoot.of (g.map (residue D)) (residue D x)) := congrArg eB hπ
        _ = _ := AdjoinRoot.map_of e.toRingHom _ _ hredPoly.symm.dvd (residue D x)
    rw [hq, eL.commutes]
    rfl
  · have htrans : Transcendental K a := fun h ↦ halg h.isIntegral
    let P := (maximalIdeal D).map (C : D →+* D[X])
    have : P.IsPrime := Ideal.isPrime_map_C_of_isPrime
    let S := Localization.AtPrime P
    let f : D →+* S := (algebraMap D[X] S).comp C
    have hf : Function.Injective f :=
      (FaithfulSMul.algebraMap_injective D[X] S).comp C_injective
    have hS : maximalIdeal S = Ideal.span {(p : S)} := by
      change maximalIdeal (Localization.AtPrime P) = _
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      change ((maximalIdeal D).map C).map (algebraMap D[X] S) = _
      rw [Ideal.map_map, hD, Ideal.map_span, Set.image_singleton, map_natCast]
    have hpS : (p : S) ≠ 0 := by
      intro h
      apply hpD
      apply hf
      simpa using h
    let : IsDiscreteValuationRing S := dvr_of_maximalIdeal_eq_span hpS hS
    let : IsLocalHom f := isLocalHom_of_uniformizer f hD
      (by rw [map_natCast, hS]; exact Ideal.mem_span_singleton_self _)
    let g : D[X] →+* L := (aeval a : K[X] →ₐ[K] L).toRingHom.comp (mapRingHom r)
    have hgker : RingHom.ker g = P := by
      ext q
      change (aeval a : K[X] →ₐ[K] L) (q.map r) = 0 ↔ q ∈ P
      rw [← map_zero (aeval a : K[X] →ₐ[K] L),
        (transcendental_iff_injective.mp htrans).eq_iff, Ideal.mem_map_C_iff]
      simp only [Polynomial.ext_iff, coeff_map, coeff_zero, ← RingHom.mem_ker, hrker]
    let F : P.ResidueField →+* L := Ideal.ResidueField.lift P g hgker.ge
      (fun q hq ↦ isUnit_iff_ne_zero.mpr (by
        change q ∉ P at hq
        change q ∉ RingHom.ker g
        rwa [hgker]))
    have hF (q : D[X]) : F (algebraMap D[X] P.ResidueField q) = g q :=
      Ideal.ResidueField.lift_algebraMap P _ _ _ _
    have hcompat (x : D) : F (residue S (f x)) = algebraMap K L (e (residue D x)) := by
      change F (algebraMap D[X] P.ResidueField (C x)) = _
      rw [hF]
      simp [g, r]
    let : Algebra K P.ResidueField :=
      ((ResidueField.map f).comp e.symm.toRingHom).toAlgebra
    let Fₐ : P.ResidueField →ₐ[K] L :=
      { F with
        commutes' := fun y ↦ by
          obtain ⟨x, rfl⟩ := hr y
          change F (ResidueField.map f (e.symm (e (residue D x)))) = _
          rw [RingEquiv.symm_apply_apply, ResidueField.map_residue, hcompat]
          rfl }
    -- The image is a subfield containing the generator, the image of X.
    have hFsurj : Function.Surjective Fₐ := by
      apply AlgHom.fieldRange_eq_top.mp
      apply top_le_iff.mp
      rw [← ha]
      apply IntermediateField.adjoin_le_iff.mpr
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      refine ⟨algebraMap D[X] P.ResidueField X, ?_⟩
      change F _ = a
      rw [hF]
      simp [g]
    have hFbij : Function.Bijective F := ⟨F.injective, hFsurj⟩
    refine ⟨S, inferInstance, inferInstance, inferInstance, f, inferInstance, hf, hS,
      RingEquiv.ofBijective F hFbij, ?_⟩
    apply RingHom.ext
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact hcompat x

end CommutativeAlgebraNotes.CoefficientRings
