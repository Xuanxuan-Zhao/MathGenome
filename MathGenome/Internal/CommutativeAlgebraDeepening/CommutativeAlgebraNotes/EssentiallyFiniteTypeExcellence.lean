import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.EssentiallyFiniteTypeExcellence
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PolynomialOverCompleteGRing
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteAndLocalizedGRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalizingRegularLociAndChains
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularMapOperations
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ComparePolynomialLocalCompletions
import Mathlib.RingTheory.Localization.Algebra
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.PolynomialOverCompleteGRing
namespace CommutativeAlgebraNotes.Excellence

open IsLocalRing
open PolynomialLocalCompletion
open private geometricallyRegular_fiber_of_localRingEquiv
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteAndLocalizedGRings

section
universe u v

local instance completionIsNoetherian (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] : IsNoetherianRing (Completion R) :=
  P103.Ch07.CompletedNoetherian.completed_noetherian R _

private theorem regular_completion_atPrime_polynomial_of_local
    (hComplete : Specs.polynomial_isGRing_of_completeLocalType.{u})
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : RegularMap R (Completion R) (algebraMap R (Completion R)))
    (P : Ideal (Polynomial R)) [P.IsPrime]
    (hP : maximalIdeal R ≤ P.comap Polynomial.C) :
    RegularMap (Localization.AtPrime P) (Completion (Localization.AtPrime P))
      (algebraMap (Localization.AtPrime P) (Completion (Localization.AtPrime P))) := by
  let H := Completion R
  let : Algebra (Polynomial R) (Polynomial H) := Polynomial.algebra R H
  obtain ⟨hp, hc, e, he⟩ := completionComparison R P hP
  let Q := extendedIdeal P
  let : Q.IsPrime := hp
  let : Q.LiesOver P := ⟨hc⟩
  let A := Localization.AtPrime P
  let B := Localization.AtPrime Q
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver P Q
  have hPoly : RegularMap (Polynomial R) (Polynomial H)
      (algebraMap (Polynomial R) (Polynomial H)) :=
    RegularMap.baseChange R H (Polynomial R) (Polynomial H) hR
  have hLoc : RegularMap A B (algebraMap A B) :=
    RegularMap.localization (Polynomial R) (Polynomial H) A B P.primeCompl Q.primeCompl hPoly
  have hB : RegularMap B (Completion B) (algebraMap B (Completion B)) := hComplete H Q
  have hComp := RegularMap.comp A B (Completion B) _ _ hLoc hB
  have hEq : e.toRingHom.comp (algebraMap A (Completion A)) =
      (algebraMap B (Completion B)).comp (algebraMap A B) :=
    RingHom.ext he
  apply RegularMap.of_comp_faithfullyFlat A (Completion A) (Completion B) _ e.toRingHom
  · rw [hEq]
    exact hComp
  · exact RingHom.FaithfullyFlat.of_bijective e.bijective

private theorem isGRing_polynomial
    (hComplete : Specs.polynomial_isGRing_of_completeLocalType.{u})
    (R : Type u) [CommRing R] [IsNoetherianRing R] (hR : IsGRing R) :
    IsGRing (Polynomial R) := by
  intro P hprime
  let p := P.comap Polynomial.C
  let : p.IsPrime := Ideal.IsPrime.comap _
  let Rₚ := Localization.AtPrime p
  let S := Polynomial Rₚ
  let : Algebra (Polynomial R) S := Polynomial.algebra R Rₚ
  let M := p.primeCompl.map (Polynomial.C : R →+* Polynomial R)
  let : IsLocalization M S := Polynomial.isLocalization p.primeCompl Rₚ
  let Q := P.map (algebraMap (Polynomial R) S)
  have hdisj : Disjoint (M : Set (Polynomial R)) (P : Set (Polynomial R)) := by
    simpa [M, p] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  let : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S P hprime hdisj
  have hunder : Q.under (Polynomial R) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M S hprime hdisj
  have hcontract : Q.comap Polynomial.C = maximalIdeal Rₚ := by
    rw [← IsLocalization.map_under p.primeCompl Rₚ (Q.comap Polynomial.C),
      ← IsLocalization.map_under p.primeCompl Rₚ (maximalIdeal Rₚ)]
    simp only [Ideal.under_def, Ideal.comap_comap]
    rw [← Polynomial.algebraMap_eq (R := Rₚ),
      ← IsScalarTower.algebraMap_eq R Rₚ S,
      IsScalarTower.algebraMap_eq R (Polynomial R) S, ← Ideal.comap_comap,
      ← Ideal.under_def (Polynomial R), hunder]
    simp [p, IsLocalization.AtPrime.under_maximalIdeal Rₚ p]
  have hQ := regular_completion_atPrime_polynomial_of_local hComplete Rₚ (hR p) Q hcontract.ge
  have hcompl : (Q.under (Polynomial R)).primeCompl = P.primeCompl := by
    ext x
    simp only [Ideal.mem_primeCompl_iff, hunder]
  let : IsLocalization P.primeCompl (Localization.AtPrime Q) := hcompl ▸
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime Q) Q
  let e := (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime Q)
    (Localization.AtPrime P)).toRingEquiv
  apply (regularMap_algebraMap_iff (Localization.AtPrime P) _).mpr
  refine ⟨inferInstance, fun q _ ↦ ?_⟩
  apply geometricallyRegular_fiber_of_localRingEquiv
    (R := Localization.AtPrime Q) (S := Localization.AtPrime P) e q
  exact ((regularMap_algebraMap_iff (Localization.AtPrime Q) _).mp hQ).2 _

private theorem isGRing_mvPolynomial_fin
    (hComplete : Specs.polynomial_isGRing_of_completeLocalType.{u})
    (R : Type u) [CommRing R] [IsNoetherianRing R] (hR : IsGRing R) (n : ℕ) :
    IsGRing (MvPolynomial (Fin n) R) := by
  induction n with
  | zero =>
    let e := (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm
    exact isGRing_surjective e.toRingHom e.surjective hR
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm
    exact isGRing_surjective e.toRingHom e.surjective
      (isGRing_polynomial hComplete _ ih)

private theorem isGRing_finiteType
    (hComplete : Specs.polynomial_isGRing_of_completeLocalType.{u})
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Algebra.FiniteType R B] (hR : IsGRing R) :
    letI := Algebra.FiniteType.isNoetherianRing R B
    IsGRing B := by
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := B)).mp
    inferInstance
  exact isGRing_surjective f.toRingHom hf (isGRing_mvPolynomial_fin hComplete R hR n)

end

theorem isGRing_of_essFiniteType_conditional.{u,v} :
    Specs.polynomial_isGRing_of_completeLocalType.{u} →
      Specs.isGRing_of_essFiniteTypeType.{u,v} := by
  intro hComplete R B _ _ _ _ _ hR
  obtain ⟨B₀, M, hfinite, hloc⟩ :=
    (Algebra.essFiniteType_iff_exists_subalgebra R B).mp inferInstance
  let := Algebra.FiniteType.isNoetherianRing R B₀
  exact isGRing_localization M (isGRing_finiteType hComplete R B₀ hR)

theorem quasiExcellent_of_essFiniteType_conditional.{u,v} :
    Specs.polynomial_isGRing_of_completeLocalType.{u} →
      Specs.quasiExcellent_of_essFiniteTypeType.{u,v} := by
  intro hComplete R B _ _ _ _ hR
  obtain ⟨hNoeth, hG, hJ⟩ := hR
  let := hNoeth
  exact ⟨Algebra.EssFiniteType.isNoetherianRing R B,
    isGRing_of_essFiniteType_conditional hComplete R B hG, J2.of_essFiniteType hJ⟩

theorem excellent_of_essFiniteType_conditional.{u,v} :
    Specs.polynomial_isGRing_of_completeLocalType.{u} →
      Specs.excellent_of_essFiniteTypeType.{u,v} := by
  intro hComplete R B _ _ _ _ hR
  obtain ⟨hNoeth, hG, hJ, hCat⟩ := hR
  let := hNoeth
  exact ⟨Algebra.EssFiniteType.isNoetherianRing R B,
    isGRing_of_essFiniteType_conditional hComplete R B hG, J2.of_essFiniteType hJ,
    UniversallyCatenary.of_essFiniteType hCat⟩

end CommutativeAlgebraNotes.Excellence

universe v8_closure_fab540d856bc646d_u0 v8_closure_fab540d856bc646d_u1
theorem _root_.«CommutativeAlgebraNotes».«Excellence».«excellent_of_essFiniteType» : _root_.«CommutativeAlgebraNotes».«Excellence».«Specs».«excellent_of_essFiniteTypeType».{v8_closure_fab540d856bc646d_u0, v8_closure_fab540d856bc646d_u1} :=
  @_root_.«CommutativeAlgebraNotes».«Excellence».«excellent_of_essFiniteType_conditional».{v8_closure_fab540d856bc646d_u0, v8_closure_fab540d856bc646d_u1} (@_root_.«CommutativeAlgebraNotes».«Excellence».«polynomial_isGRing_of_completeLocal».{v8_closure_fab540d856bc646d_u0})
theorem _root_.«CommutativeAlgebraNotes».«Excellence».«isGRing_of_essFiniteType» : _root_.«CommutativeAlgebraNotes».«Excellence».«Specs».«isGRing_of_essFiniteTypeType».{v8_closure_fab540d856bc646d_u0, v8_closure_fab540d856bc646d_u1} :=
  @_root_.«CommutativeAlgebraNotes».«Excellence».«isGRing_of_essFiniteType_conditional».{v8_closure_fab540d856bc646d_u0, v8_closure_fab540d856bc646d_u1} (@_root_.«CommutativeAlgebraNotes».«Excellence».«polynomial_isGRing_of_completeLocal».{v8_closure_fab540d856bc646d_u0})
theorem _root_.«CommutativeAlgebraNotes».«Excellence».«quasiExcellent_of_essFiniteType» : _root_.«CommutativeAlgebraNotes».«Excellence».«Specs».«quasiExcellent_of_essFiniteTypeType».{v8_closure_fab540d856bc646d_u0, v8_closure_fab540d856bc646d_u1} :=
  @_root_.«CommutativeAlgebraNotes».«Excellence».«quasiExcellent_of_essFiniteType_conditional».{v8_closure_fab540d856bc646d_u0, v8_closure_fab540d856bc646d_u1} (@_root_.«CommutativeAlgebraNotes».«Excellence».«polynomial_isGRing_of_completeLocal».{v8_closure_fab540d856bc646d_u0})
