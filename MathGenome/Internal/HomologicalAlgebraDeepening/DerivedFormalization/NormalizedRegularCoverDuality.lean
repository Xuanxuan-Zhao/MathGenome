import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.NormalizedRegularCoverDuality
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CoinductionComplex
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularCover
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.NormalizedDualizingComplex

namespace DerivedFormalization.NormalizedRegularCoverDuality

open CategoryTheory Opposite
open IsLocalRing (ResidueField maximalIdeal)
open Specs.DerivedFormalization.NormalizedRegularCoverDuality
open Specs.DerivedFormalization.Cochains
  (derivedValue qValue stalkValue derivedStalkValue derivedCohomologyValue cohomologyFactorsValue)
open Specs.DerivedFormalization.DerivedCoinduction (Coinduction)
open Specs.DerivedFormalization.DerivedHomAdjunction (Presentation homComparison)
open Specs.DerivedFormalization.DerivedHomModels (Models rHomValue)
open Specs.DerivedFormalization.DerivedRestriction
  (restrictScalarsComplexValue derivedRestrictScalarsValue derivedRestrictScalarsFactorsValue)
open Specs.DerivedFormalization.CochainModels (internalHomValue)
open Specs.DerivedFormalization.CoinductionComplex (coinduceValue)
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel
  (ShiftedRingResolution BoundedInjectiveResolution shiftedRing)
open CommutativeAlgebraNotes.RegularCoverDualizingModel (regularHomComplexIso)

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- The normalized object attached to a regular cover by derived coinduction. -/
def normalizedObject : normalizedObjectType.{u} := normalizedObjectValue

theorem regularCoverExists : RegularCoverExists.{u} := by
  intro R _ _ _ _
  obtain ⟨S, hS, hreg, hc, f, hlocal, hf, e, he⟩ :=
    CommutativeAlgebraNotes.CoefficientRings.completeRegularCover R
  exact ⟨S, hS, hreg, (maximalIdeal S).spanFinrank,
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).symm, hc, f, hlocal, hf, e, he⟩

theorem residueIdentification : ResidueIdentification.{u} := by
  intro S R _ _ _ _ f _ hf
  let e := RingEquiv.ofBijective (ResidueField.map f)
    (CommutativeAlgebraNotes.localQuotient_residue_bijective f hf)
  exact ⟨e, rfl, (ResidueField.map_comp_residue f).symm⟩

private theorem boundedResolution_isKInjective {S : Type u} [CommRing S] {K}
    (J : BoundedInjectiveResolution (S := S) K) : J.complex.IsKInjective := by
  let := J.isStrictlyGE
  let := J.injective
  exact CochainComplex.isKInjective_of_injective J.complex J.lower

private theorem homComparison_isIso {R : Type u} [CommRing R] (H : Models.{u,u} R)
    {X Y : derivedValue.{u} R} (P : Presentation X) (I : Presentation Y)
    (hI : I.complex.IsKInjective) : IsIso (homComparison H P I) := by
  unfold homComparison
  exact IsIso.comp_isIso'
    (eqToIso (H.hom.obj_eq P.representative.obj I.representative.obj).symm).isIso_hom
    (DerivedHomAdjunction.singleReplacements.{u,u}.2.1 H
      P.representative I.representative (Or.inr hI))

/-- After restriction of scalars the coinduced model is the signed Hom from the
regular target module, with comparison induced by evaluation at one. -/
def restrictionIso {S R : Type u} [CommRing S] [CommRing R]
    (f : S →+* R) (G : Coinduction.{u} f) (HS : Models.{u,u} S) {d : ℕ}
    (J : ShiftedRingResolution S d) :
    (derivedRestrictScalarsValue.{u} f).obj (normalizedObject f G d) ≅
      (rHomValue HS).obj
        (op ((derivedRestrictScalarsValue.{u} f).obj
          ((derivedStalkValue R).obj (ModuleCat.of R R))),
          (qValue S).obj (shiftedRing S d)) := by
  let M := (stalkValue R).obj (ModuleCat.of R R)
  let C := (coinduceValue.{u} f).obj J.complex
  let F := restrictScalarsComplexValue.{u} f
  let L := derivedRestrictScalarsValue.{u} f
  let P : Presentation (L.obj ((derivedStalkValue R).obj (ModuleCat.of R R))) :=
    ⟨F.obj M, ((derivedRestrictScalarsFactorsValue f).app M).symm⟩
  letI := J.quasiIso
  let I : Presentation ((qValue S).obj (shiftedRing S d)) :=
    ⟨J.complex, (asIso ((qValue S).map J.ι)).symm⟩
  have hJ := boundedResolution_isKInjective J
  letI := homComparison_isIso HS P I hJ
  let e : F.obj C ≅ internalHomValue (F.obj M) J.complex :=
    F.mapIso (regularHomComplexIso C) ≪≫ Coinduction.underlyingHomIso.{u} f M J.complex
  exact L.mapIso (modelIso f G J hJ) ≪≫
    (derivedRestrictScalarsFactorsValue f).app C ≪≫ (qValue S).mapIso e ≪≫
      asIso (homComparison HS P I)

private theorem homothety_isIso {S R : Type u} [CommRing S] [CommRing R]
    (f : S →+* R) (G : Coinduction.{u} f) (HR : Models.{u,u} R) {d : ℕ}
    (J : ShiftedRingResolution S d) (hJ : J.complex.IsKInjective)
    (hC : ((coinduceValue.{u} f).obj J.complex).IsKInjective)
    (h : IsIso (Specs.CommutativeAlgebraNotes.DualizingComplexHomothety.derivedHomothety f J)) :
    IsIso (homothety f G HR J hJ) := by
  let P : Presentation (normalizedObjectValue f G d) :=
    ⟨(coinduceValue.{u} f).obj J.complex, (modelIso f G J hJ).symm⟩
  change IsIso (_ ≫ homComparison HR P P)
  exact IsIso.comp_isIso' h (homComparison_isIso HR P P hC)

theorem normalizedDualizing : NormalizedDualizing.{u} := by
  intro S R _ _ _ _ _ _ _ f _ hf d hd G HS HR D k RS
  obtain ⟨hresolved, hmodel⟩ :=
    CommutativeAlgebraNotes.NormalizedDualizingComplex.normalizedDualizingComplex f hf hd
  obtain ⟨J⟩ := hresolved
  obtain ⟨⟨_, hGE, hLE, hC⟩, hfinite, _, ⟨enorm⟩⟩ := hmodel J
  let C := (coinduceValue.{u} f).obj J.complex
  have hJ := boundedResolution_isKInjective J
  let eD := modelIso f G J hJ
  let eH (q : ℤ) : (derivedCohomologyValue R q).obj D ≅ C.homology q :=
    (derivedCohomologyValue R q).mapIso eD ≪≫ (cohomologyFactorsValue R q).app C
  let P : Presentation k :=
    ⟨(stalkValue R).obj (ModuleCat.of R (ResidueField R)), Iso.refl _⟩
  let I : Presentation D := ⟨C, eD.symm⟩
  let := homComparison_isIso HR P I hC
  refine ⟨⟨J⟩, ⟨restrictionIso f G HS J⟩, ?_, ?_,
    ⟨(asIso (homComparison HR P I)).symm ≪≫ enorm⟩, ?_⟩
  · intro q
    let : Module.Finite R (C.homology q) := hfinite q
    exact Module.Finite.of_surjective (eH q).toLinearEquiv.symm.toLinearMap
      (eH q).toLinearEquiv.symm.surjective
  · refine ⟨J.lower, J.upper, ?_⟩
    let : C.IsStrictlyGE J.lower := hGE
    let : C.IsStrictlyLE J.upper := hLE
    intro q hq
    apply CategoryTheory.Limits.IsZero.of_iso _ (eH q)
    rcases hq with hlower | hupper
    · exact C.isZero_of_isGE J.lower q hlower
    · exact C.isZero_of_isLE J.upper q hupper
  · intro J'
    obtain ⟨hbounded, _, hhom, _⟩ := hmodel J'
    have hJ' := boundedResolution_isKInjective J'
    exact ⟨⟨modelIso f G J' hJ'⟩, ⟨hJ', homothety_isIso f G HR J' hJ' hbounded.2.2.2 hhom⟩,
      hbounded⟩

end

end DerivedFormalization.NormalizedRegularCoverDuality
