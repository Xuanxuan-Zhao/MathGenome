import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.IdealTorsionProperties
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalCohomologyExactSequence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
import Batteries.Tactic.OpenPrivate

/-! The natural long exact sequence of local cohomology. -/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
open Specs.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues (rightValue rightBoundary)
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors (ExactPair)
open AdvancedHomologicalAlgebra.LieHochschildSerre
  (rightValueResolutionIso rightValueResolutionIso_natural resolutionPlus resolutionAugmentation)

open private rightValueBoundaryOnRow from
  MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.LieHochschildSerre

namespace CommutativeAlgebraNotes

namespace LocalCohomologySequence

open Specs.CommutativeAlgebraNotes.LocalCohomologyExactSequence

universe v u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)

local instance : HasDerivedCategory (ModuleCat.{v} R) := HasDerivedCategory.standard _

/-- The comparison from the chosen right-derived functors to the cohomology
of the total right-derived functor. -/
private def toTotal (n : ℕ) :
    localCohomology.{v} I (n : ℤ) ≅ rightValue (idealTorsionFunctor I) n :=
  let F := idealTorsionFunctor.{v} I
  NatIso.ofComponents
    (fun X => (injectiveResolution X).isoRightDerivedObj F n ≪≫
      (rightValueResolutionIso F n (injectiveResolution X)).symm)
    (fun {X Y} f => by
      let P := injectiveResolution X
      let Q := injectiveResolution Y
      let φ : InjectiveResolution.Hom P Q f :=
        ⟨InjectiveResolution.desc f Q P, InjectiveResolution.desc_commutes_zero f Q P⟩
      dsimp only [Iso.trans_hom, Iso.symm_hom]
      apply (cancel_mono (rightValueResolutionIso F n Q).hom).mp
      let U := rightValueResolutionIso F n P
      let V := rightValueResolutionIso F n Q
      change ((F.rightDerived n).map f ≫ ((Q.isoRightDerivedObj F n).hom ≫ V.inv)) ≫ V.hom =
        (((P.isoRightDerivedObj F n).hom ≫ U.inv) ≫ (rightValue F n).map f) ≫ V.hom
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [show (rightValue F n).map f ≫ V.hom = U.hom ≫ _ from
        rightValueResolutionIso_natural F n φ, Iso.inv_hom_id_assoc]
      exact InjectiveResolution.isoRightDerivedObj_hom_naturality f P Q φ.hom
        φ.ι_f_zero_comp_hom_f_zero F n)

private lemma toTotal_comp_resolution {M : ModuleCat.{v} R} (P : InjectiveResolution M)
    (n : ℕ) :
    (toTotal I n).hom.app M ≫ (rightValueResolutionIso (idealTorsionFunctor I) n P).hom =
      (P.isoRightDerivedObj (idealTorsionFunctor I) n).hom := by
  let F := idealTorsionFunctor.{v} I
  let Q := injectiveResolution M
  let φ : InjectiveResolution.Hom Q P (𝟙 M) :=
    ⟨InjectiveResolution.desc (𝟙 M) P Q, InjectiveResolution.desc_commutes_zero _ P Q⟩
  have h₁ := rightValueResolutionIso_natural F n φ
  have h₂ := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 M) Q P φ.hom
    φ.ι_f_zero_comp_hom_f_zero F n
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h₁ h₂
  change ((Q.isoRightDerivedObj F n).hom ≫ (rightValueResolutionIso F n Q).inv) ≫
    (rightValueResolutionIso F n P).hom = (P.isoRightDerivedObj F n).hom
  rw [Category.assoc, h₁, Iso.inv_hom_id_assoc]
  exact h₂.symm

/-- The triangle boundary in the coordinates of the given right-derived functor. -/
private def totalBoundary {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (n : ℕ) :
    (localCohomology I (n : ℤ)).obj S.X₃ ⟶
      (localCohomology I ((n + 1 : ℕ) : ℤ)).obj S.X₁ :=
  (toTotal I n).hom.app S.X₃ ≫ rightBoundary (idealTorsionFunctor I) hS n ≫
    (toTotal I (n + 1)).inv.app S.X₁

private abbrev stalk (C : Type*) [Category* C] [Abelian C] :=
  AdvancedHomologicalAlgebra.GrothendieckEdges.stalkComplex C

local instance (C : Type*) [Category* C] [Abelian C] : (stalk C).PreservesZeroMorphisms where
  map_zero X Y := (CochainComplex.plus C).ι.map_injective
    ((CochainComplex.singleFunctor C 0).map_zero X Y)

local instance {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    (F : C ⥤ D) [F.Additive] : F.mapCochainComplexPlus.PreservesZeroMorphisms where
  map_zero X Y := (CochainComplex.plus D).ι.map_injective
    ((F.mapHomologicalComplex (.up ℤ)).map_zero X.obj Y.obj)

private lemma rightBoundary_on_horseshoe
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (P : InjectiveResolution S.X₁) (Q : InjectiveResolution S.X₃)
    (H : ResolvingRow S P.ι' Q.ι') (hH : H.IsHorseshoe) (n : ℕ) :
    let F := Specs.CommutativeAlgebraNotes.IdealTorsion.idealTorsionFunctor I
    let eP := (rightValueResolutionIso F (n + 1) P) ≪≫ extendResolutionIso I (n + 1) P
    let eQ := (rightValueResolutionIso F n Q) ≪≫ extendResolutionIso I n Q
    rightBoundary F hS n ≫ eP.hom =
      eQ.hom ≫ (mappedShortExact I hH.2.2.2).δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) := by
  let F := Specs.CommutativeAlgebraNotes.IdealTorsion.idealTorsionFunctor I
  let C := ModuleCat.{v} R
  let incl := CochainComplex.Plus.ι C
  let M : CochainComplex.Plus C :=
    ⟨H.middle, hH.2.1.1.imp (fun b hb => (CochainComplex.isStrictlyGE_iff _ b).2 hb)⟩
  let T : ShortComplex (CochainComplex.Plus C) :=
    ShortComplex.mk (X₁ := resolutionPlus P) (X₂ := M) (X₃ := resolutionPlus Q)
      ((CochainComplex.plus C).homMk H.inclusion)
      ((CochainComplex.plus C).homMk H.projection)
      (incl.map_injective H.zero)
  let φ : S.map (stalk C) ⟶ T :=
    ShortComplex.homMk (resolutionAugmentation P)
      ((CochainComplex.plus C).homMk H.augmentation) (resolutionAugmentation Q)
      (incl.map_injective H.comm_left) (incl.map_injective H.comm_right)
  let hT : (T.map incl).ShortExact := hH.1
  let hFT : ((T.map F.mapCochainComplexPlus).map incl).ShortExact :=
    mappedShortExact I hH.2.2.2
  have h := rightValueBoundaryOnRow F hS hT hFT φ n
  dsimp only [Iso.trans_hom, rightValueResolutionIso, extendResolutionIso]
  simp only [Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    AdvancedHomologicalAlgebra.LieHochschildSerre.resolutionEmbedding,
    Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  exact h

private lemma totalBoundary_on_horseshoe
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (P : InjectiveResolution S.X₁) (Q : InjectiveResolution S.X₃)
    (H : ResolvingRow S P.ι' Q.ι') (hH : H.IsHorseshoe) (n : ℕ) :
    totalBoundary I hS n ≫ (resolutionIso I (n + 1) P).hom =
      (resolutionIso I n Q).hom ≫
        (mappedShortExact I hH.2.2.2).δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) := by
  have comparison (m : ℕ) {M : ModuleCat.{v} R} (J : InjectiveResolution M) :
      (toTotal I m).hom.app M ≫ ((rightValueResolutionIso (idealTorsionFunctor I) m J) ≪≫
        extendResolutionIso I m J).hom = (resolutionIso I m J).hom := by
    simp only [resolutionIso, Iso.trans_hom, ← Category.assoc, toTotal_comp_resolution]
  rw [← comparison (n + 1) P, ← comparison n Q]
  simp only [totalBoundary, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [rightBoundary_on_horseshoe I hS P Q H hH n]

private lemma boundary_eq_totalBoundary {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (n : ℕ) :
    boundary I hS (n : ℤ) = totalBoundary I hS n := by
  let P := injectiveResolution S.X₁
  let Q := injectiveResolution S.X₃
  let ex := existsResolvingRow hS P Q
  apply (cancel_mono (resolutionIso I (n + 1) P).hom).mp
  rw [totalBoundary_on_horseshoe I hS P Q ex.choose ex.choose_spec n]
  change ((resolutionIso I n Q).hom ≫ _ ≫ (resolutionIso I (n + 1) P).inv) ≫ _ = _
  simp

/-- The local cohomology boundary, with the ordinary cochain sign. -/
abbrev δ {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact) (q : ℤ) :
    (localCohomology I q).obj S.X₃ ⟶ (localCohomology I (q + 1)).obj S.X₁ :=
  boundary I hS q

theorem δ_on_horseshoe : boundaryOnResolutionType.{v, u} := by
  intro R _ _ I S hS P Q H hH n
  rw [boundary_eq_totalBoundary I hS n]
  exact totalBoundary_on_horseshoe I hS P Q H hH n

/-- The connecting maps commute with morphisms of short exact sequences. -/
theorem δ_naturality : boundaryNaturalType.{v, u} := by
  intro R _ _ I S T hS hT φ q
  cases q with
  | negSucc n => simp [boundary]
  | ofNat n =>
    change (localCohomology I (n : ℤ)).map φ.τ₃ ≫ boundary I hT (n : ℤ) =
      boundary I hS (n : ℤ) ≫ (localCohomology I ((n + 1 : ℕ) : ℤ)).map φ.τ₁
    rw [boundary_eq_totalBoundary I hS n, boundary_eq_totalBoundary I hT n]
    simp only [totalBoundary, Category.assoc, (toTotal I n).hom.naturality_assoc]
    rw [reassoc_of% (AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightConnectingNatural
      _ _ (idealTorsionFunctor I) _ _ hS hT φ n), (toTotal I (n + 1)).inv.naturality]

/-- A map of short exact sequences gives a commuting map of long exact sequences. -/
theorem naturality : naturalityType.{v, u} := by
  intro R _ _ I S T hS hT φ q
  let F := localCohomology I q
  refine ⟨?_, ?_, δ_naturality I hS hT φ q⟩
  · change F.map S.f ≫ F.map φ.τ₂ = F.map φ.τ₁ ≫ F.map T.f
    rw [← F.map_comp, ← F.map_comp, φ.comm₁₂]
  · change F.map S.g ≫ F.map φ.τ₃ = F.map φ.τ₂ ≫ F.map T.g
    rw [← F.map_comp, ← F.map_comp, φ.comm₂₃]

private theorem exactPair_of_iso {C : Type*} [Category* C] [Abelian C]
    {X Y Z X' Y' Z' : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (e₁ : X ≅ X') (e₂ : Y ≅ Y') (e₃ : Z ≅ Z')
    (hf : f ≫ e₂.hom = e₁.hom ≫ f') (hg : g ≫ e₃.hom = e₂.hom ≫ g')
    (h : ExactPair f' g') : ExactPair f g := by
  have hz : f ≫ g = 0 := (cancel_mono e₃.hom).mp (by
    rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc, h.zero, comp_zero, zero_comp])
  exact ⟨hz, ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ hf.symm hg.symm).symm h.exact⟩

private theorem exactPair_of_isZero_middle {C : Type*} [Category* C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : IsZero Y) : ExactPair f g := by
  have hz : f ≫ g = 0 := by rw [h.eq_zero_of_tgt f, zero_comp]
  exact ⟨hz, ShortComplex.exact_of_isZero_X₂ _ h⟩

private theorem isZero_obj_neg (q : ℤ) (hq : q < 0) (M : ModuleCat.{v} R) :
    IsZero ((localCohomology I q).obj M) := by
  rw [localCohomology_of_neg I q hq]
  exact (CategoryTheory.Functor.isZero_iff (0 : ModuleCat.{v} R ⥤ ModuleCat.{v} R)).1
    (isZero_zero _) M

/-- The canonical identification of degree zero with sections supported in the ideal. -/
abbrev degreeZeroIso {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    [PreservesFiniteLimits (idealTorsionFunctor.{v} I)] :
    localCohomology.{v} I 0 ≅ idealTorsionFunctor I :=
  Specs.CommutativeAlgebraNotes.LocalCohomologyExactSequence.degreeZeroIso I

/-- The map from degree-zero local cohomology to the original module. -/
abbrev edge {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    [PreservesFiniteLimits (idealTorsionFunctor.{v} I)] :
    localCohomology.{v} I 0 ⟶ 𝟭 (ModuleCat.{v} R) :=
  Specs.CommutativeAlgebraNotes.LocalCohomologyExactSequence.edge I

theorem degreeZeroUnit_isIso : degreeZeroUnitType.{v, u} := by
  intro R _ _ _ I
  exact inferInstanceAs (IsIso (idealTorsionFunctor.{v} I).toRightDerivedZero)

/-- The first map out of degree zero is injective by left exactness of ideal torsion. -/
theorem mono_zero : monoZeroType.{v, u} := by
  intro R _ _ _ I S hS
  let e := (idealTorsionFunctor.{v} I).rightDerivedZeroIsoSelf
  let := (idealTorsionFunctor_leftExact I S hS).2
  have h : Mono ((localCohomology I 0).map S.f ≫ e.hom.app S.X₂) := by
    change Mono (((idealTorsionFunctor I).rightDerived 0).map S.f ≫ e.hom.app S.X₂)
    rw [e.hom.naturality]
    infer_instance
  exact mono_of_mono _ (e.hom.app S.X₂)

/-- Exactness at each of the three terms in every integer degree. -/
theorem exact : exactSequenceType.{v, u} := by
  intro R _ _ _ I S hS q
  cases q with
  | ofNat n =>
    change ExactPair ((localCohomology I (n : ℤ)).map S.f) ((localCohomology I (n : ℤ)).map S.g) ∧
      ExactPair ((localCohomology I (n : ℤ)).map S.g) (boundary I hS (n : ℤ)) ∧
      ExactPair (boundary I hS (n : ℤ)) ((localCohomology I ((n + 1 : ℕ) : ℤ)).map S.f)
    rw [boundary_eq_totalBoundary I hS n]
    let E := toTotal I n
    let E' := toTotal I (n + 1)
    have hd : totalBoundary I hS n ≫ E'.hom.app S.X₁ =
        E.hom.app S.X₃ ≫ rightBoundary (idealTorsionFunctor I) hS n := by
      simp [totalBoundary, E, E']
    exact ⟨exactPair_of_iso (E.app _) (E.app _) (E.app _)
          (E.hom.naturality S.f) (E.hom.naturality S.g)
          (AdvancedHomologicalAlgebra.UniversalDeltaFunctors.right_exact₂ _ hS n),
      exactPair_of_iso (E.app _) (E.app _) (E'.app _) (E.hom.naturality S.g) hd
        (AdvancedHomologicalAlgebra.UniversalDeltaFunctors.right_exact₃ _ hS n),
      exactPair_of_iso (E.app _) (E'.app _) (E'.app _) hd (E'.hom.naturality S.f)
        (AdvancedHomologicalAlgebra.UniversalDeltaFunctors.right_exact₁ _ hS n)⟩
  | negSucc n =>
    have hz (M : ModuleCat.{v} R) := isZero_obj_neg I (.negSucc n) (Int.negSucc_lt_zero n) M
    refine ⟨exactPair_of_isZero_middle _ _ (hz S.X₂),
      exactPair_of_isZero_middle _ _ (hz S.X₃), ?_⟩
    cases n with
    | zero =>
      have hm := mono_zero I hS
      change ExactPair (0 : _ ⟶ (localCohomology I 0).obj S.X₁) ((localCohomology I 0).map S.f)
      exact ⟨zero_comp, (ShortComplex.exact_iff_mono _ rfl).2 hm⟩
    | succ n =>
      exact exactPair_of_isZero_middle _ _
        (isZero_obj_neg I (Int.negSucc (n + 1) + 1) (by omega) S.X₁)

end

end LocalCohomologySequence

end CommutativeAlgebraNotes
