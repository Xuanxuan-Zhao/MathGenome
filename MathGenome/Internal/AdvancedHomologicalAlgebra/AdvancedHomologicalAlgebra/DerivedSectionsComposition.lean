import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedSectionsComposition
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.RightDerivedComposition
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExactFunctorLocalization

noncomputable section
set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.HigherDirectImageLocalTheory
open AdvancedHomologicalAlgebra.DerivedSectionsTheory
open Specs.AdvancedHomologicalAlgebra.DerivedSectionsComposition
universe u v u' v' w w'

namespace AdvancedHomologicalAlgebra.DerivedSectionsComposition

theorem localDescription : localDescriptionType.{u} :=
  HigherDirectImageLocalDescription.localDescription

theorem injectivePushforwardAcyclic : injectivePushforwardAcyclicType.{u} :=
  HigherDirectImageLocalDescription.injectivePushforwardAcyclic

/-- Underlying pushforward of additive presheaves is precomposition. -/
instance directImagePreservesFiniteLimits {X Y : TopCat.{u}} (R : RingSheaf X)
    (S : RingSheaf Y) (f : X ⟶ Y)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R) :
    PreservesFiniteLimits (directImage R S f φ) := by
  let U := SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (directImage R S f φ ⋙ U) := by
    let e : directImage R S f φ ⋙ U ≅
        (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
          (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map f).op := Iso.refl _
    exact preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves (directImage R S f φ) U

theorem leftExact : leftExactType.{u} := by
  intro X Y R S f φ
  exact ⟨inferInstance, inferInstance⟩

theorem sectionsIdentity : sectionsIdentityType.{u} := by
  intro X Y R S f φ
  exact ⟨DerivedSectionsTheory.sectionsIdentity R S f φ⟩

theorem compositionHypothesis : compositionHypothesisType.{u} := by
  intro X Y R S f φ
  letI := HasDerivedCategory.standard (Modules S)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing S ⊤))
  intro I hI
  apply (AcyclicTermComparison.rightVanishing (Modules S)
    (ModuleCat.{u} (sectionRing S ⊤)) (globalSections S) _).mpr
  intro n
  exact HigherDirectImageLocalDescription.injectivePushforwardAcyclic R S f φ I hI ⊤ n

section Exact
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- HA-R10 with the canonical HA-R06 comparison data. -/
def exactDerivedIdentification : F.rightDerivedFunctorPlus ≅
    ExactFunctorLocalization.plusFunctor F :=
  Classical.choose ((ExactFunctorLocalization.boundedDescent F).rightIdentification
    { functor := F.rightDerivedFunctorPlus
      unit := F.rightDerivedFunctorPlusUnith
      universal := TotalRightDerivedFunctor.universal A B F })

private lemma exactDerivedIdentification_fac (K : HomotopyCategory.Plus A) :
    F.rightDerivedFunctorPlusUnith.app K ≫
      (exactDerivedIdentification F).hom.app (DerivedCategory.Plus.Qh.obj K) =
    (ExactFunctorLocalization.plusComparison F).inv.app K := by
  have h := (Classical.choose_spec
    ((ExactFunctorLocalization.boundedDescent F).rightIdentification
      { functor := F.rightDerivedFunctorPlus
        unit := F.rightDerivedFunctorPlusUnith
        universal := TotalRightDerivedFunctor.universal A B F })).1
  exact congrArg (fun τ => τ.app K) h

lemma exactUnitIso (K : HomotopyCategory.Plus A) :
    IsIso (F.rightDerivedFunctorPlusUnith.app K) := by
  apply (isIso_comp_right_iff _ ((exactDerivedIdentification F).hom.app
    (DerivedCategory.Plus.Qh.obj K))).mp
  rw [exactDerivedIdentification_fac]
  infer_instance

private lemma exactDerivedIdentification_on_complex (K : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      (((isoWhiskerRight (exactDerivedIdentification F) DerivedCategory.Plus.ι) ≪≫
        ExactFunctorLocalization.plusRestriction F).hom.app (DerivedCategory.Plus.Q.obj K)) =
      F.mapDerivedCategoryFactors.inv.app K.obj := by
  let L := (HomotopyCategory.Plus.quotient A).obj K
  have hι := DerivedCategory.Plus.ι.congr_map (exactDerivedIdentification_fac F L)
  rw [Functor.map_comp] at hι
  have hUnit : F.rightDerivedFunctorPlusUnit.app K = F.rightDerivedFunctorPlusUnith.app L := by
    rw [Functor.rightDerivedFunctorPlusUnit_app]
    change 𝟙 _ ≫ DerivedCategory.Plus.Qh.map (𝟙 _) ≫
      F.rightDerivedFunctorPlusUnith.app L ≫ F.rightDerivedFunctorPlus.map (𝟙 _) = _
    simp
  have hFactor : F.mapDerivedCategoryFactorsh.hom.app L.obj =
      F.mapDerivedCategoryFactors.hom.app K.obj := by
    have hK := F.mapDerivedCategoryFactorsh_hom_app K.obj
    change F.mapDerivedCategoryFactorsh.hom.app L.obj =
      F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj K.obj)) ≫
      F.mapDerivedCategoryFactors.hom.app K.obj ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) at hK
    rw [map_id, map_id, Category.id_comp, Category.id_comp] at hK
    exact hK.trans (Category.comp_id _)
  have hIso : F.mapDerivedCategoryFactorsh.app L.obj =
      F.mapDerivedCategoryFactors.app K.obj := Iso.ext hFactor
  calc
    _ = F.mapDerivedCategoryFactorsh.inv.app L.obj := by
      rw [hUnit]
      change _ ≫ (DerivedCategory.Plus.ι.map
        ((exactDerivedIdentification F).hom.app (DerivedCategory.Plus.Qh.obj L)) ≫ 𝟙 _) = _
      rw [Category.comp_id]
      exact hι
    _ = _ := congrArg Iso.inv hIso

omit [EnoughInjectives A] in
private lemma cohomologyIso_on_complex (n : ℤ) (K : CochainComplex A ℤ) :
    (ExactFunctorLocalization.cohomologyIso F n).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor B n).map (F.mapDerivedCategoryFactors.hom.app K) ≫
      (DerivedCategory.homologyFunctorFactors B n).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      ((K.sc n).mapHomologyIso F).hom ≫
      F.map ((DerivedCategory.homologyFunctorFactors A n).inv.app K) := by
  let ff := Localization.fullyFaithfulWhiskeringLeft (DerivedCategory.Q (C := A))
    (HomologicalComplex.quasiIso A (.up ℤ)) B
  let e := (associator _ _ _).symm ≪≫
    isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor B n) ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors B n) ≪≫
    ExactFunctorLocalization.complexCohomologyIso F n ≪≫
    isoWhiskerRight (DerivedCategory.homologyFunctorFactors A n).symm F ≪≫
    associator _ _ _
  change (ff.preimage e.hom).app (DerivedCategory.Q.obj K) = _
  have h := congrArg (fun τ => NatTrans.app τ K) (ff.map_preimage e.hom)
  change (ff.preimage e.hom).app (DerivedCategory.Q.obj K) = e.hom.app K at h
  simpa only [e, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerLeft_app,
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc, whiskerRight_app, ExactFunctorLocalization.complexCohomologyIso,
    NatIso.ofComponents_hom_app] using h

end Exact

section Sections
variable {X Y : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (f : X ⟶ Y)
  (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R)

attribute [local instance] HasDerivedCategory.standard

local notation "D" => directImage R S f φ
local notation "G" => globalSections S
local notation "H" => globalSections R
local notation "T" => scalarRestriction R S f φ

private def restrictionData : ScalarRestrictionData R S f φ where
  termwise := isoWhiskerRight (exactDerivedIdentification T) _ ≪≫
    ExactFunctorLocalization.plusRestriction T
  termwise_on_complex := exactDerivedIdentification_on_complex T
  homology := ExactFunctorLocalization.cohomologyIso T
  homology_on_complex := cohomologyIso_on_complex T

theorem exactRestriction : exactRestrictionType.{u} := by
  intro X Y R S f φ
  exact ⟨inferInstance, inferInstance, ⟨restrictionData R S f φ⟩⟩

/-- The sections identity applied to complexes in the bounded-below categories. -/
private def complexSectionsIso :
    (D ⋙ G).mapCochainComplexPlus ≅ (H).mapCochainComplexPlus ⋙ (T).mapCochainComplexPlus :=
  ((CochainComplex.plus _).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (CochainComplex.Plus.ι (Modules R))
      (mapHomologicalComplexCompIso
        (DerivedSectionsTheory.sectionsIdentity R S f φ).symm (.up ℤ)).symm)

/-- Before localization, the comparison is the sections identity followed by
the exact restriction unit and the image of the sections unit. -/
private def sectionsComparisonInput :
    (D ⋙ G).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ ((H).rightDerivedFunctorPlus ⋙ (T).rightDerivedFunctorPlus) :=
  whiskerRight (complexSectionsIso R S f φ).hom _ ≫
    (associator _ _ _).hom ≫
    whiskerLeft (H).mapCochainComplexPlus (T).rightDerivedFunctorPlusUnit ≫
    (associator _ _ _).inv ≫
    whiskerRight (H).rightDerivedFunctorPlusUnit (T).rightDerivedFunctorPlus ≫
    (associator _ _ _).hom

private def sectionsComparison :
    (D ⋙ G).rightDerivedFunctorPlus ⟶ (H).rightDerivedFunctorPlus ⋙ (T).rightDerivedFunctorPlus :=
  (D ⋙ G).rightDerivedFunctorPlus.rightDerivedDesc
    (D ⋙ G).rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso (Modules R))
    _ (sectionsComparisonInput R S f φ)

private lemma sectionsComparison_fac (I : CochainComplex.Plus (Modules R)) :
    (D ⋙ G).rightDerivedFunctorPlusUnit.app I ≫
      (sectionsComparison R S f φ).app (DerivedCategory.Plus.Q.obj I) =
    DerivedCategory.Plus.Q.map ((complexSectionsIso R S f φ).hom.app I) ≫
      (T).rightDerivedFunctorPlusUnit.app ((H).mapCochainComplexPlus.obj I) ≫
      (T).rightDerivedFunctorPlus.map ((H).rightDerivedFunctorPlusUnit.app I) := by
  have h := (D ⋙ G).rightDerivedFunctorPlus.rightDerived_fac
    (D ⋙ G).rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso (Modules R))
    _ (sectionsComparisonInput R S f φ)
  simpa only [sectionsComparison, sectionsComparisonInput, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using congrArg (fun τ => τ.app I) h

private lemma sectionsComparison_isIso : IsIso (sectionsComparison R S f φ) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro A
  obtain ⟨a, K, hK, hb, ⟨e⟩⟩ :=
    InjectiveComplexReplacement.plusRepresentative (Modules R) A
  let I : CochainComplex.Plus (Modules R) := ⟨K, a, hb⟩
  let e' : A ≅ DerivedCategory.Plus.Q.obj I :=
    DerivedCategory.TStructure.t.plus.fullyFaithfulι.preimageIso e
  apply (NatTrans.isIso_app_iff_of_iso (sectionsComparison R S f φ) e').mpr
  let := hK
  have : IsIso ((D ⋙ G).rightDerivedFunctorPlusUnit.app I) := by
    simp only [Functor.rightDerivedFunctorPlusUnit_app]
    infer_instance
  have : IsIso ((H).rightDerivedFunctorPlusUnit.app I) := by
    simp only [Functor.rightDerivedFunctorPlusUnit_app]
    infer_instance
  rw [← isIso_comp_left_iff ((D ⋙ G).rightDerivedFunctorPlusUnit.app I),
    sectionsComparison_fac]
  have : IsIso ((T).rightDerivedFunctorPlusUnit.app ((H).mapCochainComplexPlus.obj I)) := by
    let K := (H).mapCochainComplexPlus.obj I
    letI := exactUnitIso T ((HomotopyCategory.Plus.quotient _).obj K)
    simp only [Functor.rightDerivedFunctorPlusUnit_app]
    infer_instance
  infer_instance

private def sectionsData : SectionsDerivedData R S f φ := by
  letI := sectionsComparison_isIso R S f φ
  refine { restriction := restrictionData R S f φ
           comparison := asIso (sectionsComparison R S f φ)
           on_injective := ?_
           composition_isIso := ?_ }
  · intro I _
    dsimp only [asIso_hom]
    rw [← Category.assoc, ← Functor.map_comp, sectionsComparison_fac]
    simp only [Functor.map_comp, Category.assoc]
    have h := (restrictionData R S f φ).termwise.hom.naturality
      ((H).rightDerivedFunctorPlusUnit.app I)
    simp only [Functor.comp_map, Functor.comp_obj] at h
    have h' := congrArg (fun k => k ≫ (T).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map ((H).rightDerivedFunctorPlusUnit.app I)))
      ((restrictionData R S f φ).termwise_on_complex ((H).mapCochainComplexPlus.obj I))
    simp only [Category.assoc] at h'
    erw [h, h']
    rfl
  · letI := (RightDerivedComposition.comparisonIsoIff (Modules R) (Modules S)
      (ModuleCat.{u} (sectionRing S ⊤)) D G).mpr (compositionHypothesis R S f φ)
    exact NatIso.isIso_of_isIso_app _

end Sections

theorem derivedComposition : derivedCompositionType.{u} := by
  intro X Y R S f φ
  exact ⟨sectionsData R S f φ⟩

end AdvancedHomologicalAlgebra.DerivedSectionsComposition
