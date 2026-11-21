import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FlasqueAcyclicity
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveComplexReplacement
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExtShiftedHom
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.SheafCohomology
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
universe u

namespace AdvancedHomologicalAlgebra.SheafCohomology

section ResolutionModel

open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  [EnoughInjectives A]

theorem resolutionModelMap_isIso (F : A ⥤ B) [F.Additive]
    {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hι : QuasiIso ι)
    (hI : ∀ q : ℤ, rightAcyclicValue F (I.X q)) (n : ℕ) :
    IsIso (resolutionModelMap F ι hι n) := by
  let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  haveI : IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj K)) :=
    AcyclicTermComparison.rightComparison_homotopy F _ hI
  haveI : IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
    simp only [Functor.rightDerivedFunctorPlusUnit_app]
    infer_instance
  unfold resolutionModelMap
  infer_instance

/-- The canonical augmented-model map is functorial for a square commuting
after localization. -/
theorem resolutionModelMap_naturality (F : A ⥤ B) [F.Additive]
    {M N : A} {I J : CochainComplex A ℤ} [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hι : QuasiIso ι)
    (κ : (CochainComplex.singleFunctor A 0).obj N ⟶ J) (hκ : QuasiIso κ)
    (f : M ⟶ N) (g : I ⟶ J)
    (h : DerivedCategory.Q.map (ι ≫ g) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor A 0).map f ≫ κ)) (n : ℕ) :
    resolutionModelMap F ι hι n ≫ (rightValue F n).map f =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ) ≫
        resolutionModelMap F κ hκ n := by
  let S : A ⥤ CochainComplex.Plus A :=
    (CochainComplex.plus A).lift (CochainComplex.singleFunctor A 0)
      (fun _ ↦ ⟨0, inferInstance⟩)
  let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let L : CochainComplex.Plus A := ⟨J, 0, inferInstance⟩
  let i : S.obj M ⟶ K := ObjectProperty.homMk ι
  let j : S.obj N ⟶ L := ObjectProperty.homMk κ
  let m : K ⟶ L := ObjectProperty.homMk g
  let Q := DerivedCategory.Plus.Q (C := A)
  let Q' := DerivedCategory.Plus.Q (C := B)
  let RF := F.rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let α := F.rightDerivedFunctorPlusUnit
  let F' := F.mapCochainComplexPlus
  let β := DerivedCategory.homologyFunctorFactors B (n : ℤ)
  haveI : IsIso (Q.map i) :=
    Localization.inverts Q (CochainComplex.Plus.quasiIso A) i hι
  haveI : IsIso (Q.map j) :=
    Localization.inverts Q (CochainComplex.Plus.quasiIso A) j hκ
  have hq : Q.map i ≫ Q.map m = Q.map (S.map f) ≫ Q.map j := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [← Functor.map_comp] at h ⊢
    exact h
  have hq' : inv (Q.map i) ≫ Q.map (S.map f) = Q.map m ≫ inv (Q.map j) := by
    apply (cancel_mono (Q.map j)).mp
    simp [Category.assoc, ← hq]
  have hn : α.app K ≫ RF.map (Q.map m) = Q'.map (F'.map m) ≫ α.app L :=
    α.naturality m |>.symm
  have hb : HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ) ≫
      β.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      β.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫ H.map (Q'.map (F'.map m)) :=
    β.inv.naturality ((F.mapHomologicalComplex (.up ℤ)).map g)
  change (β.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫ H.map (α.app K ≫ RF.map (inv (Q.map i)))) ≫
      H.map (RF.map (Q.map (S.map f))) = _ ≫
    β.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫ H.map (α.app L ≫ RF.map (inv (Q.map j)))
  rw [Category.assoc, ← H.map_comp, Category.assoc, ← RF.map_comp, hq', RF.map_comp, ← Category.assoc, hn]
  simp only [H.map_comp, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ H.map (α.app L) ≫ H.map (RF.map (inv (Q.map j)))) hb.symm

open private mappedStalkIso from MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

/-- Compute the degree-zero unit of a right derived functor on the stalk model. -/
theorem rightDegreeZeroUnit_stalk (F : A ⥤ B) [F.Additive] (M : A) :
    (rightDegreeZeroUnit F).app M =
      ((HomologicalComplex.homologyFunctor B (.up ℤ) 0).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M) ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      resolutionModelMap F (𝟙 ((CochainComplex.singleFunctor A 0).obj M))
        (by infer_instance) 0 := by
  let K : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
  let L : CochainComplex.Plus B := ⟨(CochainComplex.singleFunctor B 0).obj (F.obj M), 0,
    inferInstance⟩
  let g := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M
  let g' : L ⟶ F.mapCochainComplexPlus.obj K := ObjectProperty.homMk g
  let QB := DerivedCategory.Plus.Q (C := B)
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let β := DerivedCategory.homologyFunctorFactors B 0
  have hmap : (mappedStalkIso F).inv.app M = DerivedCategory.Q.map g := by
    unfold mappedStalkIso
    simp [g, DerivedCategory.singleFunctorIsoCompQ,
      DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      HomotopyCategory.singleFunctorPostcompQuotientIso,
      HomotopyCategory.singleFunctorsPostcompQuotientIso, Functor.mapHomotopyCategoryFactors]
    rfl
  have hsource : (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app M = 𝟙 _ := by
    rfl
  have hunit : F.rightDerivedFunctorPlusUnit.app K =
      F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj M) := by
    simp only [Functor.rightDerivedFunctorPlusUnit_app]
    have hB : (DerivedCategory.Plus.quotientCompQhIso B).inv.app
        (F.mapCochainComplexPlus.obj K) = 𝟙 _ := rfl
    have hA : (DerivedCategory.Plus.quotientCompQhIso A).hom.app K = 𝟙 _ := rfl
    have hF : F.quotientCompMapHomotopyCategoryPlusIso.inv.app K = 𝟙 _ := rfl
    simp [hA, hB, hF]
    rfl
  have hm : resolutionModelMap F (𝟙 K.obj) (by infer_instance) 0 =
      β.inv.app (F.mapCochainComplexPlus.obj K).obj ≫ H.map
        (F.rightDerivedFunctorPlusUnit.app K) := by
    unfold resolutionModelMap
    change β.inv.app (F.mapCochainComplexPlus.obj K).obj ≫ H.map
      (F.rightDerivedFunctorPlusUnit.app K ≫ F.rightDerivedFunctorPlus.map
        (inv ((DerivedCategory.Plus.Q (C := A)).map (𝟙 K)))) = _
    simp
  rw [hm, hunit]
  simp only [rightDegreeZeroUnit, NatTrans.comp_app, isoWhiskerLeft_inv, whiskerLeft_app,
    whiskerRight_app, Functor.map_comp, associator_inv_app, Category.id_comp, Iso.app_inv,
    Functor.mapIso_inv, Iso.trans_inv]
  dsimp only [FullyFaithful.whiskeringRight, FullyFaithful.preimageIso]
  simp only [Iso.symm_hom, hmap, hsource]
  have hpre : (FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := B))).preimage
      (DerivedCategory.Q.map g) = QB.map g' := by
    apply DerivedCategory.Plus.ι.map_injective
    rw [FullyFaithful.map_preimage]
    rfl
  rw [hpre]
  have hpreSource : (FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := A))).preimage
      (X := (DerivedCategory.Plus.singleFunctor A 0).obj M)
      (Y := (DerivedCategory.Plus.singleFunctor A 0).obj M) (𝟙 ((HomotopyCategory.singleFunctor A 0 ⋙ DerivedCategory.Qh).obj M)) =
      𝟙 ((DerivedCategory.Plus.singleFunctor A 0).obj M) := by
    apply DerivedCategory.Plus.ι.map_injective
    rw [FullyFaithful.map_preimage, CategoryTheory.Functor.map_id]
    rfl
  erw [hpreSource]
  let S := (DerivedCategory.Plus.singleFunctor A 0).obj M
  let u := F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj M)
  change (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app (F.obj M) ≫
      H.map (QB.map g') ≫ H.map u ≫ H.map (F.rightDerivedFunctorPlus.map (𝟙 S)) = _
  have hid : H.map (F.rightDerivedFunctorPlus.map (𝟙 S)) = 𝟙 _ := by
    rw [F.rightDerivedFunctorPlus.map_id, H.map_id]
  erw [hid, Category.comp_id]
  have hβ : (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app (F.obj M) =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
        β.inv.app L.obj := by
    simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
      HomologicalComplex.homologyFunctorSingleIso, β, L]
  rw [hβ]
  have hn : HomologicalComplex.homologyMap g 0 ≫
      β.inv.app (F.mapCochainComplexPlus.obj K).obj =
        β.inv.app L.obj ≫ H.map (QB.map g') := β.inv.naturality g
  simp only [Category.assoc, ← reassoc_of% hn]
  rfl

end ResolutionModel

section ResolutionLift

open HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

/-- A monic quasi-isomorphism into a bounded below complex has the lifting
property against the zero map out of a bounded below complex of injectives. -/
lemma injectiveResolutionLift {A : Type*} [Category A] [Abelian A]
    {K I J : CochainComplex A ℤ} [K.IsStrictlyGE 0] [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (i : K ⟶ I) [Mono i] [QuasiIso i] (j : K ⟶ J)
    (hJ : ∀ q, Injective (J.X q)) :
    ∃ g : I ⟶ J, i ≫ g = j := by
  let K' : CochainComplex.Plus A := ⟨K, 0, inferInstance⟩
  let I' : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let J' : CochainComplex.Plus A := ⟨J, 0, inferInstance⟩
  let i' : K' ⟶ I' := ObjectProperty.homMk i
  let j' : K' ⟶ J' := ObjectProperty.homMk j
  have : Mono i' := (CochainComplex.Plus.mono_iff i').2 (show Mono i from inferInstance)
  have : WeakEquivalence i' :=
    (CochainComplex.Plus.modelCategoryQuillen.weakEquivalence_iff i').2 (show QuasiIso i from inferInstance)
  have : IsFibrant J' :=
    (CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff J').2 hJ
  let sq : CommSq j' i' (terminal.from J') (terminal.from I') := ⟨Subsingleton.elim _ _⟩
  exact ⟨sq.lift.hom, congrArg (fun f ↦ f.hom) sq.fac_left⟩

end ResolutionLift

def cohomology : cohomologyType.{u} := cohomologyValue

theorem resolution : resolutionType.{u} := by
  intro X R U M I hb ι hι hI n
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R U))
  exact ClassicalDerivedValues.rightComputation _ _ _ M I ι hι hI n

theorem zero : zeroType.{u} := by
  intro X R U
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R U))
  letI := ClassicalDerivedValues.rightZero _ _ (SheafOfModules.evaluation R (op U))
  exact ⟨(asIso (rightDegreeZeroUnit (SheafOfModules.evaluation R (op U)))).symm, rfl⟩

theorem longExact : longExactType.{u} := by
  intro X R U
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R U))
  exact UniversalDeltaFunctors.rightDelta _ _ (SheafOfModules.evaluation R (op U))

theorem flasque : flasqueType.{u} := by
  intro X R U M hM n
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R U))
  exact FlasqueAcyclicity.flasqueAcyclic R U M hM n

def sectionsRestriction : sectionsRestrictionType.{u} := sectionsRestrictionValue

section StalkComparison

open HomologicalComplex

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B]
  [Abelian A] [Abelian A'] [Abelian B]

/-- Homology of the termwise section identification in degree zero of a stalk. -/
theorem homology_stalk_comparison (J : A ⥤ A') (G : A' ⥤ B) (F : A ⥤ B)
    [J.Additive] [G.Additive] [F.Additive] (e : J ⋙ G ≅ F) (M : A) :
    ((homologyFunctor B (.up ℤ) 0).mapIso
        ((singleMapHomologicalComplex F (.up ℤ) 0).app M) ≪≫
        singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      homologyMap ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).inv.app
        ((CochainComplex.singleFunctor A 0).obj M)) 0 ≫
      homologyMap ((G.mapHomologicalComplex (.up ℤ)).map
        ((singleMapHomologicalComplex J (.up ℤ) 0).hom.app M)) 0 =
    e.inv.app M ≫ ((homologyFunctor B (.up ℤ) 0).mapIso
        ((singleMapHomologicalComplex G (.up ℤ) 0).app (J.obj M)) ≪≫
        singleObjHomologySelfIso (.up ℤ) 0 (G.obj (J.obj M))).inv := by
  let c := ComplexShape.up ℤ
  let S := (CochainComplex.singleFunctor A 0).obj M
  let a := (singleMapHomologicalComplex F c 0).inv.app M
  let b := (Functor.mapHomologicalComplexCompIso e c).inv.app S
  let d := (G.mapHomologicalComplex c).map ((singleMapHomologicalComplex J c 0).hom.app M)
  let a' := (singleMapHomologicalComplex G c 0).inv.app (J.obj M)
  let x := e.inv.app M
  have h : a ≫ b ≫ d = (CochainComplex.singleFunctor B 0).map x ≫ a' := by
    ext q
    by_cases hq : q = 0
    · subst q
      simp only [a, b, d, a', x, S, HomologicalComplex.comp_f, c,
        singleMapHomologicalComplex_hom_app_self, singleMapHomologicalComplex_inv_app_self,
        Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
        Functor.map_comp, Category.assoc]
      change _ = (((HomologicalComplex.single B (.up ℤ) 0).map (e.inv.app M)).f 0) ≫ _
      rw [single_map_f_self]
      have hn := e.inv.naturality (singleObjXSelf (.up ℤ) 0 M).inv
      change F.map (singleObjXSelf (.up ℤ) 0 M).inv ≫ _ =
        e.inv.app M ≫ G.map (J.map (singleObjXSelf (.up ℤ) 0 M).inv) at hn
      simp only [reassoc_of% hn, ← G.map_comp, comp_obj]
      rw [← J.map_comp_assoc, Iso.inv_hom_id, J.map_id]
      simp
    · apply (isZero_single_obj_X c 0 (F.obj M) q hq).eq_of_src
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
  change (singleObjHomologySelfIso c 0 (F.obj M)).inv ≫ homologyMap a 0 ≫
      homologyMap b 0 ≫ homologyMap d 0 =
    x ≫ (singleObjHomologySelfIso c 0 (G.obj (J.obj M))).inv ≫ homologyMap a' 0
  rw [← homologyMap_comp b d, ← homologyMap_comp a (b ≫ d), h, homologyMap_comp,
    singleObjHomologySelfIso_inv_naturality_assoc]
  rfl

end StalkComparison

section DegreeZeroComparison

open HomologicalComplex

attribute [local instance] HasDerivedCategory.standard

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B]
  [Abelian A] [Abelian A'] [Abelian B] [EnoughInjectives A] [EnoughInjectives A']

theorem degreeZero_comparison_of_stalk (J : A ⥤ A') (G : A' ⥤ B) (F : A ⥤ B)
    [J.Additive] [G.Additive] [F.Additive] (e : J ⋙ G ≅ F) (M : A)
    (t : (rightValue F 0).obj M ⟶ (rightValue G 0).obj (J.obj M))
    (hJ : QuasiIso ((singleMapHomologicalComplex J (.up ℤ) 0).inv.app M))
    (h : resolutionModelMap F (𝟙 ((CochainComplex.singleFunctor A 0).obj M))
        (by infer_instance) 0 ≫ t =
      homologyMap ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).inv.app
        ((CochainComplex.singleFunctor A 0).obj M)) 0 ≫
      resolutionModelMap G
        (I := (J.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj M))
        ((singleMapHomologicalComplex J (.up ℤ) 0).inv.app M) hJ 0) :
    (rightDegreeZeroUnit F).app M ≫ t =
      e.inv.app M ≫ (rightDegreeZeroUnit G).app (J.obj M) := by
  let c := ComplexShape.up ℤ
  let S : CochainComplex A' ℤ := (CochainComplex.singleFunctor A' 0).obj (J.obj M)
  let j := singleMapHomologicalComplex J c 0
  have hj : DerivedCategory.Q.map (j.inv.app M ≫ j.hom.app M) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor A' 0).map (𝟙 (J.obj M)) ≫ 𝟙 S) := by
    simp [j, S]
    rfl
  let K : CochainComplex A' ℤ :=
    (J.mapHomologicalComplex c).obj ((CochainComplex.singleFunctor A 0).obj M)
  have hb : K.IsStrictlyGE 0 := by dsimp [K, c]; infer_instance
  letI := hb
  have hm := resolutionModelMap_naturality G (I := K) (j.inv.app M) hJ (𝟙 S) (by infer_instance)
    (𝟙 (J.obj M)) (j.hom.app M) hj 0
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hm
  rw [rightDegreeZeroUnit_stalk, rightDegreeZeroUnit_stalk, Category.assoc, h]
  erw [hm]
  simpa only [Category.assoc] using! congrArg
    (fun k ↦ k ≫ resolutionModelMap G (𝟙 S) (by infer_instance) 0)
    (homology_stalk_comparison J G F e M)

end DegreeZeroComparison

section OpenRestriction

open CategoryTheory.Pretriangulated
set_option maxHeartbeats 400000

section RestrictionDerived

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B]
    [Abelian A] [Abelian A'] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B]
    (J : A ⥤ A') [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]

private def exactDerivedPlus : DerivedCategory.Plus A ⥤ DerivedCategory.Plus A' :=
  ObjectProperty.lift _ (DerivedCategory.Plus.ι ⋙ J.mapDerivedCategory) (by
    intro K
    have : (DerivedCategory.Plus.Q (C := A)).EssSurj :=
      Functor.essSurj_of_iso (DerivedCategory.Plus.quotientCompQhIso A)
    obtain ⟨L, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (DerivedCategory.Plus.Q (C := A)) K
    obtain ⟨n, hn⟩ := (J.mapCochainComplexPlus.obj L).property
    letI := hn
    letI : DerivedCategory.TStructure.t.IsGE
        ((J.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).obj L.obj) n :=
      inferInstanceAs ((DerivedCategory.Q.obj (J.mapCochainComplexPlus.obj L).obj).IsGE n)
    exact ⟨n, DerivedCategory.TStructure.t.isGE_of_iso
      (J.mapDerivedCategoryFactors.symm.app L.obj ≪≫
        (DerivedCategory.Plus.ι ⋙ J.mapDerivedCategory).mapIso e) n⟩)

private instance : (exactDerivedPlus J).CommShift ℤ :=
  ObjectProperty.commShiftLift ..

private def exactDerivedPlusFactors :
    DerivedCategory.Plus.Q ⋙ exactDerivedPlus J ≅ J.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _ (J.mapDerivedCategoryFactors.app K.obj))
    (by intro K L f; apply DerivedCategory.Plus.ι.map_injective;
        exact J.mapDerivedCategoryFactors_hom_naturality f.hom)

private instance : NatTrans.CommShift (exactDerivedPlusFactors J).hom ℤ := by
  refine NatTrans.CommShift.of_comp_faithful DerivedCategory.Plus.ι ?_
  have h : whiskerRight (exactDerivedPlusFactors J).hom DerivedCategory.Plus.ι =
      (associator ..).hom ≫
        whiskerLeft _ (ObjectProperty.liftCompιIso _ _ _).hom ≫ (associator ..).inv ≫
        whiskerRight (DerivedCategory.Plus.QCompιIso A).hom _ ≫ (associator ..).hom ≫
        whiskerLeft (CochainComplex.Plus.ι A) J.mapDerivedCategoryFactors.hom ≫
        (associator ..).inv ≫ whiskerRight J.mapCochainComplexPlusCompι.inv _ ≫
        (associator ..).hom ≫ whiskerLeft _ (DerivedCategory.Plus.QCompιIso A').inv ≫
        (associator ..).inv := by
    apply NatTrans.ext
    funext L
    change J.mapDerivedCategoryFactors.hom.app L.obj = _
    simp [ObjectProperty.liftCompιIso]
    erw [J.mapDerivedCategory.map_id, Category.id_comp, Category.id_comp]
  rw [h]
  infer_instance

private def exactDerivedPlusSingle :
    DerivedCategory.Plus.singleFunctor A 0 ⋙ exactDerivedPlus J ≅
      J ⋙ DerivedCategory.Plus.singleFunctor A' 0 :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    ((J.mapDerivedCategorySingleFunctor 0).app M))
    (by intro M N f; apply DerivedCategory.Plus.ι.map_injective;
        exact (J.mapDerivedCategorySingleFunctor 0).hom.naturality f)

private def mapPlusCompIso (F : A' ⥤ B) [F.Additive] (G : A ⥤ B) [G.Additive]
    (e : J ⋙ F ≅ G) :
    J.mapCochainComplexPlus ⋙ F.mapCochainComplexPlus ≅ G.mapCochainComplexPlus :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _
    ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).app K.obj))
    (by intro K L f; apply (CochainComplex.Plus.ι B).map_injective;
        exact (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.naturality f.hom)

private instance (F : A' ⥤ B) [F.Additive] (G : A ⥤ B) [G.Additive] (e : J ⋙ F ≅ G) :
    NatTrans.CommShift (mapPlusCompIso J F G e).hom ℤ := by
  refine NatTrans.CommShift.of_comp_faithful (CochainComplex.Plus.ι B) ?_
  have h : whiskerRight (mapPlusCompIso J F G e).hom (CochainComplex.Plus.ι B) =
      (associator ..).hom ≫
        whiskerLeft _ F.mapCochainComplexPlusCompι.hom ≫ (associator ..).inv ≫
        whiskerRight J.mapCochainComplexPlusCompι.hom _ ≫ (associator ..).hom ≫
        whiskerLeft (CochainComplex.Plus.ι A) (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom ≫
        G.mapCochainComplexPlusCompι.inv := by
    apply NatTrans.ext
    funext L
    simp [mapPlusCompIso, Functor.mapCochainComplexPlusCompι]
  rw [h]
  infer_instance

private lemma unit_isIso_of_injective
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex.Plus C)
    (hK : ∀ i : ℤ, Injective (K.obj.X i)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  let L : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty _ K.obj hK
  obtain ⟨n, hn⟩ := K.property
  have hL : L.IsStrictlyGE n := by
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι _)]
    exact hn
  let L' : CochainComplex.Plus (InjectiveObject C) := ⟨L, n, hL⟩
  let K' := (InjectiveObject.ι C).mapCochainComplexPlus.obj L'
  have h : K' = K := ObjectProperty.FullSubcategory.ext rfl
  rw [← h]
  infer_instance

variable [EnoughInjectives A] [EnoughInjectives A']
    (F : A' ⥤ B) [F.Additive] (G : A ⥤ B) [G.Additive] (e : J ⋙ F ≅ G)

private def restrictionDerivedUnit :
    J.mapCochainComplexPlus ⋙ F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ exactDerivedPlus J ⋙ F.rightDerivedFunctorPlus :=
  whiskerLeft J.mapCochainComplexPlus F.rightDerivedFunctorPlusUnit ≫
    (associator ..).inv ≫ whiskerRight (exactDerivedPlusFactors J).inv _ ≫ (associator ..).hom

private instance : NatTrans.CommShift (restrictionDerivedUnit J F) ℤ := by
  dsimp only [restrictionDerivedUnit]
  infer_instance

private lemma restrictionDerivedUnit_isDerived
    (hJ : ∀ M : A, Injective M → Injective (J.obj M)) :
    (exactDerivedPlus J ⋙ F.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (restrictionDerivedUnit J F) (CochainComplex.Plus.quasiIso A) := by
  have h : (CochainComplex.Plus.localizerMorphism A).Derives
      (J.mapCochainComplexPlus ⋙ F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
    intro K L f hf
    simp only [Functor.comp_map]
    rw [HomotopyCategory.Plus.inverseImage_quasiIso_mapCochainComplexPlus_injectiveObjectι] at hf
    dsimp
    apply Localization.inverts _ (CochainComplex.Plus.quasiIso B)
    exact homotopyEquivalences_le_quasiIso _ _ _
      (F.homotopyEquivalences_mapCochainComplexPlus_map _
        (J.homotopyEquivalences_mapCochainComplexPlus_map _
          ((InjectiveObject.ι A).homotopyEquivalences_mapCochainComplexPlus_map _ hf)))
  refine h.isRightDerivedFunctor_of_isIso _ (fun K => ?_)
  dsimp [restrictionDerivedUnit]
  have := unit_isIso_of_injective F
    (J.mapCochainComplexPlus.obj ((InjectiveObject.ι A).mapCochainComplexPlus.obj K))
    (fun i => hJ _ (K.obj.X i).property)
  infer_instance

private def restrictionDerivedIso (hJ : ∀ M : A, Injective M → Injective (J.obj M)) :
    G.rightDerivedFunctorPlus ≅ exactDerivedPlus J ⋙ F.rightDerivedFunctorPlus := by
  letI := restrictionDerivedUnit_isDerived J F hJ
  exact rightDerivedNatIso _ _ G.rightDerivedFunctorPlusUnit (restrictionDerivedUnit J F)
    (CochainComplex.Plus.quasiIso A)
      (isoWhiskerRight (mapPlusCompIso J F G e).symm DerivedCategory.Plus.Q ≪≫
        (associator ..))

private instance (hJ : ∀ M : A, Injective M → Injective (J.obj M)) :
    NatTrans.CommShift (restrictionDerivedIso J F G e hJ).hom ℤ := by
  let QB := DerivedCategory.Plus.Q (C := B)
  let γ := mapPlusCompIso J F G e
  let i := whiskerRight γ.inv QB
  let j := (associator J.mapCochainComplexPlus F.mapCochainComplexPlus QB).hom
  haveI : γ.hom.CommShift ℤ :=
    inferInstanceAs ((mapPlusCompIso J F G e).hom.CommShift ℤ)
  haveI : γ.inv.CommShift ℤ := NatTrans.CommShift.of_iso_inv γ ℤ
  haveI : i.CommShift ℤ := NatTrans.CommShift.whiskerRight γ.inv QB ℤ
  haveI : j.CommShift ℤ := NatTrans.CommShift.associator F.mapCochainComplexPlus QB ℤ
  haveI : (i ≫ j).CommShift ℤ := NatTrans.CommShift.comp i j ℤ
  refine NatTrans.CommShift.of_isRightDerivedFunctor
    G.rightDerivedFunctorPlusUnit (restrictionDerivedUnit J F)
    (i ≫ j) (CochainComplex.Plus.quasiIso A) ?_
  letI := restrictionDerivedUnit_isDerived J F hJ
  simp [restrictionDerivedIso, i, j, QB, γ]

private def exactDerivedPlusCompιIso :
    exactDerivedPlus J ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ J.mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

private instance : NatTrans.CommShift (exactDerivedPlusCompιIso J).hom ℤ :=
  ObjectProperty.commShift_liftCompιIso_hom ..

private theorem plusTriangle_map_ι_mor₃ {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    (DerivedCategory.Plus.ι.mapTriangle.obj (plusTriangle C hS)).mor₃ =
      (show _ from hS.singleδ) := by
  change (hS.singleδ ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)) ≫
    (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) = hS.singleδ
  rw [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

private def mapPlusTriangleIso {S : ShortComplex A} (hS : S.ShortExact) :
    (exactDerivedPlus J).mapTriangle.obj (plusTriangle A hS) ≅
      plusTriangle A' (hS.map_of_exact J) := by
  let T := plusTriangle A hS
  let L : DerivedCategory.Plus A' ⥤ DerivedCategory A' := DerivedCategory.Plus.ι
  let L₀ : DerivedCategory.Plus A ⥤ DerivedCategory A := DerivedCategory.Plus.ι
  apply L.mapTriangle.preimageIso
  refine ((mapTriangleCompIso (exactDerivedPlus J) L).symm.app T) ≪≫
    ((mapTriangleIso (exactDerivedPlusCompιIso J)).app T) ≪≫
    ((mapTriangleCompIso L₀ J.mapDerivedCategory).app T) ≪≫ ?_
  refine Triangle.isoMk _ _
    ((J.mapDerivedCategorySingleFunctor 0).app S.X₁)
    ((J.mapDerivedCategorySingleFunctor 0).app S.X₂)
    ((J.mapDerivedCategorySingleFunctor 0).app S.X₃) ?_ ?_ ?_
  · exact (J.mapDerivedCategorySingleFunctor 0).hom.naturality S.f
  · exact (J.mapDerivedCategorySingleFunctor 0).hom.naturality S.g
  · dsimp only [T, L, L₀, Functor.comp_obj]
    change (J.mapDerivedCategory.map
        (DerivedCategory.Plus.ι.mapTriangle.obj (plusTriangle A hS)).mor₃ ≫
      (J.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _) ≫ _ =
        _ ≫ (DerivedCategory.Plus.ι.mapTriangle.obj (plusTriangle A' (hS.map_of_exact J))).mor₃
    erw [plusTriangle_map_ι_mor₃ hS, plusTriangle_map_ι_mor₃ (hS.map_of_exact J)]
    change (ShiftedHom.map hS.singleδ J.mapDerivedCategory) ≫ _ = _
    rw [hS.mapShiftedHom_singleδ J]
    simp [Category.assoc, ← Functor.map_comp]

omit [EnoughInjectives A] [EnoughInjectives A'] in
private lemma mapPlusTriangleIso_hom₁ {S : ShortComplex A} (hS : S.ShortExact) :
    (mapPlusTriangleIso J hS).hom.hom₁ = (exactDerivedPlusSingle J).hom.app S.X₁ := by
  apply DerivedCategory.Plus.ι.map_injective
  unfold mapPlusTriangleIso
  change (((DerivedCategory.Plus.ι (C := A')).mapTriangle).map
    (((DerivedCategory.Plus.ι (C := A')).mapTriangle).preimage _)).hom₁ = _
  rw [Functor.map_preimage]
  simp [exactDerivedPlusCompιIso, exactDerivedPlusSingle, ObjectProperty.liftCompιIso]
  exact Category.id_comp _

omit [EnoughInjectives A] [EnoughInjectives A'] in
private lemma mapPlusTriangleIso_hom₃ {S : ShortComplex A} (hS : S.ShortExact) :
    (mapPlusTriangleIso J hS).hom.hom₃ = (exactDerivedPlusSingle J).hom.app S.X₃ := by
  apply DerivedCategory.Plus.ι.map_injective
  unfold mapPlusTriangleIso
  change (((DerivedCategory.Plus.ι (C := A')).mapTriangle).map
    (((DerivedCategory.Plus.ι (C := A')).mapTriangle).preimage _)).hom₃ = _
  rw [Functor.map_preimage]
  simp [exactDerivedPlusCompιIso, exactDerivedPlusSingle, ObjectProperty.liftCompιIso]
  exact Category.id_comp _

private def restrictionValueIso (hJ : ∀ M : A, Injective M → Injective (J.obj M)) (n : ℕ) :
    rightValue G n ≅ J ⋙ rightValue F n := by
  let H := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let S := DerivedCategory.Plus.singleFunctor A 0
  let S' := DerivedCategory.Plus.singleFunctor A' 0
  let RF := F.rightDerivedFunctorPlus
  exact isoWhiskerLeft S (isoWhiskerRight (restrictionDerivedIso J F G e hJ) H) ≪≫
    isoWhiskerLeft S (associator (exactDerivedPlus J) RF H) ≪≫
    (associator S (exactDerivedPlus J) (RF ⋙ H)).symm ≪≫
    isoWhiskerRight (exactDerivedPlusSingle J) (RF ⋙ H) ≪≫
    associator J S' (RF ⋙ H)

private lemma restrictionValueIso_boundary (hJ : ∀ M : A, Injective M → Injective (J.obj M))
    (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ) :
    (restrictionValueIso J F G e hJ n).hom.app S.X₃ ≫ rightBoundary F (hS.map_of_exact J) n =
      rightBoundary G hS n ≫ (restrictionValueIso J F G e hJ (n + 1)).hom.app S.X₁ := by
  let γ := ((mapTriangleIso (restrictionDerivedIso J F G e hJ)).app (plusTriangle A hS)).hom ≫
    ((mapTriangleCompIso (exactDerivedPlus J) F.rightDerivedFunctorPlus).app _).hom ≫
    F.rightDerivedFunctorPlus.mapTriangle.map (mapPlusTriangleIso J hS).hom
  have hd := (DerivedCategory.Plus.homologyFunctor B 0).homologySequenceδ_naturality γ
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)
  simp [γ, restrictionValueIso, rightBoundary, mapPlusTriangleIso_hom₁,
    mapPlusTriangleIso_hom₃] at hd ⊢
  exact hd


private lemma restrictionDerivedIso_unit (hJ : ∀ M : A, Injective M → Injective (J.obj M))
    (K : CochainComplex.Plus A) :
    G.rightDerivedFunctorPlusUnit.app K ≫
      (restrictionDerivedIso J F G e hJ).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map ((mapPlusCompIso J F G e).inv.app K) ≫
      F.rightDerivedFunctorPlusUnit.app (J.mapCochainComplexPlus.obj K) ≫
        F.rightDerivedFunctorPlus.map ((exactDerivedPlusFactors J).inv.app K) := by
  letI := restrictionDerivedUnit_isDerived J F hJ
  simp [restrictionDerivedIso, restrictionDerivedUnit]

omit [EnoughInjectives A] [EnoughInjectives A'] in
private lemma exactDerivedPlus_map_augmentation {M : A} {I : CochainComplex A ℤ}
    [I.IsStrictlyGE 0] (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) :
    let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
    let L : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
    let q : L ⟶ K := ObjectProperty.homMk i
    let K' := J.mapCochainComplexPlus.obj K
    let L' : CochainComplex.Plus A' :=
      ⟨(CochainComplex.singleFunctor A' 0).obj (J.obj M), 0, inferInstance⟩
    let q' : L' ⟶ K' := ObjectProperty.homMk
      (((J.mapCochainComplexSingleFunctor 0).inv.app M) ≫
      (J.mapHomologicalComplex (.up ℤ)).map i)
    (exactDerivedPlus J).map (DerivedCategory.Plus.Q.map q) ≫
      (exactDerivedPlusFactors J).hom.app K =
    (exactDerivedPlusSingle J).hom.app M ≫ DerivedCategory.Plus.Q.map q' := by
  intro K L q K' L' q'
  apply DerivedCategory.Plus.ι.map_injective
  have h := J.mapDerivedCategoryFactors_hom_naturality i
  change J.mapDerivedCategory.map (DerivedCategory.Q.map i) ≫
    J.mapDerivedCategoryFactors.hom.app I =
      (J.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      DerivedCategory.Q.map (((J.mapCochainComplexSingleFunctor 0).inv.app M) ≫
        (J.mapHomologicalComplex (.up ℤ)).map i)
  rw [h, Functor.map_comp, ← Category.assoc]
  congr 1
  rw [← cancel_epi ((J.mapDerivedCategorySingleFunctor 0).inv.app M),
    Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]


end RestrictionDerived

section RestrictionModel
attribute [local instance] HasDerivedCategory.standard

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B]
    [Abelian A] [Abelian A'] [Abelian B] [EnoughInjectives A] [EnoughInjectives A']
    (J : A ⥤ A') [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (F : A' ⥤ B) [F.Additive] (G : A ⥤ B) [G.Additive] (e : J ⋙ F ≅ G)

private lemma restrictionValueIso_model
    (hJ : ∀ M : A, Injective M → Injective (J.obj M))
    {M : A} {I : CochainComplex A ℤ} [I.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i)
    (hJi : QuasiIso (((J.mapCochainComplexSingleFunctor 0).inv.app M) ≫
      (J.mapHomologicalComplex (.up ℤ)).map i)) (n : ℕ) :
    resolutionModelMap G i hi n ≫ (restrictionValueIso J F G e hJ n).hom.app M =
      HomologicalComplex.homologyMap
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).inv.app I) (n : ℤ) ≫
        resolutionModelMap F _ hJi n := by
  let K : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let L : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
  let q : L ⟶ K := ObjectProperty.homMk i
  let K' := J.mapCochainComplexPlus.obj K
  let L' : CochainComplex.Plus A' :=
    ⟨(CochainComplex.singleFunctor A' 0).obj (J.obj M), 0, inferInstance⟩
  let q' : L' ⟶ K' := ObjectProperty.homMk
    (((J.mapCochainComplexSingleFunctor 0).inv.app M) ≫
      (J.mapHomologicalComplex (.up ℤ)).map i)
  let Q := DerivedCategory.Plus.Q (C := A)
  let Q' := DerivedCategory.Plus.Q (C := A')
  let QB := DerivedCategory.Plus.Q (C := B)
  let RJ := exactDerivedPlus J
  let RF := F.rightDerivedFunctorPlus
  let RG := G.rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let τ := restrictionDerivedIso J F G e hJ
  let σ := exactDerivedPlusSingle J
  let θ := exactDerivedPlusFactors J
  let γ := mapPlusCompIso J F G e
  let α := G.rightDerivedFunctorPlusUnit
  let α' := F.rightDerivedFunctorPlusUnit
  let β := DerivedCategory.homologyFunctorFactors B (n : ℤ)
  haveI : IsIso (Q.map q) := Localization.inverts Q (CochainComplex.Plus.quasiIso A) q hi
  haveI : IsIso (Q'.map q') := Localization.inverts Q' (CochainComplex.Plus.quasiIso A') q' hJi
  have hq : RJ.map (Q.map q) ≫ θ.hom.app K = σ.hom.app M ≫ Q'.map q' :=
    exactDerivedPlus_map_augmentation J i
  have hq' : θ.inv.app K ≫ RJ.map (inv (Q.map q)) ≫ σ.hom.app M = inv (Q'.map q') := by
    apply (cancel_mono (Q'.map q')).mp
    rw [Category.assoc, Category.assoc, ← hq, ← RJ.map_comp_assoc,
      IsIso.inv_hom_id, RJ.map_id, Category.id_comp, Iso.inv_hom_id_app, IsIso.inv_hom_id]
  have hn : RG.map (inv (Q.map q)) ≫ τ.hom.app (Q.obj L) =
      τ.hom.app (Q.obj K) ≫ RF.map (RJ.map (inv (Q.map q))) :=
    τ.hom.naturality (inv (Q.map q))
  have hτ : α.app K ≫ τ.hom.app (Q.obj K) = QB.map (γ.inv.app K) ≫
      α'.app K' ≫ RF.map (θ.inv.app K) :=
    restrictionDerivedIso_unit J F G e hJ K
  have hα : α.app K ≫ RG.map (inv (Q.map q)) ≫
      τ.hom.app (Q.obj L) ≫ RF.map (σ.hom.app M) =
      QB.map (γ.inv.app K) ≫ α'.app K' ≫ RF.map (inv (Q'.map q')) := by
    rw [reassoc_of% hn, ← Category.assoc (α.app K), hτ]
    simp only [Category.assoc, ← RF.map_comp, hq']
  let comparison := (Functor.mapHomologicalComplexCompIso e (.up ℤ)).inv.app I
  have hb : HomologicalComplex.homologyMap comparison (n : ℤ) ≫
      β.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K'.obj) =
      β.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫ H.map (QB.map (γ.inv.app K)) :=
    β.inv.naturality comparison
  have he :
      (restrictionValueIso J F G e hJ n).hom.app M =
      H.map (τ.hom.app (Q.obj L) ≫ RF.map (σ.hom.app M)) := by
    simp [restrictionValueIso, H, τ, Q, L, RF, σ]
    rfl
  change (β.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
    H.map (α.app K ≫ RG.map (inv (Q.map q)))) ≫ _ =
      HomologicalComplex.homologyMap comparison (n : ℤ) ≫
      β.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K'.obj) ≫
      H.map (α'.app K' ≫ RF.map (inv (Q'.map q')))
  rw [he, Category.assoc, ← H.map_comp, Category.assoc, hα]
  simp only [H.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ H.map (α'.app K') ≫ H.map (RF.map (inv (Q'.map q')))) hb.symm

private lemma restrictionValueIso_zero
    (hJ : ∀ M : A, Injective M → Injective (J.obj M)) :
    rightDegreeZeroUnit G ≫ (restrictionValueIso J F G e hJ 0).hom =
      e.inv ≫ whiskerLeft J (rightDegreeZeroUnit F) := by
  apply NatTrans.ext
  funext M
  let S : CochainComplex A ℤ := (CochainComplex.singleFunctor A 0).obj M
  let a := (J.mapCochainComplexSingleFunctor 0).inv.app M
  have ha : QuasiIso a := by dsimp [a]; infer_instance
  have ha' : QuasiIso (a ≫ (J.mapHomologicalComplex (.up ℤ)).map (𝟙 S)) := by
    letI := ha
    infer_instance
  have hm := restrictionValueIso_model J F G e hJ (𝟙 S) (by infer_instance) ha' 0
  apply degreeZero_comparison_of_stalk J F G e M _ ha
  have h : a ≫ (J.mapHomologicalComplex (.up ℤ)).map (𝟙 S) = a := by
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  change _ = _ ≫ resolutionModelMap F
    (a ≫ (J.mapHomologicalComplex (.up ℤ)).map (𝟙 S)) ha' 0 at hm
  simpa only [h] using! hm

end RestrictionModel


theorem locality : localityType.{u} := by
  intro X R U
  dsimp only
  let J := restriction R U
  let F := openSections R U
  let G := SheafOfModules.evaluation R (op U)
  let e := sectionsRestriction R U
  haveI : PreservesFiniteLimits J :=
    (SheafInjectivesAndRestriction.Expected.restriction_exact R U).1
  haveI : PreservesFiniteColimits J :=
    (SheafInjectivesAndRestriction.Expected.restriction_exact R U).2
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (U.sheafRestrict.obj R))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R U))
  let hJ : ∀ M : Modules R, Injective M → Injective (J.obj M) :=
    SheafInjectivesAndRestriction.restriction_injective R U
  refine ⟨restrictionValueIso J F G e hJ, restrictionValueIso_zero J F G e hJ, ?_, ?_⟩
  · intro S hS
    exact ⟨hS.map_of_exact J, restrictionValueIso_boundary J F G e hJ S hS⟩
  · intro M I hI ι hι hI'
    letI := hι
    have hJι : QuasiIso (restrictedAugmentation R U ι) := by
      haveI : QuasiIso ((J.mapCochainComplexSingleFunctor 0).inv.app M) :=
        quasiIso_of_isIso _
      haveI : QuasiIso ((J.mapHomologicalComplex (.up ℤ)).map ι) :=
        HomologicalComplex.quasiIso_map_of_preservesHomology _ _
      exact quasiIso_comp _ _
    exact ⟨hJι, fun q => hJ _ (hI' q), restrictionValueIso_model J F G e hJ ι hι hJι⟩

end OpenRestriction

instance abelianSectionsPreservesFiniteLimits (X : TopCat.{u}) (U : Opens X) :
    PreservesFiniteLimits (abelianSections X U) := by
  change PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u} ⋙ (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))
  exact comp_preservesFiniteLimits _ _

/-- Dimension shifting in ordinary abelian sheaves, using the flasque
lifting theorem for sections on any open. -/
theorem abelianFlasqueAcyclic (X : TopCat.{u}) (U : Opens X)
    (M : AbelianSheaves X) (hM : TopCat.Sheaf.IsFlasque M) (n : ℕ) :
    IsZero ((abelianCohomology X U (n + 1)).obj M) := by
  letI := HasDerivedCategory.standard (AbelianSheaves X)
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  let F := abelianSections X U
  have : PreservesFiniteLimits F := inferInstanceAs (PreservesFiniteLimits (abelianSections X U))
  let T := rightSystem F
  have hT : IsCohomological T := UniversalDeltaFunctors.rightDelta _ _ F
  have vanish (I : AbelianSheaves X) [Injective I] (k : ℕ) :
      IsZero ((T.value (k + 1)).obj I) :=
    ClassicalDerivedValues.rightInjectiveVanishing _ _ F I k
  suffices h : ∀ N : AbelianSheaves X, TopCat.Sheaf.IsFlasque N →
      IsZero ((T.value (n + 1)).obj N) from h M hM
  induction n with
  | zero =>
    intro N hN
    letI := hN
    let S := UniversalDeltaFunctors.injectiveSequence N
    have hS : S.ShortExact := UniversalDeltaFunctors.injectiveSequence_shortExact N
    letI : Epi (T.δ hS 0) :=
      UniversalDeltaFunctors.dimensionShift_epi T hT vanish N 0
    have hsur : Epi (F.map S.g) := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS
    letI := ClassicalDerivedValues.rightZero _ _ F
    let e := (asIso (rightDegreeZeroUnit F)).symm
    have hepi : Epi ((T.value 0).map S.g) := by
      change Epi ((rightValue F 0).map S.g)
      apply (epi_comp_iff_of_isIso _ (e.hom.app S.X₃)).mp
      rw [e.hom.naturality S.g]
      infer_instance
    letI := hepi
    exact IsZero.of_epi_eq_zero (T.δ hS 0)
      (zero_of_epi_comp ((T.value 0).map S.g) (hT.exact₃ hS 0).zero)
  | succ n ih =>
    intro N hN
    letI := hN
    let S := UniversalDeltaFunctors.injectiveSequence N
    have hS : S.ShortExact := UniversalDeltaFunctors.injectiveSequence_shortExact N
    letI : TopCat.Sheaf.IsFlasque S.X₂ :=
      SheafInjectivesAndRestriction.abelian_injective_flasque X _ inferInstance
    have hQ : TopCat.Sheaf.IsFlasque S.X₃ :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    letI : Epi (T.δ hS (n + 1)) :=
      UniversalDeltaFunctors.dimensionShift_epi T hT vanish N (n + 1)
    exact IsZero.of_epi (T.δ hS (n + 1)) (ih S.X₃ hQ)

section ForgetSections

attribute [local instance] HasDerivedCategory.standard
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
variable {X : TopCat.{u}}

private lemma forgottenAugmentation_quasiIso (R : RingSheaf X) {M : Modules R}
    {I : CochainComplex (Modules R) ℤ}
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I)
    (hι : QuasiIso ι) : QuasiIso (forgottenAugmentation R ι) := by
  letI := hι
  let F := SheafOfModules.toSheaf R
  haveI : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map ι) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology ι F
  exact quasiIso_comp ((F.mapCochainComplexSingleFunctor 0).inv.app M)
    ((F.mapHomologicalComplex (.up ℤ)).map ι)

private lemma forgottenAugmentation_commutes (R : RingSheaf X) {M N : Modules R}
    {I J : CochainComplex (Modules R) ℤ}
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I)
    (κ : (CochainComplex.singleFunctor (Modules R) 0).obj N ⟶ J)
    (f : M ⟶ N) (g : I ⟶ J)
    (h : ι ≫ g = (CochainComplex.singleFunctor (Modules R) 0).map f ≫ κ) :
    forgottenAugmentation R ι ≫ ((SheafOfModules.toSheaf R).mapHomologicalComplex (.up ℤ)).map g =
      (CochainComplex.singleFunctor (AbelianSheaves X) 0).map ((SheafOfModules.toSheaf R).map f) ≫
        forgottenAugmentation R κ := by
  let F := SheafOfModules.toSheaf R
  dsimp [forgottenAugmentation]
  change (F.mapCochainComplexSingleFunctor 0).inv.app M ≫
      (F.mapHomologicalComplex (.up ℤ)).map ι ≫ (F.mapHomologicalComplex (.up ℤ)).map g =
    (CochainComplex.singleFunctor (AbelianSheaves X) 0).map (F.map f) ≫
      (F.mapCochainComplexSingleFunctor 0).inv.app N ≫ (F.mapHomologicalComplex (.up ℤ)).map κ
  rw [← Functor.map_comp, h, Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun x => x ≫ (F.mapHomologicalComplex (.up ℤ)).map κ)
      ((F.mapCochainComplexSingleFunctor 0).inv.naturality f).symm) |>.trans (Category.assoc _ _ _)

private def forgetComplexComparison (R : RingSheaf X) (U : Opens X) :
    (SheafOfModules.evaluation R (op U)).mapHomologicalComplex (.up ℤ) ⋙
      (forget₂ (ModuleCat.{u} (sectionRing R U)) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ) ≅
    (SheafOfModules.toSheaf R).mapHomologicalComplex (.up ℤ) ⋙
      (abelianSections X U).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (forgetSectionsIso R U) (.up ℤ)

private def forgetModelComparison (R : RingSheaf X) (U : Opens X)
    (I : CochainComplex (Modules R) ℤ) (n : ℕ) :
    ((forget₂ (ModuleCat.{u} (sectionRing R U)) AddCommGrpCat.{u}).obj
      ((((SheafOfModules.evaluation R (op U)).mapHomologicalComplex (.up ℤ)).obj I).homology
        (n : ℤ))) ≅
    (((abelianSections X U).mapHomologicalComplex (.up ℤ)).obj
      (((SheafOfModules.toSheaf R).mapHomologicalComplex (.up ℤ)).obj I)).homology (n : ℤ) := by
  let G := forget₂ (ModuleCat.{u} (sectionRing R U)) AddCommGrpCat.{u}
  let K := ((SheafOfModules.evaluation R (op U)).mapHomologicalComplex (.up ℤ)).obj I
  exact ((K.sc (n : ℤ)).mapHomologyIso G).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) (n : ℤ)).mapIso
      ((forgetComplexComparison R U).app I)

private lemma forgetModelComparison_naturality (R : RingSheaf X) (U : Opens X)
    {I J : CochainComplex (Modules R) ℤ} (g : I ⟶ J) (n : ℕ) :
    let G := forget₂ (ModuleCat.{u} (sectionRing R U)) AddCommGrpCat.{u}
    let Γ := SheafOfModules.evaluation R (op U)
    let Γ' := abelianSections X U
    let F := SheafOfModules.toSheaf R
    G.map (HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)) ≫
      (forgetModelComparison R U J n).hom =
    (forgetModelComparison R U I n).hom ≫
      HomologicalComplex.homologyMap
        ((Γ'.mapHomologicalComplex (.up ℤ)).map ((F.mapHomologicalComplex (.up ℤ)).map g)) (n : ℤ) := by
  intro G Γ Γ' F
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) (n : ℤ)
  let K := (Γ.mapHomologicalComplex (.up ℤ)).obj I
  let L := (Γ.mapHomologicalComplex (.up ℤ)).obj J
  let m : K ⟶ L := (Γ.mapHomologicalComplex (.up ℤ)).map g
  let Gm := G.mapHomologicalComplex (.up ℤ)
  let Fm := F.mapHomologicalComplex (.up ℤ)
  let Γm := Γ'.mapHomologicalComplex (.up ℤ)
  let t := forgetComplexComparison R U
  have h₁ :
      G.map (HomologicalComplex.homologyMap m (n : ℤ)) ≫ ((L.sc (n : ℤ)).mapHomologyIso G).inv =
        ((K.sc (n : ℤ)).mapHomologyIso G).inv ≫ H.map (Gm.map m) :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ (n : ℤ)).map m) G
  have h₂ :
      H.map (Gm.map m) ≫ H.map (t.hom.app J) =
        H.map (t.hom.app I) ≫ H.map (Γm.map (Fm.map g)) := by
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map (t.hom.naturality g)
  change G.map (HomologicalComplex.homologyMap m (n : ℤ)) ≫
      (((L.sc (n : ℤ)).mapHomologyIso G).inv ≫ H.map (t.hom.app J)) =
    (((K.sc (n : ℤ)).mapHomologyIso G).inv ≫ H.map (t.hom.app I)) ≫ H.map (Γm.map (Fm.map g))
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]


theorem forgottenResolution : forgottenResolutionType.{u} := by
  intro X R M I hb ι hι hI
  refine ⟨forgottenAugmentation_quasiIso R ι hι, ?_⟩
  intro q
  exact (SheafInjectivesAndRestriction.flasque_iff R (I.X q)).mpr
    (SheafInjectivesAndRestriction.Expected.injectives_flasque R (I.X q) (hI q))

theorem forget : forgetType.{u} := by
  intro X R U
  let B := ModuleCat.{u} (sectionRing R U)
  let Γ := SheafOfModules.evaluation R (op U)
  let Γ' := abelianSections X U
  let G := forget₂ B AddCommGrpCat.{u}
  let F := SheafOfModules.toSheaf R
  let S := CochainComplex.singleFunctor (Modules R) 0
  let T (n : ℕ) := rightValue Γ n ⋙ G
  let W (n : ℕ) := F ⋙ rightValue Γ' n
  change ∃ e : ∀ n, T n ≅ W n, _
  have hΓ' : PreservesFiniteLimits Γ' := inferInstanceAs (PreservesFiniteLimits (abelianSections X U))
  have modelAcyclic (M : Modules R) (hM : Injective M) : rightAcyclicValue Γ M := by
    letI := hM
    exact AcyclicTermComparison.rightAcyclic_of_injective Γ M
  have modelForgetAcyclic (M : Modules R) (hM : Injective M) :
      rightAcyclicValue Γ' (F.obj M) := by
    apply (AcyclicTermComparison.rightVanishing _ _ Γ' (F.obj M)).mpr
    intro n
    exact abelianFlasqueAcyclic X U _ ((SheafInjectivesAndRestriction.flasque_iff R M).mpr
      (SheafInjectivesAndRestriction.Expected.injectives_flasque R M hM)) n
  have modelForgetMap (M : Modules R) (I : CochainComplex (Modules R) ℤ) [I.IsStrictlyGE 0]
      (ι : S.obj M ⟶ I) (hι : QuasiIso ι) (hI : ∀ q, Injective (I.X q)) (n : ℕ) :
      IsIso (resolutionModelMap Γ' (forgottenAugmentation R ι)
        (forgottenAugmentation_quasiIso R ι hι) n) :=
    resolutionModelMap_isIso Γ' _ _ (fun q => modelForgetAcyclic (I.X q) (hI q)) n
  choose J κ hmono hquasi hinj hbound using fun (M : Modules R) ↦
    InjectiveComplexReplacement.replacement _ (S.obj M) 0 inferInstance
  letI (M : Modules R) : (J M).IsStrictlyGE 0 := hbound M
  let app (M : Modules R) (n : ℕ) : (T n).obj M ≅ (W n).obj M := by
    letI := resolutionModelMap_isIso Γ (κ M) (hquasi M)
      (fun q => modelAcyclic ((J M).X q) (hinj M q)) n
    letI := modelForgetMap M (J M) (κ M) (hquasi M) (hinj M) n
    exact (G.mapIso (asIso (resolutionModelMap Γ (κ M) (hquasi M) n))).symm ≪≫
      forgetModelComparison R U (J M) n ≪≫
      asIso (resolutionModelMap Γ' (forgottenAugmentation R (κ M))
        (forgottenAugmentation_quasiIso R (κ M) (hquasi M)) n)
  have modelSquare (n : ℕ) (M : Modules R) :
      G.map (resolutionModelMap Γ (κ M) (hquasi M) n) ≫ (app M n).hom =
        (forgetModelComparison R U (J M) n).hom ≫
          resolutionModelMap Γ' (forgottenAugmentation R (κ M))
            (forgottenAugmentation_quasiIso R (κ M) (hquasi M)) n := by
    letI := resolutionModelMap_isIso Γ (κ M) (hquasi M)
      (fun q => modelAcyclic ((J M).X q) (hinj M q)) n
    letI := modelForgetMap M (J M) (κ M) (hquasi M) (hinj M) n
    let a := G.mapIso (asIso (resolutionModelMap Γ (κ M) (hquasi M) n))
    change a.hom ≫ a.inv ≫ _ = _
    exact a.hom_inv_id_assoc _
  have modelNat (n : ℕ) {M N : Modules R} (f : M ⟶ N)
      {I : CochainComplex (Modules R) ℤ} [I.IsStrictlyGE 0]
      (ι : S.obj N ⟶ I) (hι : QuasiIso ι) (hI : ∀ q, Injective (I.X q)) :
      ∃ g : J M ⟶ I,
        G.map (resolutionModelMap Γ (κ M) (hquasi M) n) ≫ (T n).map f =
          G.map (HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)) ≫
            G.map (resolutionModelMap Γ ι hι n) ∧
        resolutionModelMap Γ' (forgottenAugmentation R (κ M))
          (forgottenAugmentation_quasiIso R (κ M) (hquasi M)) n ≫ (W n).map f =
          HomologicalComplex.homologyMap ((Γ'.mapHomologicalComplex (.up ℤ)).map
            ((F.mapHomologicalComplex (.up ℤ)).map g)) (n : ℤ) ≫
            resolutionModelMap Γ' (forgottenAugmentation R ι)
              (forgottenAugmentation_quasiIso R ι hι) n := by
    letI : Mono (κ M) := HomologicalComplex.mono_of_mono_f _ (hmono M)
    letI : QuasiIso (κ M) := hquasi M
    obtain ⟨g,hg⟩ := injectiveResolutionLift (κ M) (S.map f ≫ ι) hI
    refine ⟨g, ?_, ?_⟩
    · change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
      rw [← G.map_comp, ← G.map_comp]
      exact congrArg G.map (resolutionModelMap_naturality Γ _ _ _ _ f g
        (congrArg DerivedCategory.Q.map hg) n)
    · exact resolutionModelMap_naturality Γ' _ _ _ _ (F.map f) _
        (congrArg DerivedCategory.Q.map (forgottenAugmentation_commutes R _ _ f g hg)) n
  let e (n : ℕ) : T n ≅ W n := NatIso.ofComponents (fun M => app M n) (by
    intro M N f
    obtain ⟨g, hg, hFg⟩ := modelNat n f (κ N) (hquasi N) (hinj N)
    letI : IsIso (resolutionModelMap Γ (κ M) (hquasi M) n) :=
      resolutionModelMap_isIso Γ _ _ (fun q => modelAcyclic _ (hinj M q)) n
    apply (cancel_epi (G.map (resolutionModelMap Γ (κ M) (hquasi M) n))).mp
    rw [← Category.assoc, hg, Category.assoc, modelSquare, ← Category.assoc,
      forgetModelComparison_naturality, Category.assoc, ← hFg,
      ← Category.assoc, ← modelSquare, Category.assoc])
  refine ⟨e, ?_⟩
  intro M I hb ι hι hI
  refine ⟨forgottenAugmentation_quasiIso R ι hι, ?_⟩
  intro n
  have hall : G.map (resolutionModelMap Γ ι hι n) ≫ (app M n).hom =
      (forgetModelComparison R U I n).hom ≫
        resolutionModelMap Γ' (forgottenAugmentation R ι)
          (forgottenAugmentation_quasiIso R ι hι) n := by
    obtain ⟨g, hg, hFg⟩ := modelNat n (𝟙 M) ι hι hI
    rw [(T n).map_id] at hg
    rw [(W n).map_id] at hFg
    replace hg := (Category.comp_id _).symm.trans hg
    replace hFg := (Category.comp_id _).symm.trans hFg
    haveI : IsIso (resolutionModelMap Γ (κ M) (hquasi M) n) :=
      resolutionModelMap_isIso Γ _ _ (fun q => modelAcyclic _ (hinj M q)) n
    haveI : IsIso (resolutionModelMap Γ ι hι n) :=
      resolutionModelMap_isIso Γ _ _ (fun q => modelAcyclic _ (hI q)) n
    haveI : IsIso (G.map (HomologicalComplex.homologyMap
        ((Γ.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ))) :=
      IsIso.of_isIso_fac_right hg.symm
    apply (cancel_epi (G.map (HomologicalComplex.homologyMap
      ((Γ.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)))).mp
    rw [← Category.assoc, ← hg, modelSquare, ← Category.assoc,
      forgetModelComparison_naturality, Category.assoc, ← hFg]
  let K := (Γ.mapHomologicalComplex (.up ℤ)).obj I
  let a := (K.sc (n : ℤ)).mapHomologyIso G
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) (n : ℤ)
  let t := (forgetComplexComparison R U).hom.app I
  let r := resolutionModelMap Γ' (forgottenAugmentation R ι)
    (forgottenAugmentation_quasiIso R ι hι) n
  change a.hom ≫ (G.map (resolutionModelMap Γ ι hι n) ≫ (app M n).hom) = H.map t ≫ r
  rw [hall]
  change a.hom ≫ (a.inv ≫ H.map t) ≫ r = _
  rw [Category.assoc, a.hom_inv_id_assoc]

end ForgetSections

/-- Transport the open-unit representation through the equivalence of
integer modules and ordinary abelian sheaves. -/
def abelianOpenUnitEquiv (X : TopCat.{u}) (U : Opens X) (F : AbelianSheaves X) :
    (abelianOpenUnit X U ⟶ F) ≃+ (abelianSections X U).obj F := by
  let E := SheafInjectivesAndRestriction.integerModulesEquivalence X
  let R := constantIntegerRingSheaf X
  letI : E.functor.Additive :=
    inferInstanceAs (SheafOfModules.toSheaf (constantIntegerRingSheaf X)).Additive
  exact ((E.toAdjunction.homAddEquiv (openUnit R U) F).trans
    (SheafInjectivesAndRestriction.homOpenUnitAddEquiv R U (E.inverse.obj F))).trans
      ((abelianSections X U).mapIso (E.counitIso.app F)).addCommGroupIsoToAddEquiv

lemma abelianOpenUnitEquiv_naturality (X : TopCat.{u}) (U : Opens X)
    {F G : AbelianSheaves X} (f : abelianOpenUnit X U ⟶ F) (g : F ⟶ G) :
    abelianOpenUnitEquiv X U G (f ≫ g) =
      (abelianSections X U).map g (abelianOpenUnitEquiv X U F f) := by
  let E := SheafInjectivesAndRestriction.integerModulesEquivalence X
  let R := constantIntegerRingSheaf X
  change (abelianSections X U).map (E.counitIso.hom.app G)
    (SheafInjectivesAndRestriction.homOpenUnit R U (E.inverse.obj G)
      (E.toAdjunction.homEquiv _ G (f ≫ g))) =
    (abelianSections X U).map g
      ((abelianSections X U).map (E.counitIso.hom.app F)
        (SheafInjectivesAndRestriction.homOpenUnit R U (E.inverse.obj F)
          (E.toAdjunction.homEquiv _ F f)))
  rw [Adjunction.homEquiv_naturality_right,
    SheafInjectivesAndRestriction.homOpenUnit_naturality]
  exact congr($(congrArg (abelianSections X U).map (E.counitIso.hom.naturality g))
    (SheafInjectivesAndRestriction.homOpenUnit R U (E.inverse.obj F)
      (E.toAdjunction.homEquiv _ F f)))

private lemma abelianOpenUnitEquiv_eval (X : TopCat.{u}) (U : Opens X)
    (F : AbelianSheaves X) (f : abelianOpenUnit X U ⟶ F) :
    abelianOpenUnitEquiv X U F f = (abelianSections X U).map f
      (abelianOpenUnitSection X U) := by
  let E := SheafInjectivesAndRestriction.integerModulesEquivalence X
  let R := constantIntegerRingSheaf X
  let g : openUnit R U ⟶ E.inverse.obj F := E.toAdjunction.homEquiv _ _ f
  have hg : E.functor.map g ≫ E.counitIso.hom.app F = f := by
    calc
      E.functor.map g ≫ E.counitIso.hom.app F =
          (E.toAdjunction.homEquiv _ _).symm g :=
        (E.toAdjunction.homEquiv_counit _ _ g).symm
      _ = f := (E.toAdjunction.homEquiv _ _).symm_apply_apply f
  change (abelianSections X U).map (E.counitIso.hom.app F)
    (SheafInjectivesAndRestriction.homOpenUnit R U (E.inverse.obj F) g) = _
  rw [SheafInjectivesAndRestriction.homOpenUnit_eval, ← hg, Functor.map_comp]
  rfl

private def abelianOpenUnitIso (X : TopCat.{u}) (U : Opens X) :
    preadditiveCoyoneda.obj (op (abelianOpenUnit X U)) ≅ abelianSections X U := by
  refine NatIso.ofComponents (fun F ↦ (abelianOpenUnitEquiv X U F).toAddCommGrpIso) ?_
  intro F G g
  ext f
  exact abelianOpenUnitEquiv_naturality X U f g

theorem abelianOpenUnitRepresentation : abelianOpenUnitType.{u} := by
  intro X U
  exact ⟨abelianOpenUnitIso X U, abelianOpenUnitEquiv_eval X U⟩

open CochainComplex CochainComplex.HomComplex
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

private def abelianOpenUnitCochainIso (X : TopCat.{u}) (U : Opens X)
    (I : CochainComplex (AbelianSheaves X) ℤ) :
    HomComplex ((CochainComplex.singleFunctor (AbelianSheaves X) 0).obj
      (abelianOpenUnit X U)) I ≅
      ((abelianSections X U).mapHomologicalComplex (.up ℤ)).obj I := by
  let P := abelianOpenUnit X U
  let L := (CochainComplex.singleFunctor (AbelianSheaves X) 0).obj P
  refine HomologicalComplex.Hom.isoOfComponents (fun q ↦
    ((Cochain.fromSingleEquiv (zero_add q) :
        Cochain L I q ≃+ (P ⟶ I.X q)).trans
      (abelianOpenUnitEquiv X U (I.X q))).toAddCommGrpIso) ?_
  intro q r h
  have hr : r = q + 1 := h.symm
  subst r
  ext (z : Cochain L I q)
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z q (zero_add q)
  change (abelianSections X U).map (I.d q (q + 1))
    (abelianOpenUnitEquiv X U (I.X q) (Cochain.fromSingleEquiv (zero_add q)
      (Cochain.fromSingleMk f (zero_add q)))) =
    abelianOpenUnitEquiv X U (I.X (q + 1)) (Cochain.fromSingleEquiv
      (zero_add (q + 1)) (δ q (q + 1) (Cochain.fromSingleMk f (zero_add q))))
  rw [Cochain.δ_fromSingleMk f (zero_add q) (q + 1) (q + 1) (zero_add (q + 1))]
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  exact (abelianOpenUnitEquiv_naturality X U f (I.d q (q + 1))).symm

private theorem abelianOpenUnitCochainIso_eval (X : TopCat.{u}) (U : Opens X)
    (I : CochainComplex (AbelianSheaves X) ℤ) (q : ℤ)
    (f : Cochain ((CochainComplex.singleFunctor (AbelianSheaves X) 0).obj
      (abelianOpenUnit X U)) I q) :
    (abelianOpenUnitCochainIso X U I).hom.f q f =
      (abelianSections X U).map (Cochain.fromSingleEquiv (zero_add q) f)
        (abelianOpenUnitSection X U) :=
  abelianOpenUnitEquiv_eval X U _ _

section HomPostcomposition

variable {A : Type*} [Category A] [Preadditive A] {L I J : CochainComplex A ℤ}

private def homComplexPostcomp (L : CochainComplex A ℤ) (g : I ⟶ J) :
    HomComplex L I ⟶ HomComplex L J where
  f q := AddCommGrpCat.ofHom
    { toFun := fun z : Cochain L I q ↦ z.comp (.ofHom g) (add_zero q)
      map_zero' := Cochain.zero_comp _ _
      map_add' := fun _ _ ↦ Cochain.add_comp _ _ _ _ }
  comm' q r _ := by
    ext z
    change δ q r (z.comp (.ofHom g) (add_zero q)) = (δ q r z).comp (.ofHom g) (add_zero r)
    exact δ_comp_ofHom z g r

private def cocyclePostcomp (L : CochainComplex A ℤ) (g : I ⟶ J) (n : ℤ) :
    Cocycle L I n →+ Cocycle L J n where
  toFun z := z.postcomp g
  map_zero' := by
    apply Cocycle.ext
    change Cochain.comp (0 : Cochain L I n) (.ofHom g) (add_zero n) = 0
    exact Cochain.zero_comp _ _
  map_add' := by
    intro x y
    apply Cocycle.ext
    change Cochain.comp ((x : Cochain L I n) + (y : Cochain L I n)) (.ofHom g) (add_zero n) =
      Cochain.comp (x : Cochain L I n) (.ofHom g) (add_zero n) +
        Cochain.comp (y : Cochain L I n) (.ofHom g) (add_zero n)
    exact Cochain.add_comp _ _ _ _

private def classPostcomp (L : CochainComplex A ℤ) (g : I ⟶ J) (n : ℤ) :
    CohomologyClass L I n →+ CohomologyClass L J n := by
  refine CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom L J n).comp (cocyclePostcomp L g n)) ?_
  rintro z ⟨p, hp, a, ha⟩
  exact (CohomologyClass.mk_eq_zero_iff _).mpr
    ⟨p, hp, a.comp (.ofHom g) (add_zero p), by
      change δ p n (a.comp (.ofHom g) (add_zero p)) =
        (z : Cochain L I n).comp (.ofHom g) (add_zero n)
      rw [δ_comp_ofHom, ha]⟩

private lemma homologyAddEquiv_postcomp_mk (L : CochainComplex A ℤ)
    (g : I ⟶ J) (n : ℤ) (z : Cocycle L I n) :
    (HomComplex.homologyAddEquiv L J n)
      (HomologicalComplex.homologyMap (homComplexPostcomp L g) n
        ((HomComplex.homologyAddEquiv L I n).symm (CohomologyClass.mk z))) =
          CohomologyClass.mk (z.postcomp g) := by
  let φ := (HomologicalComplex.shortComplexFunctor _ _ n).map (homComplexPostcomp L g)
  let γ : ShortComplex.LeftHomologyMapData φ
      (HomComplex.leftHomologyData L I n) (HomComplex.leftHomologyData L J n) :=
    { φK := AddCommGrpCat.ofHom (cocyclePostcomp L g n)
      φH := AddCommGrpCat.ofHom (classPostcomp L g n)
      commi := by ext; rfl
      commf' := by
        ext z
        apply Subtype.ext
        exact (δ_comp_ofHom z g _).symm
      commπ := by ext; rfl }
  have e := congr($(γ.homologyMap_comm)
    ((HomComplex.homologyAddEquiv L I n).symm (CohomologyClass.mk z)))
  change _ = (classPostcomp L g n)
    (HomComplex.homologyAddEquiv L I n
      ((HomComplex.homologyAddEquiv L I n).symm (CohomologyClass.mk z))) at e
  rw [AddEquiv.apply_symm_apply] at e
  exact e

end HomPostcomposition

private lemma abelianOpenUnitCochainIso_naturality (X : TopCat.{u}) (U : Opens X)
    {I J : CochainComplex (AbelianSheaves X) ℤ} (g : I ⟶ J) :
    (abelianOpenUnitCochainIso X U I).hom ≫
      ((abelianSections X U).mapHomologicalComplex (.up ℤ)).map g =
    homComplexPostcomp ((CochainComplex.singleFunctor (AbelianSheaves X) 0).obj
      (abelianOpenUnit X U)) g ≫ (abelianOpenUnitCochainIso X U J).hom := by
  ext q (z : Cochain ((CochainComplex.singleFunctor (AbelianSheaves X) 0).obj
      (abelianOpenUnit X U)) I q)
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z q (zero_add q)
  change (abelianSections X U).map (g.f q)
    ((abelianOpenUnitCochainIso X U I).hom.f q (Cochain.fromSingleMk f (zero_add q))) =
    (abelianOpenUnitCochainIso X U J).hom.f q
      ((Cochain.fromSingleMk f (zero_add q)).comp (Cochain.ofHom g) (add_zero q))
  rw [← Cochain.fromSingleMk_postcomp f (zero_add q) g]
  change (abelianSections X U).map (g.f q)
    (abelianOpenUnitEquiv X U (I.X q) (Cochain.fromSingleEquiv (zero_add q)
      (Cochain.fromSingleMk f (zero_add q)))) =
    abelianOpenUnitEquiv X U (J.X q) (Cochain.fromSingleEquiv (zero_add q)
      (Cochain.fromSingleMk (f ≫ g.f q) (zero_add q)))
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  exact (abelianOpenUnitEquiv_naturality X U f (g.f q)).symm

section ExtComparison

attribute [local instance] HasDerivedCategory.standard

variable (X : TopCat.{u}) (U : Opens X)

private abbrev openUnitStalk :=
  (CochainComplex.singleFunctor (AbelianSheaves X) 0).obj (abelianOpenUnit X U)

private abbrev abelianStalk (F : AbelianSheaves X) :=
  (CochainComplex.singleFunctor (AbelianSheaves X) 0).obj F

private def sectionClassEquiv {F : AbelianSheaves X}
    {I : CochainComplex (AbelianSheaves X) ℤ} [I.IsStrictlyGE 0]
    (ι : abelianStalk X F ⟶ I) (hι : QuasiIso ι) (hI : ∀ q, Injective (I.X q))
    (n : ℕ) :
    CohomologyClass (openUnitStalk X U) I (n : ℤ) ≃+
      (abelianCohomology X U n).obj F := by
  haveI := resolutionModelMap_isIso (abelianSections X U) ι hι (fun q ↦ by
    letI := hI q
    exact AcyclicTermComparison.rightAcyclic_of_injective (abelianSections X U) (I.X q)) n
  exact (HomComplex.homologyAddEquiv _ I (n : ℤ)).symm.trans
    (((HomologicalComplex.homologyFunctor _ (.up ℤ) (n : ℤ)).mapIso
      (abelianOpenUnitCochainIso X U I)).addCommGroupIsoToAddEquiv.trans
        (asIso (resolutionModelMap (abelianSections X U) ι hι n)).addCommGroupIsoToAddEquiv)

private lemma sectionClassEquiv_postcomp {F G : AbelianSheaves X}
    {I J : CochainComplex (AbelianSheaves X) ℤ} [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (ι : abelianStalk X F ⟶ I) (hι : QuasiIso ι) (hI : ∀ q, Injective (I.X q))
    (κ : abelianStalk X G ⟶ J) (hκ : QuasiIso κ) (hJ : ∀ q, Injective (J.X q))
    (f : F ⟶ G) (g : I ⟶ J)
    (h : ι ≫ g = (CochainComplex.singleFunctor (AbelianSheaves X) 0).map f ≫ κ)
    (n : ℕ) (z : Cocycle (openUnitStalk X U) I (n : ℤ)) :
    (abelianCohomology X U n).map f
      (sectionClassEquiv X U ι hι hI n (CohomologyClass.mk z)) =
    sectionClassEquiv X U κ hκ hJ n (CohomologyClass.mk (z.postcomp g)) := by
  let Γ := abelianSections X U
  let L := openUnitStalk X U
  let x := (HomComplex.homologyAddEquiv L I (n : ℤ)).symm (CohomologyClass.mk z)
  have hh := resolutionModelMap_naturality Γ ι hι κ hκ f g
    (congrArg (DerivedCategory.Q (C := AbelianSheaves X)).map h) n
  have hh' := congr($(hh)
    (HomologicalComplex.homologyMap (abelianOpenUnitCochainIso X U I).hom (n : ℤ) x))
  change (abelianCohomology X U n).map f
      (sectionClassEquiv X U ι hι hI n (CohomologyClass.mk z)) = _ at hh'
  rw [hh']
  change resolutionModelMap Γ κ hκ n
      (HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)
        (HomologicalComplex.homologyMap (abelianOpenUnitCochainIso X U I).hom (n : ℤ) x)) =
    resolutionModelMap Γ κ hκ n
      (HomologicalComplex.homologyMap (abelianOpenUnitCochainIso X U J).hom (n : ℤ)
        ((HomComplex.homologyAddEquiv L J (n : ℤ)).symm (CohomologyClass.mk (z.postcomp g))))
  have hc := congr($(congrArg (fun m ↦ HomologicalComplex.homologyMap m (n : ℤ))
    (abelianOpenUnitCochainIso_naturality X U g)) x)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  change HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)
      (HomologicalComplex.homologyMap (abelianOpenUnitCochainIso X U I).hom (n : ℤ) x) =
    HomologicalComplex.homologyMap (abelianOpenUnitCochainIso X U J).hom (n : ℤ)
      (HomologicalComplex.homologyMap (homComplexPostcomp L g) (n : ℤ) x) at hc
  rw [hc]
  have hz := homologyAddEquiv_postcomp_mk L g (n : ℤ) z
  rw [← hz, AddEquiv.symm_apply_apply]

private structure AbelianInjectiveModel (F : AbelianSheaves X) where
  complex : CochainComplex (AbelianSheaves X) ℤ
  lowerBound : complex.IsStrictlyGE 0
  augmentation : abelianStalk X F ⟶ complex
  mono : Mono augmentation
  quasiIso : QuasiIso augmentation
  injective : ∀ q : ℤ, Injective (complex.X q)

private def abelianInjectiveModel (F : AbelianSheaves X) : AbelianInjectiveModel X F :=
  Classical.choice (by
    obtain ⟨I, ι, hm, hι, hI, hb⟩ := InjectiveComplexReplacement.replacement
      (AbelianSheaves X) (abelianStalk X F) 0 (by dsimp [abelianStalk]; infer_instance)
    exact ⟨⟨I, hb, ι, HomologicalComplex.mono_of_mono_f ι hm, hι, hI⟩⟩)

private def classExtEquiv {F : AbelianSheaves X}
    {I : CochainComplex (AbelianSheaves X) ℤ} [I.IsStrictlyGE 0]
    (ι : abelianStalk X F ⟶ I) (hι : QuasiIso ι) (hI : ∀ q, Injective (I.X q))
    (n : ℕ) :
    CohomologyClass (openUnitStalk X U) I (n : ℤ) ≃+ abelianExt X U F n :=
  (HomComplex.homologyAddEquiv (openUnitStalk X U) I (n : ℤ)).symm.trans
    (Classical.choose (ExtShiftedHom.injective_comparison (AbelianSheaves X)
      (abelianOpenUnit X U) F I ι hι
      ⟨0, fun q hq ↦ I.isZero_of_isStrictlyGE 0 q hq⟩ hI (n : ℤ)))

private lemma classExtEquiv_apply {F : AbelianSheaves X}
    {I : CochainComplex (AbelianSheaves X) ℤ} [I.IsStrictlyGE 0]
    (ι : abelianStalk X F ⟶ I) (hι : QuasiIso ι) (hI : ∀ q, Injective (I.X q))
    (n : ℕ) (z : CohomologyClass (openUnitStalk X U) I (n : ℤ)) :
    classExtEquiv X U ι hι hI n z = injectiveClassMap (abelianOpenUnit X U) F I ι hι (n : ℤ) z :=
  Classical.choose_spec (ExtShiftedHom.injective_comparison (AbelianSheaves X)
    (abelianOpenUnit X U) F I ι hι
    ⟨0, fun q hq ↦ I.isZero_of_isStrictlyGE 0 q hq⟩ hI (n : ℤ)) z

private lemma injectiveClassMap_postcomp {F G : AbelianSheaves X}
    {I J : CochainComplex (AbelianSheaves X) ℤ}
    (ι : abelianStalk X F ⟶ I) (hι : QuasiIso ι)
    (κ : abelianStalk X G ⟶ J) (hκ : QuasiIso κ)
    (f : F ⟶ G) (g : I ⟶ J)
    (h : ι ≫ g = (CochainComplex.singleFunctor (AbelianSheaves X) 0).map f ≫ κ)
    (n : ℕ) (z : Cocycle (openUnitStalk X U) I (n : ℤ)) :
    injectiveClassMap (abelianOpenUnit X U) G J κ hκ (n : ℤ) (CohomologyClass.mk (z.postcomp g)) =
      extMap (𝟙 (abelianOpenUnit X U)) f (n : ℤ)
        (injectiveClassMap (abelianOpenUnit X U) F I ι hι (n : ℤ) (CohomologyClass.mk z)) := by
  have hh : Nonempty (Homotopy (ι ≫ g)
      ((CochainComplex.singleFunctor (AbelianSheaves X) 0).map f ≫ κ)) :=
    ⟨Homotopy.ofEq h⟩
  have hz : z.precomp ((CochainComplex.singleFunctor (AbelianSheaves X) 0).map
      (𝟙 (abelianOpenUnit X U))) = z := by
    rw [CategoryTheory.Functor.map_id]
    apply Cocycle.ext
    exact Cochain.id_comp (z : Cochain (openUnitStalk X U) I (n : ℤ))
  simpa only [hz] using ExtShiftedHom.injective_natural (AbelianSheaves X)
    (abelianOpenUnit X U) (abelianOpenUnit X U) F G I J ι κ hι hκ
    (𝟙 (abelianOpenUnit X U)) f g hh (n : ℤ) z

private def sectionExtEquiv (F : AbelianSheaves X) (n : ℕ) :
    (abelianCohomology X U n).obj F ≃+ abelianExt X U F n := by
  let P := abelianInjectiveModel X F
  letI := P.lowerBound
  exact (sectionClassEquiv X U P.augmentation P.quasiIso P.injective n).symm.trans
    (classExtEquiv X U P.augmentation P.quasiIso P.injective n)

private lemma sectionExtEquiv_model (F : AbelianSheaves X)
    (I : CochainComplex (AbelianSheaves X) ℤ) [I.IsStrictlyGE 0]
    (ι : abelianStalk X F ⟶ I) (hι : QuasiIso ι) (hI : ∀ q, Injective (I.X q))
    (n : ℕ) (x : CohomologyClass (openUnitStalk X U) I (n : ℤ)) :
    sectionExtEquiv X U F n (sectionClassEquiv X U ι hι hI n x) =
      injectiveClassMap (abelianOpenUnit X U) F I ι hι (n : ℤ) x := by
  let P := abelianInjectiveModel X F
  letI := P.lowerBound
  letI := P.mono
  letI := P.quasiIso
  obtain ⟨g, hg⟩ := injectiveResolutionLift P.augmentation ι hI
  have hg' : P.augmentation ≫ g =
      (CochainComplex.singleFunctor (AbelianSheaves X) 0).map (𝟙 F) ≫ ι := by
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using hg
  obtain ⟨y, hy⟩ := (CohomologyClass.mk_surjective (K := openUnitStalk X U)
    (L := P.complex) (n := (n : ℤ)))
    ((sectionClassEquiv X U P.augmentation P.quasiIso P.injective n).symm
      (sectionClassEquiv X U ι hι hI n x))
  have hxy : CohomologyClass.mk (y.postcomp g) = x := by
    apply (sectionClassEquiv X U ι hι hI n).injective
    rw [← sectionClassEquiv_postcomp X U P.augmentation P.quasiIso P.injective
      ι hι hI (𝟙 F) g hg' n y, CategoryTheory.Functor.map_id]
    change sectionClassEquiv X U P.augmentation P.quasiIso P.injective n
      (CohomologyClass.mk y) = _
    rw [hy, AddEquiv.apply_symm_apply]
  change classExtEquiv X U P.augmentation P.quasiIso P.injective n
    ((sectionClassEquiv X U P.augmentation P.quasiIso P.injective n).symm
      (sectionClassEquiv X U ι hι hI n x)) = _
  rw [← hy, classExtEquiv_apply, ← hxy]
  have hh := injectiveClassMap_postcomp X U P.augmentation P.quasiIso ι hι
    (𝟙 F) g hg' n y
  simpa only [extMap, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using hh.symm

/-- On the common injective model, the open-unit representation identifies
the section cochains with homomorphisms from the open unit in every degree. -/
theorem ext : Specs.AdvancedHomologicalAlgebra.SheafCohomology.extType.{u} := by
  intro X U
  refine ⟨sectionExtEquiv X U, ?_, ?_⟩
  · intro F G f n x
    let P := abelianInjectiveModel X F
    let Q := abelianInjectiveModel X G
    letI := P.lowerBound
    letI := P.mono
    letI := P.quasiIso
    letI := Q.lowerBound
    obtain ⟨g, hg⟩ := injectiveResolutionLift P.augmentation
      ((CochainComplex.singleFunctor (AbelianSheaves X) 0).map f ≫ Q.augmentation) Q.injective
    obtain ⟨y, hy⟩ := (CohomologyClass.mk_surjective (K := openUnitStalk X U)
      (L := P.complex) (n := (n : ℤ)))
      ((sectionClassEquiv X U P.augmentation P.quasiIso P.injective n).symm x)
    have hx : sectionClassEquiv X U P.augmentation P.quasiIso P.injective n
        (CohomologyClass.mk y) = x := by rw [hy, AddEquiv.apply_symm_apply]
    rw [← hx, sectionClassEquiv_postcomp X U P.augmentation P.quasiIso P.injective
      Q.augmentation Q.quasiIso Q.injective f g hg, sectionExtEquiv_model, sectionExtEquiv_model]
    exact injectiveClassMap_postcomp X U P.augmentation P.quasiIso Q.augmentation
      Q.quasiIso f g hg n y
  · intro F I hb ι hι hI
    exact ⟨abelianOpenUnitCochainIso X U I, abelianOpenUnitCochainIso_eval X U I,
      fun n x ↦ sectionExtEquiv_model X U F I ι hι hI n x⟩

end ExtComparison

end AdvancedHomologicalAlgebra.SheafCohomology
