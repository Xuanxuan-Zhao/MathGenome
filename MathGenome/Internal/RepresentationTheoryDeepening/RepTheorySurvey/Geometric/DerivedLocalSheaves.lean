import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicTermComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedLocalSheaves
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SheafModels
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite TopologicalSpace Topology
open scoped ZeroObject

universe u

namespace RepTheorySurvey.Geometric.DerivedLocalSheaves

open Analytic LocalSheaf

theorem inverseImageExact : LocalSheaf.Expected.InverseImageExact.{u} := by
  intro X Y m S h
  have hExact : ∀ T : ShortComplex (Sheaves X), T.ShortExact →
      (T.map (inverseImage m)).ShortExact :=
    ((inverseImage m).exact_tfae.out 4 1).mp
      (show PreservesFiniteLimits (inverseImage m) ∧ PreservesFiniteColimits (inverseImage m)
        from ⟨inferInstance, inferInstance⟩)
  exact hExact S h

theorem stalkExact : LocalSheaf.Expected.StalkExact.{u} := by
  intro X x S h
  have hExact : ∀ T : ShortComplex (Sheaves X), T.ShortExact → (T.map (stalk x)).ShortExact :=
    ((stalk x).exact_tfae.out 2 1).mp (SheafModels.stalkExact x)
  exact hExact S h

def closedDirectImageFullyFaithful : LocalSheaf.Expected.ClosedDirectImageFullyFaithful.{u} :=
  fun Z => Analytic.closedDirectImageFullyFaithful Z

theorem supportedEssentialImage : LocalSheaf.Expected.SupportedEssentialImage.{u} :=
  SheafModels.supportedEssentialImage

instance stalkPreservesHomology {X : TopCat.{u}} (x : X) : (stalk x).PreservesHomology :=
  ((stalk x).exact_tfae.out 2 3).mp (SheafModels.stalkExact x)

instance presheafStalkPreservesHomology {X : TopCat.{u}} (x : X) :
    (TopCat.Presheaf.stalkFunctor Coeff.{u} x).PreservesHomology := by
  unfold TopCat.Presheaf.stalkFunctor
  let R := (Functor.whiskeringLeft _ _ Coeff.{u}).obj (OpenNhds.inclusion x).op
  let L : ((OpenNhds x)ᵒᵖ ⥤ Coeff.{u}) ⥤ Coeff.{u} := colim
  have : PreservesFiniteLimits (R ⋙ L) := comp_preservesFiniteLimits R L
  have : PreservesFiniteColimits (R ⋙ L) := comp_preservesFiniteColimits R L
  exact inferInstanceAs ((R ⋙ L).PreservesHomology)

open private stalkPushforward_naturality
  from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

private def stalkDirectImageIso {Y X : TopCat.{u}} (m : Y ⟶ X) (hm : IsInducing m)
    (y : Y) : directImage m ⋙ stalk (m y) ≅ stalk y :=
  NatIso.ofComponents (fun F =>
    letI := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      Coeff.{u} hm F.obj y
    asIso (TopCat.Presheaf.stalkPushforward Coeff.{u} m F.obj y))
    (fun f => stalkPushforward_naturality m f.hom y)

theorem closedDirectImagePreservesHomology {X : TopCat.{u}} {Z : Set X}
    (hZ : IsClosed Z) : (directImage (closedInclusion Z)).PreservesHomology := by
  let i := closedInclusion Z
  apply ((directImage i).exact_tfae.out 2 3).mp
  intro S h
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  by_cases hx : x ∈ Z
  · let z : Z := ⟨x, hx⟩
    change (S.map (directImage i ⋙ stalk (i z))).Exact
    exact (ShortComplex.exact_iff_of_iso (S.mapNatIso (stalkDirectImageIso i
      IsInducing.subtypeVal z))).mpr (h.map (stalk z))
  · apply ShortComplex.exact_of_isZero_X₂
    exact closedDirectImage_supported hZ S.X₂ x hx

theorem closedDirectImageExact : LocalSheaf.Expected.ClosedDirectImageExact.{u} := by
  intro X Z hZ S h
  letI := closedDirectImagePreservesHomology hZ
  have hExact : ∀ T : ShortComplex (Sheaves (TopCat.of Z)), T.ShortExact →
      (T.map (directImage (closedInclusion Z))).ShortExact :=
    ((directImage (closedInclusion Z)).exact_tfae.out 3 1).mp
      (show (directImage (closedInclusion Z)).PreservesHomology from inferInstance)
  exact hExact S h

private def sectionCohomologyIso {J C : Type*} [Category* J] [Category* C] [Abelian C]
    (P : CochainComplex (J ⥤ C) ℤ) (q : ℤ) :
    P.asFunctor ⋙ HomologicalComplex.homologyFunctor _ _ q ≅ P.homology q := by
  let ev := evaluation J C
  letI (U : J) : (ev.obj U).Additive := inferInstanceAs (((evaluation J C).obj U).Additive)
  letI (U : J) : PreservesFiniteLimits (ev.obj U) :=
    inferInstanceAs (PreservesFiniteLimits ((evaluation J C).obj U))
  letI (U : J) : PreservesFiniteColimits (ev.obj U) :=
    inferInstanceAs (PreservesFiniteColimits ((evaluation J C).obj U))
  refine NatIso.ofComponents (fun U => (P.sc q).mapHomologyIso (ev.obj U)) ?_
  intro U V f
  let τ : ev.obj U ⟶ ev.obj V := ev.map f
  change ShortComplex.homologyMap ((P.sc q).mapNatTrans τ) ≫
    ((P.sc q).mapHomologyIso (ev.obj V)).hom =
    ((P.sc q).mapHomologyIso (ev.obj U)).hom ≫ τ.app (P.sc q).homology
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def stalkSectionCohomologyIso {X : TopCat.{u}} (K : CochainComplex (Sheaves X) ℤ)
    (x : X) (q : ℤ) :
    (stalk x).obj (K.homology q) ≅ stalkColimit (openSectionCohomology K q) x := by
  let P := ((TopCat.Sheaf.forget Coeff.{u} X).mapHomologicalComplex (.up ℤ)).obj K
  let T := TopCat.Presheaf.stalkFunctor Coeff.{u} x
  exact ((K.sc q).mapHomologyIso (stalk x)).symm ≪≫
    ((P.sc q).mapHomologyIso T) ≪≫
    T.mapIso (sectionCohomologyIso P q).symm

private def plusHomologyFactors (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory C] (q : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C q ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.QCompιIso C) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C q)

private def derivedRepresentative {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (T : C ⥤ D) [T.Additive] (I : CochainComplex.Plus (InjectiveObject C))
    {F : DerivedCategory.Plus C} (e : DerivedCategory.Plus.Q.obj (injectiveComplex I) ≅ F) :
    DerivedCategory.Plus.Q.obj (T.mapCochainComplexPlus.obj (injectiveComplex I)) ≅
      T.rightDerivedFunctorPlus.obj F :=
  asIso (T.rightDerivedFunctorPlusUnit.app (injectiveComplex I)) ≪≫
    T.rightDerivedFunctorPlus.mapIso e

private def derivedCohomologyIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (T : C ⥤ D) [T.Additive] (I : CochainComplex.Plus (InjectiveObject C))
    (q : ℤ) (F : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj (injectiveComplex I) ≅ F) :
    (DerivedCategory.Plus.homologyFunctor _ q).obj (T.rightDerivedFunctorPlus.obj F) ≅
      ((T.mapCochainComplexPlus.obj (injectiveComplex I)).obj).homology q :=
  (DerivedCategory.Plus.homologyFunctor _ q).mapIso (derivedRepresentative T I e).symm ≪≫
    (plusHomologyFactors D q).app _

private lemma derivedRepresentative_naturality {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    {T S : C ⥤ D} [T.Additive] [S.Additive] (τ : T ⟶ S)
    (I : CochainComplex.Plus (InjectiveObject C))
    {F : DerivedCategory.Plus C} (e : DerivedCategory.Plus.Q.obj (injectiveComplex I) ≅ F) :
    DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app (injectiveComplex I)) ≫
      (derivedRepresentative S I e).hom =
    (derivedRepresentative T I e).hom ≫ τ.rightDerivedFunctorPlus.app F := by
  dsimp only [derivedRepresentative, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [Category.assoc, ← NatTrans.rightDerivedFunctorPlus_fac_app_assoc,
    τ.rightDerivedFunctorPlus.naturality]

private lemma derivedCohomologyIso_inv_naturality {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    {T S : C ⥤ D} [T.Additive] [S.Additive] (τ : T ⟶ S)
    (I : CochainComplex.Plus (InjectiveObject C)) (q : ℤ)
    {F : DerivedCategory.Plus C} (e : DerivedCategory.Plus.Q.obj (injectiveComplex I) ≅ F) :
    HomologicalComplex.homologyMap (τ.mapCochainComplexPlus.app (injectiveComplex I)).hom q ≫
      (derivedCohomologyIso S I q F e).inv =
    (derivedCohomologyIso T I q F e).inv ≫
      (DerivedCategory.Plus.homologyFunctor D q).map (τ.rightDerivedFunctorPlus.app F) := by
  let H := DerivedCategory.Plus.homologyFunctor D q
  let f := τ.mapCochainComplexPlus.app (injectiveComplex I)
  change _ ≫ ((plusHomologyFactors D q).inv.app _ ≫ H.map (derivedRepresentative S I e).hom) =
    ((plusHomologyFactors D q).inv.app _ ≫ H.map (derivedRepresentative T I e).hom) ≫ _
  have hf := (plusHomologyFactors D q).inv.naturality f
  change HomologicalComplex.homologyMap f.hom q ≫
      (plusHomologyFactors D q).inv.app (S.mapCochainComplexPlus.obj (injectiveComplex I)) =
      (plusHomologyFactors D q).inv.app (T.mapCochainComplexPlus.obj (injectiveComplex I)) ≫
        H.map (DerivedCategory.Plus.Q.map f) at hf
  rw [← Category.assoc, hf]
  simp only [Category.assoc, ← Functor.map_comp, f, derivedRepresentative_naturality]
  rw [H.map_comp]

private theorem existsInjectiveRepresentative {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [EnoughInjectives C] (F : DerivedCategory.Plus C) :
    ∃ I : CochainComplex.Plus (InjectiveObject C),
      Nonempty (DerivedCategory.Plus.Q.obj (injectiveComplex I) ≅ F) := by
  obtain ⟨n, hn⟩ := F.property
  haveI : F.IsGE n := (F.isGE_ι_obj_iff n).mp hn
  obtain ⟨I, _, hI⟩ := F.exists_injective_nonempty_iso n
  exact ⟨I, hI⟩

theorem directImageStalk : LocalSheaf.Expected.DirectImageStalk.{u} := by
  intro Y X m x q F I e
  exact ⟨(stalk x).mapIso (derivedCohomologyIso (directImage m) I q F e) ≪≫
    stalkSectionCohomologyIso _ x q⟩

theorem extraordinaryInverseImageStalk : LocalSheaf.Expected.ExtraordinaryInverseImageStalk.{u} := by
  intro X Z hZ x q F I e
  let i := closedInclusion Z
  let K := ((extraordinaryInverseImage hZ).mapCochainComplexPlus.obj (injectiveComplex I)).obj
  letI := closedDirectImagePreservesHomology hZ
  exact ⟨(stalk (X := TopCat.of Z) x).mapIso
    (derivedCohomologyIso (extraordinaryInverseImage hZ) I q F e) ≪≫
    ((stalkDirectImageIso i IsInducing.subtypeVal x).app (K.homology q)).symm ≪≫
    (stalk x.val).mapIso
      ((K.sc q).mapHomologyIso (directImage i)).symm ≪≫
    stalkSectionCohomologyIso (((directImage i).mapHomologicalComplex (.up ℤ)).obj K) x.val q⟩

private def openCohomologyOfDerivedIso {X : TopCat.{u}} (T : Sheaves X ⥤ Sheaves X)
    [T.Additive] (I : CochainComplex.Plus (InjectiveObject (Sheaves X))) (q : ℤ) {F : BoundedBelow X}
    (e : DerivedCategory.Plus.Q.obj (injectiveComplex I) ≅ F) :
    openSectionCohomology (T.mapCochainComplexPlus.obj (injectiveComplex I)).obj q ≅
      derivedOpenCohomology T F q := by
  refine NatIso.ofComponents (fun U => (derivedCohomologyIso (T ⋙ sectionsOn U.unop) I q F e).symm) ?_
  intro U V f
  exact derivedCohomologyIso_inv_naturality (Functor.whiskerLeft T (sectionsRestriction f.unop)) I q e

theorem directImageCohomologyRestriction : LocalSheaf.Expected.DirectImageCohomologyRestriction.{u} := by
  intro Y X m q F I e
  exact ⟨Functor.isoWhiskerLeft (Opens.map m).op (openCohomologyOfDerivedIso (𝟭 _) I q e)⟩

theorem supportCohomologyRestriction : LocalSheaf.Expected.SupportCohomologyRestriction.{u} := by
  intro X Z hZ q F I e
  exact ⟨openCohomologyOfDerivedIso (extraordinaryInverseImage hZ ⋙ directImage _) I q e⟩

theorem higherDirectImageStalk : LocalSheaf.Expected.HigherDirectImageStalk.{u} := by
  intro Y X m x q F
  obtain ⟨I, ⟨e⟩⟩ := existsInjectiveRepresentative F
  obtain ⟨s⟩ := directImageStalk m x q F I e
  obtain ⟨d⟩ := directImageCohomologyRestriction m q F I e
  exact ⟨s ≪≫ (TopCat.Presheaf.stalkFunctor Coeff.{u} x).mapIso d⟩

theorem costalk : LocalSheaf.Expected.Costalk.{u} := by
  intro X Z hZ x q F
  obtain ⟨I, ⟨e⟩⟩ := existsInjectiveRepresentative F
  obtain ⟨s⟩ := extraordinaryInverseImageStalk hZ x q F I e
  obtain ⟨d⟩ := supportCohomologyRestriction hZ q F I e
  exact ⟨s ≪≫ (TopCat.Presheaf.stalkFunctor Coeff.{u} x.val).mapIso d⟩

private lemma openLanPreservesMonos {X : TopCat.{u}} (U : Opens X) :
    (U.isOpenEmbedding.functor.op.lan :
      (TopCat.of U).Presheaf Coeff.{u} ⥤ X.Presheaf Coeff.{u}).PreservesMonomorphisms where
  preserves {F G} f hf := by
    let L := U.isOpenEmbedding.functor.op
    haveI : Mono U.inclusion' := (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    rw [NatTrans.mono_iff_mono_app (L.lan.map f)]
    intro W
    by_cases hW : W.unop ≤ U
    · let V := (Opens.map U.inclusion').obj W.unop
      have hV : L.obj (op V) = W := by
        change op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj W.unop)) = W
        rw [U.functor_map_eq_inf, inf_eq_left.mpr hW, op_unop]
      rw [← hV]
      let eF := (L.lanUnit.app F).app (op V)
      let eG := (L.lanUnit.app G).app (op V)
      haveI : IsIso eF :=
        (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit F _).isIso_hom_app
      haveI : IsIso eG :=
        (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit G _).isIso_hom_app
      have hh : eF ≫ (L.lan.map f).app (L.obj (op V)) = f.app (op V) ≫ eG :=
        NatTrans.congr_app (L.lanUnit.naturality f).symm (op V)
      haveI : Mono (f.app (op V)) := (NatTrans.mono_iff_mono_app f).mp inferInstance _
      have he : (L.lan.map f).app (L.obj (op V)) = inv eF ≫ f.app (op V) ≫ eG := by
        rw [← hh, IsIso.inv_hom_id_assoc]
      rw [he]
      infer_instance
    · let A := CostructuredArrow L W
      haveI : IsEmpty A := ⟨fun a => hW (le_trans (leOfHom a.hom.unop) (by
        intro x hx
        obtain ⟨y, -, rfl⟩ := hx
        exact y.property))⟩
      let D := CostructuredArrow.proj L W ⋙ F
      let c : Cocone D := ⟨0, { app := fun a => isEmptyElim a }⟩
      let hc : IsColimit c :=
        { desc := fun _ => 0
          fac := fun _ a => isEmptyElim a
          uniq := fun _ m _ => (isZero_zero _).eq_of_src m 0 }
      let h := L.isPointwiseLeftKanExtensionLeftKanExtensionUnit F W
      exact mono_of_source_iso_zero _ (h.coconePointUniqueUpToIso hc)

theorem restrictionPreservesInjectives :
    LocalSheaf.Expected.RestrictionPreservesInjectives.{u} := by
  intro X U F hF
  let L := U.isOpenEmbedding.functor
  haveI : L.IsContinuous (Opens.grothendieckTopology (TopCat.of U))
      (Opens.grothendieckTopology X) :=
    Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let A := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous L Coeff.{u}
    (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X)
  let e := U.isOpenEmbedding.sheafPullbackIso Coeff.{u}
  haveI : L.op.lan.PreservesMonomorphisms := openLanPreservesMonos U
  haveI : (Functor.sheafPullbackConstruction.sheafPullback L Coeff.{u}
      (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X)).PreservesMonomorphisms := by
    unfold Functor.sheafPullbackConstruction.sheafPullback
    haveI : (sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U))
      Coeff.{u}).PreservesMonomorphisms := by infer_instance
    haveI : (presheafToSheaf (Opens.grothendieckTopology X)
      Coeff.{u}).PreservesMonomorphisms := by infer_instance
    exact Functor.preservesMonomorphisms_comp _ _
  exact (A.ofNatIsoRight e.symm).map_injective F hF

private def cochainAdjunction {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (a : L ⊣ R) :
    L.mapCochainComplexPlus ⊣ R.mapCochainComplexPlus where
  unit := a.unit.mapCochainComplexPlus
  counit := a.counit.mapCochainComplexPlus
  left_triangle_components K := by
    apply ObjectProperty.hom_ext
    ext n
    exact a.left_triangle_components (K.obj.X n)
  right_triangle_components K := by
    apply ObjectProperty.hom_ext
    ext n
    exact a.right_triangle_components (K.obj.X n)

private def exactPlusFactors {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] :
    DerivedCategory.Plus.Q ⋙ exactDerivedPlus L ≅ L.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  NatIso.ofComponents (fun K => DerivedCategory.Plus.ι.preimageIso (L.mapDerivedCategoryFactors.app K.obj))
    (by
      intro K M f
      apply DerivedCategory.Plus.ι.map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact L.mapDerivedCategoryFactors.hom.naturality f.hom)

private def exactRightDerivedAdjunction {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (a : L ⊣ R) :
    exactDerivedPlus L ⊣ R.rightDerivedFunctorPlus := by
  let α := exactPlusFactors L
  let β := R.rightDerivedFunctorPlusUnit
  let WC := CochainComplex.Plus.quasiIso C
  let WD := CochainComplex.Plus.quasiIso D
  haveI : (exactDerivedPlus L).IsLeftDerivedFunctor α.hom WC :=
    Functor.isLeftDerivedFunctor_of_inverts WC _ α
  haveI : ((exactDerivedPlus L) ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α.hom R.rightDerivedFunctorPlus) WC :=
    Functor.isLeftDerivedFunctor_of_inverts WC _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α R.rightDerivedFunctorPlus)
  haveI : (R.rightDerivedFunctorPlus ⋙ exactDerivedPlus L).IsRightDerivedFunctor
      (Functor.whiskerRight β (exactDerivedPlus L) ≫ (Functor.associator _ _ _).hom) WD := by
    let δ := Functor.whiskerRight β (exactDerivedPlus L) ≫ (Functor.associator _ _ _).hom
    have hDerives : (CochainComplex.Plus.localizerMorphism D).Derives
        ((R.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ exactDerivedPlus L) := by
      intro K M f hf
      haveI : IsIso ((R.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map
          ((CochainComplex.Plus.localizerMorphism D).functor.map f)) :=
        CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus R f hf
      exact Functor.map_isIso (exactDerivedPlus L) _
    exact hDerives.isRightDerivedFunctor_of_isIso δ (fun I => by
      dsimp [δ, β, CochainComplex.Plus.localizerMorphism]
      infer_instance)
  exact (cochainAdjunction a).derived WC WD α.hom β

/-- The adjunction giving the unit from pullback and derived direct image. -/
def derivedInverseDirectAdjunctionData {Y X : TopCat.{u}} (m : Y ⟶ X) :
    boundedBelowInverseImage m ⊣ derivedDirectImage m :=
  exactRightDerivedAdjunction (inverseDirectAdjunction m)

def derivedExtraordinaryAdjunctionData {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    closedExtensionPlus hZ ⊣ derivedExtraordinaryInverseImage hZ := by
  let a := extraordinaryAdjunction hZ
  letI := a.isLeftAdjoint
  exact exactRightDerivedAdjunction a

theorem derivedExtraordinaryAdjunction : LocalSheaf.Expected.DerivedExtraordinaryAdjunction.{u} :=
  fun hZ => ⟨derivedExtraordinaryAdjunctionData hZ⟩

private lemma isIsoDerivedUnitOfInjectives {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (T : C ⥤ D) [T.Additive] (K : CochainComplex.Plus C)
    (hK : ∀ n : ℤ, Injective (K.obj.X n)) :
    IsIso (T.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨n, hn⟩ := K.property
  let I : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty (isInjective C) K.obj hK
  have hI : I.IsStrictlyGE n := by
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι C)]
    exact hn
  exact inferInstanceAs (IsIso
    (T.rightDerivedFunctorPlusUnit.app (injectiveComplex (⟨I, n, hI⟩ : CochainComplex.Plus _))))

private def derivedPrecompIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [EnoughInjectives C] [EnoughInjectives D]
    {L : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (hL : ∀ I : C, Injective I → Injective (L.obj I))
    {T : C ⥤ E} {R : D ⥤ E} [T.Additive] [R.Additive] (e : T ≅ L ⋙ R) :
    T.rightDerivedFunctorPlus ≅ exactDerivedPlus L ⋙ R.rightDerivedFunctorPlus := by
  let ε : T.mapCochainComplexPlus ≅ (L ⋙ R).mapCochainComplexPlus :=
    { hom := e.hom.mapCochainComplexPlus
      inv := e.inv.mapCochainComplexPlus
      hom_inv_id := by rw [← NatTrans.mapCochainComplexPlus_comp, e.hom_inv_id,
        NatTrans.mapCochainComplexPlus_id]
      inv_hom_id := by rw [← NatTrans.mapCochainComplexPlus_comp, e.inv_hom_id,
        NatTrans.mapCochainComplexPlus_id] }
  let α : T.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ (exactDerivedPlus L ⋙ R.rightDerivedFunctorPlus) :=
    Functor.whiskerRight ε.hom _ ≫
    Functor.whiskerLeft L.mapCochainComplexPlus R.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight (exactPlusFactors L).inv R.rightDerivedFunctorPlus
  let W := CochainComplex.Plus.quasiIso C
  haveI : (exactDerivedPlus L ⋙ R.rightDerivedFunctorPlus).IsRightDerivedFunctor α W := by
    apply (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus T)
      |>.isRightDerivedFunctor_of_isIso
    intro I
    let K := injectiveComplex I
    have hI (n : ℤ) : Injective ((L.mapCochainComplexPlus.obj K).obj.X n) :=
      hL (K.obj.X n) (I.obj.X n).property
    haveI : IsIso (ε.hom.app K) := (ε.app K).isIso_hom
    haveI : IsIso (R.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K)) :=
      isIsoDerivedUnitOfInjectives R (L.mapCochainComplexPlus.obj K) hI
    haveI : IsIso ((exactPlusFactors L).inv.app K) :=
      ((exactPlusFactors L).app K).isIso_inv
    change IsIso (DerivedCategory.Plus.Q.map (ε.hom.app K) ≫ R.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K) ≫
      R.rightDerivedFunctorPlus.map ((exactPlusFactors L).inv.app K))
    infer_instance
  exact T.rightDerivedFunctorPlus.rightDerivedUnique _ T.rightDerivedFunctorPlusUnit α W

private def sectionsOnSubspaceIso {X : TopCat.{u}} (U : Opens X) (V : Opens (TopCat.of U)) :
    sectionsOn (U.isOpenEmbedding.functor.obj V) ≅
      inverseImage (openInclusion U) ⋙ sectionsOn V :=
  Functor.isoWhiskerRight (U.isOpenEmbedding.sheafPullbackIso Coeff.{u}).symm (sectionsOn V)

private def globalSectionsOnOpenIso {X : TopCat.{u}} (U : Opens X) :
    sectionsOn U ≅ inverseImage (openInclusion U) ⋙ globalSections (TopCat.of U) :=
  eqToIso (congrArg sectionsOn (U.isOpenEmbedding_obj_top).symm) ≪≫ sectionsOnSubspaceIso U ⊤

theorem openSectionsLocality : LocalSheaf.Expected.OpenSectionsLocality.{u} := by
  intro X U
  exact ⟨derivedPrecompIso (restrictionPreservesInjectives U) (globalSectionsOnOpenIso U)⟩

private def globalSectionsDirectIso {X Y : TopCat.{u}} (m : Y ⟶ X) :
    directImage m ⋙ globalSections X ≅ globalSections Y :=
  NatIso.ofComponents (fun F => F.obj.mapIso (eqToIso (congrArg op (Opens.map_top m))))
    (fun f => f.hom.naturality _ |>.symm)

theorem constantOpenRestriction : LocalSheaf.Expected.ConstantOpenRestriction.{u} := by
  intro X U
  let f := openInclusion U
  let a := constantSheafAdj (Opens.grothendieckTopology X) Coeff.{u} (isTerminalTop (α := Opens X))
  let b := constantSheafAdj (Opens.grothendieckTopology (TopCat.of U)) Coeff.{u}
    (isTerminalTop (α := Opens (TopCat.of U)))
  exact ⟨((a.comp (inverseDirectAdjunction f)).leftAdjointUniq
    (b.ofNatIsoRight (globalSectionsDirectIso f).symm)).app _⟩

private def freeRational : Type u ⥤ Coeff.{u} where
  obj S := ModuleCat.of ℚ (S →₀ ℚ)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain ℚ ℚ f)
  map_id _ := ModuleCat.hom_ext (Finsupp.lmapDomain_id ℚ ℚ)
  map_comp f g := ModuleCat.hom_ext (Finsupp.lmapDomain_comp ℚ ℚ f g)

private lemma rationalLift_single {S : Type u} {M : Type u} [AddCommGroup M] [Module ℚ M]
    (f : S → M) (x : S) : (Finsupp.lift M ℚ S f) (Finsupp.single x 1) = f x := by
  rw [Finsupp.lift_apply, Finsupp.sum_single_index]
  · simp
  · simp

private def freeRationalAdjunction : freeRational.{u} ⊣ CategoryTheory.forget Coeff.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun S M =>
        { toFun := fun f => ↾fun x => f (Finsupp.single x 1)
          invFun := fun g => ModuleCat.ofHom (Finsupp.lift M ℚ S g)
          left_inv := fun f => ModuleCat.hom_ext (Finsupp.lhom_ext' (fun x =>
            LinearMap.ext_ring (rationalLift_single (fun y : S => f.hom (Finsupp.single y 1)) x)))
          right_inv := fun g => by ext x; exact rationalLift_single g x }
      homEquiv_naturality_left_symm := by
        intro S T M f g
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext'
        intro x
        apply LinearMap.ext_ring
        simp [freeRational, Finsupp.mapDomain_single] }

theorem injectiveFlasque {X : TopCat.{u}} (F : Sheaves X) [Injective F] :
    TopCat.Sheaf.IsFlasque F := by
  let J := Opens.grothendieckTopology X
  let a := (freeRationalAdjunction.{u}.whiskerRight (Opens X)ᵒᵖ).comp
    (sheafificationAdjunction J Coeff.{u})
  let H : Opens X ⥤ Sheaves X := yoneda ⋙
    (Functor.whiskeringRight _ _ _).obj freeRational.{u} ⋙ presheafToSheaf J Coeff.{u}
  let rep (U : Opens X) : (H.obj U ⟶ F) ≃ F.obj.obj (op U) :=
    (a.homEquiv (yoneda.obj U) F).trans yonedaEquiv
  refine ⟨fun {U V} i => (ModuleCat.epi_iff_surjective _).mpr ?_⟩
  intro s
  let t := H.map i.unop
  have ht : Mono t := by
    let a₀ := ((Functor.whiskeringRight (Opens X)ᵒᵖ (Type u) Coeff.{u}).obj freeRational).map
      (yoneda.map i.unop)
    haveI : Mono a₀ := (NatTrans.mono_iff_mono_app a₀).mpr (fun W =>
      (ModuleCat.mono_iff_injective _).mpr
        (Finsupp.mapDomain_injective (fun x y _ =>
          Subsingleton.elim (α := W.unop ⟶ V.unop) x y)))
    exact (presheafToSheaf J Coeff.{u}).map_mono a₀
  let e := (rep V.unop).symm s
  let v := Injective.factorThru e t
  refine ⟨rep U.unop v, ?_⟩
  have hrep : rep V.unop (t ≫ v) = F.obj.map i (rep U.unop v) := by
    change yonedaEquiv (a.homEquiv _ F (H.map i.unop ≫ v)) =
      F.obj.map i (yonedaEquiv (a.homEquiv _ F v))
    have hn := a.homEquiv_naturality_left (yoneda.map i.unop) v
    exact (congrArg yonedaEquiv hn).trans
      (yonedaEquiv_naturality ((a.homEquiv (yoneda.obj U.unop) F) v) i.unop).symm
  rw [← hrep, Injective.comp_factorThru]
  exact (rep V.unop).apply_symm_apply s

private abbrev forgetCoefficients : Coeff.{u} ⥤ AddCommGrpCat.{u} := forget₂ _ _

private def forgetSheafCoefficients (X : TopCat.{u}) : Sheaves X ⥤ X.Sheaf AddCommGrpCat.{u} :=
  sheafCompose (Opens.grothendieckTopology X) forgetCoefficients

private instance (X : TopCat.{u}) : (forgetSheafCoefficients X).Additive where
  map_add := by intros; rfl

private def forgetStalkIso {X : TopCat.{u}} (x : X) :
    stalk x ⋙ forgetCoefficients ≅
      forgetSheafCoefficients X ⋙ TopCat.Sheaf.forget _ _ ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x :=
  Functor.isoWhiskerLeft (TopCat.Sheaf.forget Coeff.{u} X ⋙
    (Functor.whiskeringLeft _ _ Coeff.{u}).obj (OpenNhds.inclusion x).op)
    (preservesColimitNatIso forgetCoefficients)

private instance (X : TopCat.{u}) : (forgetSheafCoefficients X).PreservesHomology := by
  apply ((forgetSheafCoefficients X).exact_tfae.out 2 3).mp
  intro S hS
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  exact (ShortComplex.exact_iff_of_iso (S.mapNatIso (forgetStalkIso x))).mp
    ((hS.map (stalk x)).map forgetCoefficients)

private lemma forgetFlasque {X : TopCat.{u}} (F : Sheaves X) [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque ((forgetSheafCoefficients X).obj F) where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    ((ModuleCat.epi_iff_surjective (F.obj.map i)).mp inferInstance)

private lemma forgetSheafShortExact {X : TopCat.{u}} (S : ShortComplex (Sheaves X))
    (h : S.ShortExact) : (S.map (forgetSheafCoefficients X)).ShortExact := by
  have hExact : ∀ T : ShortComplex (Sheaves X), T.ShortExact →
      (T.map (forgetSheafCoefficients X)).ShortExact :=
    ((forgetSheafCoefficients X).exact_tfae.out 3 1).mp
      (show (forgetSheafCoefficients X).PreservesHomology from inferInstance)
  exact hExact S h

private lemma sectionsSurjectiveOfFlasque {X : TopCat.{u}} {S : ShortComplex (Sheaves X)}
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] (U : Opens X) :
    Function.Surjective (((sectionsOn U).map S.g)) := by
  let T := S.map (forgetSheafCoefficients X)
  have hT : T.ShortExact := forgetSheafShortExact S hS
  letI : TopCat.Sheaf.IsFlasque T.X₁ := forgetFlasque S.X₁
  exact (AddCommGrpCat.epi_iff_surjective _).mp
    (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hT)

private lemma flasqueQuotient {X : TopCat.{u}} {S : ShortComplex (Sheaves X)}
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] [TopCat.Sheaf.IsFlasque S.X₂] :
    TopCat.Sheaf.IsFlasque S.X₃ where
  epi i := by
    let T := S.map (forgetSheafCoefficients X)
    have hT : T.ShortExact := forgetSheafShortExact S hS
    letI : TopCat.Sheaf.IsFlasque T.X₁ := forgetFlasque S.X₁
    letI : TopCat.Sheaf.IsFlasque T.X₂ := forgetFlasque S.X₂
    haveI : TopCat.Sheaf.IsFlasque T.X₃ := TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hT
    exact (ModuleCat.epi_iff_surjective _).mpr
      ((AddCommGrpCat.epi_iff_surjective (T.X₃.obj.map i)).mp inferInstance)

private def supportedSectionsKernelIso {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (U : Opens X) (F : Sheaves X) :
    (supportedSectionsOn hZ U).obj F ≅ kernel ((restrictionOffClosed hZ U).app F) :=
  (sectionsOn U).mapIso ((supportedImageIso hZ).app F).symm ≪≫
    Classical.choose (SheafModels.supportSectionsKernel hZ U F)

@[reassoc]
private lemma supportedSectionsKernelIso_hom {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (U : Opens X) (F : Sheaves X) :
    (supportedSectionsKernelIso hZ U F).hom ≫ kernel.ι ((restrictionOffClosed hZ U).app F) =
      (supportedSectionsInclusion hZ U).app F := by
  dsimp only [supportedSectionsKernelIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [Category.assoc]
  erw [Classical.choose_spec (SheafModels.supportSectionsKernel hZ U F)]
  simp [supportedSectionsInclusion]

private def restrictionSequence {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X)
    (F : Sheaves X) : ShortComplex Coeff.{u} :=
  ShortComplex.mk ((supportedSectionsInclusion hZ U).app F)
    ((restrictionOffClosed hZ U).app F) (by rw [← supportedSectionsKernelIso_hom]; simp)

private def restrictionSequenceKernel {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (U : Opens X) (F : Sheaves X) :
    IsLimit (KernelFork.ofι (restrictionSequence hZ U F).f (restrictionSequence hZ U F).zero) :=
  IsLimit.ofIsoLimit (kernelIsKernel _)
    (Fork.ext (supportedSectionsKernelIso hZ U F) (supportedSectionsKernelIso_hom hZ U F)).symm

private lemma restrictionSequenceShortExact {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (U : Opens X) (F : Sheaves X) [TopCat.Sheaf.IsFlasque F] :
    (restrictionSequence hZ U F).ShortExact := by
  have hK := restrictionSequenceKernel hZ U F
  exact { exact := ShortComplex.exact_of_f_is_kernel _ hK
          mono_f := mono_of_isLimit_fork hK
          epi_g := inferInstanceAs (Epi (F.obj.map (homOfLE inf_le_left :
            U ⊓ complementOpen Z hZ ⟶ U).op)) }

private def restrictionComplex {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) (U : Opens X)
    (K : CochainComplex.Plus (Sheaves X)) : ShortComplex (CochainComplex Coeff.{u} ℤ) :=
  ShortComplex.mk ((supportedSectionsInclusion hZ U).mapCochainComplexPlus.app K).hom
    ((restrictionOffClosed hZ U).mapCochainComplexPlus.app K).hom (by
      apply HomologicalComplex.hom_ext
      intro n
      exact (restrictionSequence hZ U (K.obj.X n)).zero)

private lemma restrictionComplexShortExact {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (U : Opens X) (K : CochainComplex.Plus (Sheaves X))
    (hK : ∀ n : ℤ, TopCat.Sheaf.IsFlasque (K.obj.X n)) : (restrictionComplex hZ U K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => by
    haveI := hK n
    exact restrictionSequenceShortExact hZ U (K.obj.X n))

theorem supportedSectionsRestrictionTriangle :
    LocalSheaf.Expected.SupportedSectionsRestrictionTriangle.{u} := by
  intro X Z hZ U F
  obtain ⟨I, ⟨e⟩⟩ := existsInjectiveRepresentative F
  let K := injectiveComplex I
  let S := restrictionComplex hZ U K
  have hS : S.ShortExact := restrictionComplexShortExact hZ U K
    (fun n => by
      haveI : Injective (K.obj.X n) := (I.obj.X n).property
      exact injectiveFlasque (K.obj.X n))
  let L := DerivedCategory.Plus.ι (C := Coeff.{u})
  let e₁ := L.mapIso (derivedRepresentative (supportedSectionsOn hZ U) I e)
  let e₂ := L.mapIso (derivedRepresentative (sectionsOn U) I e)
  let e₃ := L.mapIso (derivedRepresentative (sectionsOn (U ⊓ complementOpen Z hZ)) I e)
  let δ := e₃.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e₁.hom⟦(1 : ℤ)⟧'
  refine ⟨δ, (distinguished_iff_of_iso ?_).mp (DerivedCategory.triangleOfSES_distinguished hS)⟩
  refine Triangle.isoMk (DerivedCategory.triangleOfSES hS) _ e₁ e₂ e₃ ?_ ?_ ?_
  · exact congrArg L.map
      (derivedRepresentative_naturality (supportedSectionsInclusion hZ U) I e)
  · exact congrArg L.map
      (derivedRepresentative_naturality (restrictionOffClosed hZ U) I e)
  · dsimp [δ]
    simp only [Iso.hom_inv_id_assoc]
    rfl

private def sectionsCompare {X : TopCat.{u}} (U : Opens X) (V : Opens (TopCat.of U))
    (W : Opens X) (hW : U.isOpenEmbedding.functor.obj V = W) :
    sectionsOn W ≅ inverseImage (openInclusion U) ⋙ sectionsOn V :=
  eqToIso (congrArg sectionsOn hW.symm) ≪≫ sectionsOnSubspaceIso U V

private lemma sectionsCompare_naturality {X : TopCat.{u}} (U : Opens X)
    {V₁ V₂ : Opens (TopCat.of U)} {W₁ W₂ : Opens X}
    (h₁ : U.isOpenEmbedding.functor.obj V₁ = W₁)
    (h₂ : U.isOpenEmbedding.functor.obj V₂ = W₂)
    (i : V₁ ⟶ V₂) (j : W₁ ⟶ W₂) (F : Sheaves X) :
    (sectionsRestriction j).app F ≫ (sectionsCompare U V₁ W₁ h₁).hom.app F =
      (sectionsCompare U V₂ W₂ h₂).hom.app F ≫
        (sectionsRestriction i).app ((inverseImage (openInclusion U)).obj F) := by
  subst W₁
  subst W₂
  have hj : j = U.isOpenEmbedding.functor.map i := Subsingleton.elim _ _
  subst j
  exact ((U.isOpenEmbedding.sheafPullbackIso Coeff.{u}).inv.app F).hom.naturality i.op

private def supportedSectionsOnOpenIso {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (U : Opens X) : supportedSectionsOn hZ U ≅ inverseImage (openInclusion U) ⋙
      supportedSectionsOn (closedSetOnOpen_isClosed hZ U) ⊤ := by
  let j := inverseImage (openInclusion U)
  let Z' := closedSetOnOpen U Z
  let hZ' := closedSetOnOpen_isClosed hZ U
  let V₁ : Opens (TopCat.of U) := ⊤ ⊓ complementOpen Z' hZ'
  let W₁ := U ⊓ complementOpen Z hZ
  have hV : U.isOpenEmbedding.functor.obj V₁ = W₁ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy.2⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, ⟨trivial, hx.2⟩, rfl⟩
  let e₁ := sectionsCompare U V₁ W₁ hV
  let e₂ := sectionsCompare U ⊤ U U.isOpenEmbedding_obj_top
  let r := restrictionOffClosed hZ U
  let r' := restrictionOffClosed (X := TopCat.of U) (Z := Z') hZ' ⊤
  let k (F : Sheaves X) :
      kernel (r.app F) ≅ kernel (r'.app (j.obj F)) :=
    kernel.mapIso _ _ (e₂.app F) (e₁.app F)
      (sectionsCompare_naturality U hV U.isOpenEmbedding_obj_top _ _ F)
  let e (F : Sheaves X) : (supportedSectionsOn hZ U).obj F ≅
      (supportedSectionsOn hZ' ⊤).obj (j.obj F) :=
    supportedSectionsKernelIso hZ U F ≪≫ k F ≪≫
      (supportedSectionsKernelIso hZ' ⊤ (j.obj F)).symm
  have he (F : Sheaves X) : (e F).hom ≫ (supportedSectionsInclusion hZ' ⊤).app (j.obj F) =
      (supportedSectionsInclusion hZ U).app F ≫ e₂.hom.app F := by
    rw [← supportedSectionsKernelIso_hom hZ' ⊤, ← supportedSectionsKernelIso_hom hZ U]
    simp [e, k, Category.assoc]
    exact kernel.lift_ι _ _ _
  refine NatIso.ofComponents e ?_
  intro F G f
  haveI : Mono ((supportedSectionsInclusion hZ' ⊤).app (j.obj G)) := by
    rw [← supportedSectionsKernelIso_hom]
    infer_instance
  apply (cancel_mono ((supportedSectionsInclusion hZ' ⊤).app (j.obj G))).mp
  change _ ≫ (e G).hom ≫ (supportedSectionsInclusion hZ' ⊤).app (j.obj G) =
    ((e F).hom ≫ (supportedSectionsOn hZ' ⊤).map (j.map f)) ≫ _
  rw [he, Category.assoc,
    (supportedSectionsInclusion (X := TopCat.of U) (Z := Z') hZ' ⊤).naturality, ← Category.assoc,
    (supportedSectionsInclusion hZ U).naturality, Category.assoc, e₂.hom.naturality]
  have hn := congrArg (fun t => t ≫ (sectionsOn (X := TopCat.of U) ⊤).map (j.map f)) (he F)
  simpa only [Category.assoc, Functor.comp_map] using hn.symm

theorem supportedSectionsLocality : LocalSheaf.Expected.SupportedSectionsLocality.{u} := by
  intro X Z hZ U
  exact ⟨derivedPrecompIso (restrictionPreservesInjectives U) (supportedSectionsOnOpenIso hZ U)⟩

theorem derivedClosedExtensionFullyFaithful :
    LocalSheaf.Expected.DerivedClosedExtensionFullyFaithful.{u} := by
  intro X Z hZ
  let i := closedInclusion Z
  let L := inverseImage i
  let R := directImage i
  let a := inverseDirectAdjunction i
  haveI := (extraordinaryAdjunction hZ).isLeftAdjoint
  let G := exactDerivedPlus L
  let H := exactDerivedPlus R
  let α := exactPlusFactors L
  let β := (exactPlusFactors R).symm
  let WC := CochainComplex.Plus.quasiIso (Sheaves X)
  let WD := CochainComplex.Plus.quasiIso (Sheaves (TopCat.of Z))
  haveI : G.IsLeftDerivedFunctor α.hom WC := Functor.isLeftDerivedFunctor_of_inverts WC G α
  haveI : (G ⋙ H).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α.hom H) WC :=
    Functor.isLeftDerivedFunctor_of_inverts WC _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α H)
  haveI : H.IsRightDerivedFunctor β.hom WD := Functor.isRightDerivedFunctor_of_inverts WD H β.symm
  haveI : (H ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight β.hom G ≫ (Functor.associator _ _ _).hom) WD :=
    Functor.isRightDerivedFunctor_of_inverts WD _
      ((Functor.isoWhiskerRight β G ≪≫ Functor.associator _ _ _).symm)
  let b := (cochainAdjunction a).derived WC WD α.hom β.hom
  haveI hCounit (F : BoundedBelow (TopCat.of Z)) : IsIso (b.counit.app F) := by
    let Q := DerivedCategory.Plus.Q (C := Sheaves (TopCat.of Z))
    obtain ⟨I, ⟨e⟩⟩ := existsInjectiveRepresentative F
    let K := injectiveComplex I
    rw [← NatTrans.isIso_app_iff_of_iso b.counit e]
    let c := (cochainAdjunction a).counit.app K
    haveI (n : ℤ) : IsIso (c.hom.f n) :=
      inducedCounit_isIso (f := i) IsInducing.subtypeVal (K.obj.X n)
    haveI : IsIso ((CochainComplex.Plus.ι (Sheaves (TopCat.of Z))).map c) :=
      HomologicalComplex.Hom.isIso_of_components c.hom
    haveI : IsIso c :=
      (CochainComplex.Plus.fullyFaithfulι (Sheaves (TopCat.of Z))).isIso_of_isIso_map c
    have h := (cochainAdjunction a).derivedε_fac_app WD α.hom β.hom K
    change G.map (β.hom.app K) ≫ b.counit.app (Q.obj K) =
      α.hom.app (R.mapCochainComplexPlus.obj K) ≫ Q.map c at h
    haveI : IsIso (α.hom.app (R.mapCochainComplexPlus.obj K)) :=
      (α.app (R.mapCochainComplexPlus.obj K)).isIso_hom
    haveI : IsIso (Q.map c) := Q.map_isIso c
    haveI : IsIso (β.hom.app K) := (β.app K).isIso_hom
    haveI : IsIso (G.map (β.hom.app K)) := G.map_isIso _
    haveI : IsIso (G.map (β.hom.app K) ≫ b.counit.app (Q.obj K)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (G.map (β.hom.app K)) _
  haveI := NatIso.isIso_of_isIso_app b.counit
  exact ⟨b.fullyFaithfulROfIsIsoCounit⟩

private def exactDerivedCohomologyIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (K : CochainComplex.Plus C) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D q).obj
      ((exactDerivedPlus L).obj (DerivedCategory.Plus.Q.obj K)) ≅ L.obj (K.obj.homology q) :=
  (DerivedCategory.Plus.homologyFunctor D q).mapIso ((exactPlusFactors L).app K) ≪≫
    (plusHomologyFactors D q).app (L.mapCochainComplexPlus.obj K) ≪≫
    (K.obj.sc q).mapHomologyIso L

theorem derivedSupportedEssentialImage : LocalSheaf.Expected.DerivedSupportedEssentialImage.{u} := by
  intro X Z hZ F
  let i := closedInclusion Z
  let L := inverseImage i
  let R := directImage i
  let a := inverseDirectAdjunction i
  haveI := (extraordinaryAdjunction hZ).isLeftAdjoint
  constructor
  · rintro ⟨G, ⟨e⟩⟩ q x hx
    obtain ⟨I, ⟨e₀⟩⟩ := existsInjectiveRepresentative G
    let K := injectiveComplex I
    let e' := (closedExtensionPlus hZ).mapIso e₀ ≪≫ e
    let H := DerivedCategory.Plus.homologyFunctor (Sheaves X) q
    let eH := (H.mapIso e').symm ≪≫ exactDerivedCohomologyIso R K q
    exact (closedDirectImage_supported hZ (K.obj.homology q) x hx).of_iso
      ((stalk x).mapIso eH)
  · intro h
    let Q := DerivedCategory.Plus.Q (C := Sheaves X)
    obtain ⟨I, ⟨e⟩⟩ := existsInjectiveRepresentative F
    let K := injectiveComplex I
    let f := (cochainAdjunction a).unit.app K
    haveI : QuasiIso f.hom := by
      rw [quasiIso_iff]
      intro q
      let H := DerivedCategory.Plus.homologyFunctor (Sheaves X) q
      let eH := ((plusHomologyFactors (Sheaves X) q).app K).symm ≪≫ H.mapIso e
      have hK : SupportedOn Z (K.obj.homology q) := fun x hx =>
        (h q x hx).of_iso ((stalk x).mapIso eH)
      haveI : IsIso (a.unit.app (K.obj.sc q).homology) :=
        closedInverseDirectUnit_isIso hZ (K.obj.homology q) hK
      rw [quasiIsoAt_iff_isIso_homologyMap]
      change IsIso (ShortComplex.homologyMap ((K.obj.sc q).mapNatTrans a.unit))
      rw [ShortComplex.homologyMap_mapNatTrans]
      infer_instance
    haveI : IsIso (Q.map f) := Localization.inverts DerivedCategory.Plus.Q
      (CochainComplex.Plus.quasiIso (Sheaves X)) f
      (show CochainComplex.Plus.quasiIso _ f from inferInstanceAs (QuasiIso f.hom))
    let e' := (exactPlusFactors R).app (L.mapCochainComplexPlus.obj K)
    exact ⟨DerivedCategory.Plus.Q.obj (L.mapCochainComplexPlus.obj K),
      ⟨e' ≪≫ (asIso (Q.map f)).symm ≪≫ e⟩⟩

section FlasqueCohomology

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
open AdvancedHomologicalAlgebra

private lemma positiveDerivedOpenSections {X : TopCat.{u}} (U : Opens X)
    (F : Sheaves X) (hF : TopCat.Sheaf.IsFlasque F) (n : ℕ) :
    IsZero ((rightValue (sectionsOn U) (n + 1)).obj F) := by
  let T := sectionsOn U
  let D := rightSystem T
  have hD : IsCohomological D :=
    UniversalDeltaFunctors.rightDelta (Sheaves X) Coeff.{u} T
  have vanish (I : Sheaves X) [Injective I] (k : ℕ) : IsZero ((D.value (k + 1)).obj I) :=
    ClassicalDerivedValues.rightInjectiveVanishing (Sheaves X) Coeff.{u} T I k
  induction n generalizing F with
  | zero =>
    let S := UniversalDeltaFunctors.injectiveSequence F
    have hS : S.ShortExact := UniversalDeltaFunctors.injectiveSequence_shortExact F
    haveI : TopCat.Sheaf.IsFlasque S.X₁ := hF
    haveI : Epi (T.map S.g) := (ModuleCat.epi_iff_surjective _).mpr
      (sectionsSurjectiveOfFlasque hS U)
    haveI : IsIso (rightDegreeZeroUnit T) := ClassicalDerivedValues.rightZero (Sheaves X) Coeff.{u} T
    haveI : Epi ((D.value 0).map S.g) := by
      change Epi ((rightValue T 0).map S.g)
      exact epi_of_epi_fac ((rightDegreeZeroUnit T).naturality S.g).symm
    haveI : Epi (D.δ hS 0) := UniversalDeltaFunctors.dimensionShift_epi D hD vanish F 0
    exact IsZero.of_epi_eq_zero (D.δ hS 0)
      (zero_of_epi_comp ((D.value 0).map S.g) (hD.exact₃ hS 0).zero)
  | succ n ih =>
    let S := UniversalDeltaFunctors.injectiveSequence F
    have hS : S.ShortExact := UniversalDeltaFunctors.injectiveSequence_shortExact F
    haveI : TopCat.Sheaf.IsFlasque S.X₁ := hF
    haveI : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
    haveI : TopCat.Sheaf.IsFlasque S.X₂ := injectiveFlasque S.X₂
    haveI : Epi (D.δ hS (n + 1)) :=
      UniversalDeltaFunctors.dimensionShift_epi D hD vanish F (n + 1)
    exact IsZero.of_epi (D.δ hS (n + 1)) (ih S.X₃ (flasqueQuotient hS))

private lemma isIsoDerivedSectionsOfFlasque {X : TopCat.{u}} (U : Opens X)
    (K : CochainComplex.Plus (Sheaves X)) (hK : ∀ n : ℤ, TopCat.Sheaf.IsFlasque (K.obj.X n)) :
    IsIso ((sectionsOn U).rightDerivedFunctorPlusUnit.app K) := by
  let T := sectionsOn U
  let K' := (HomotopyCategory.Plus.quotient _).obj K
  have hA (n : ℤ) : rightAcyclicValue T (K'.obj.as.X n) :=
    (AcyclicTermComparison.rightVanishing (Sheaves X) Coeff.{u} T _).mpr
      (positiveDerivedOpenSections U _ (hK n))
  haveI : IsIso (T.rightDerivedFunctorPlusUnith.app K') :=
    AcyclicTermComparison.rightComparison (Sheaves X) Coeff.{u} T K' hA
  change IsIso (T.rightDerivedFunctorPlusUnit.app K)
  simp only [Functor.rightDerivedFunctorPlusUnit_app]
  infer_instance

end FlasqueCohomology

private lemma isIsoMapResolution {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (T : C ⥤ D) [T.Additive] {K J : CochainComplex.Plus C} (f : K ⟶ J)
    [IsIso (DerivedCategory.Plus.Q.map f)] [IsIso (T.rightDerivedFunctorPlusUnit.app K)]
    [IsIso (T.rightDerivedFunctorPlusUnit.app J)] :
    IsIso (DerivedCategory.Plus.Q.map (T.mapCochainComplexPlus.map f)) := by
  let Q := DerivedCategory.Plus.Q (C := D)
  have h := T.rightDerivedFunctorPlusUnit.naturality f
  change Q.map (T.mapCochainComplexPlus.map f) ≫ T.rightDerivedFunctorPlusUnit.app J =
    T.rightDerivedFunctorPlusUnit.app K ≫ T.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) at h
  haveI : IsIso (Q.map (T.mapCochainComplexPlus.map f) ≫ T.rightDerivedFunctorPlusUnit.app J) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (T.rightDerivedFunctorPlusUnit.app J)

private def restrictionComplexMap {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (U : Opens X) {K L : CochainComplex.Plus (Sheaves X)} (f : K ⟶ L) :
    restrictionComplex hZ U K ⟶ restrictionComplex hZ U L where
  τ₁ := ((supportedSectionsOn hZ U).mapCochainComplexPlus.map f).hom
  τ₂ := ((sectionsOn U).mapCochainComplexPlus.map f).hom
  τ₃ := ((sectionsOn (U ⊓ complementOpen Z hZ)).mapCochainComplexPlus.map f).hom
  comm₁₂ := congrArg (fun k => k.hom) ((supportedSectionsInclusion hZ U).mapCochainComplexPlus.naturality f)
  comm₂₃ := congrArg (fun k => k.hom) ((restrictionOffClosed hZ U).mapCochainComplexPlus.naturality f)

theorem supportedSectionsFlasqueResolution :
    LocalSheaf.Expected.SupportedSectionsFlasqueResolution.{u} := by
  intro X Z hZ U K hK
  let V := U ⊓ complementOpen Z hZ
  let T := supportedSectionsOn hZ U
  let S := restrictionComplex hZ U K
  have hS : S.ShortExact := restrictionComplexShortExact hZ U K hK
  let e := IsLimit.conePointUniqueUpToIso hS.fIsKernel (kernelIsKernel S.g)
  have he : e.hom ≫ kernel.ι S.g = S.f :=
    IsLimit.conePointUniqueUpToIso_hom_comp hS.fIsKernel (kernelIsKernel S.g) WalkingParallelPair.zero
  haveI hU : IsIso ((sectionsOn U).rightDerivedFunctorPlusUnit.app K) :=
    isIsoDerivedSectionsOfFlasque U K hK
  haveI hV : IsIso ((sectionsOn V).rightDerivedFunctorPlusUnit.app K) :=
    isIsoDerivedSectionsOfFlasque V K hK
  refine ⟨⟨e, he⟩, hS.epi_g, ?_, hU, hV⟩
  obtain ⟨n, hn⟩ := K.property
  letI : K.obj.IsStrictlyGE n := hn
  obtain ⟨I, _, f, hf⟩ := K.exists_quasiIso_injective n
  let J := injectiveComplex I
  haveI : IsIso (DerivedCategory.Plus.Q.map f) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _) _ hf
  have hJ (i : ℤ) : TopCat.Sheaf.IsFlasque (J.obj.X i) := by
    haveI : Injective (J.obj.X i) := (I.obj.X i).property
    exact injectiveFlasque (J.obj.X i)
  let S' := restrictionComplex hZ U J
  have hS' : S'.ShortExact := restrictionComplexShortExact hZ U J hJ
  let φ := DerivedCategory.triangleOfSES.map hS hS' (restrictionComplexMap hZ U f)
  let L := DerivedCategory.Plus.ι (C := Coeff.{u})
  have hQ₂ : IsIso φ.hom₂ := by
    change IsIso (L.map (DerivedCategory.Plus.Q.map ((sectionsOn U).mapCochainComplexPlus.map f)))
    haveI := isIsoMapResolution (sectionsOn U) f
    infer_instance
  have hQ₃ : IsIso φ.hom₃ := by
    change IsIso (L.map (DerivedCategory.Plus.Q.map ((sectionsOn V).mapCochainComplexPlus.map f)))
    haveI := isIsoMapResolution (sectionsOn V) f
    infer_instance
  have hQ₁ : IsIso φ.hom₁ := isIso₁_of_isIso₂₃ φ
    (DerivedCategory.triangleOfSES_distinguished hS)
    (DerivedCategory.triangleOfSES_distinguished hS') hQ₂ hQ₃
  change IsIso (L.map (DerivedCategory.Plus.Q.map (T.mapCochainComplexPlus.map f))) at hQ₁
  haveI : IsIso (DerivedCategory.Plus.Q.map (T.mapCochainComplexPlus.map f)) :=
    isIso_of_reflects_iso _ L
  have h := T.rightDerivedFunctorPlusUnit.naturality f
  dsimp only [Functor.comp_map] at h
  haveI : IsIso (T.rightDerivedFunctorPlusUnit.app K ≫
      T.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (T.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f))

end RepTheorySurvey.Geometric.DerivedLocalSheaves
