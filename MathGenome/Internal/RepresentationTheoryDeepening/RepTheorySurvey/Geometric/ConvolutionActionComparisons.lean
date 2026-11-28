import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionActionComparisons
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

namespace RepTheorySurvey.Geometric.ConvolutionActionComparisons

open Analytic LocalSheaf ConvolutionUnitConeSpecs ConvolutionActionComparisonsSpecs
open IntersectionComplex (shiftedConstant directImageComparison adjointSquareMap
  pullbackSquare boundedBelowPullbackComposition)
open AnalyticAction (Parameters projection)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] derivedInverseImage

open private cochainAdjunction exactPlusFactors
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves

theorem derivedAdjunction_normalized {Y X : TopCat.{0}} (m : Y ⟶ X) :
    IsDerivedDirectAdjunction m (DerivedLocalSheaves.derivedInverseDirectAdjunctionData m) := by
  intro K
  let L := inverseImage m
  let R := directImage m
  let α := exactPlusFactors L
  let β := R.rightDerivedFunctorPlusUnit
  let W := CochainComplex.Plus.quasiIso (Sheaves X)
  have : ((exactDerivedPlus L) ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α.hom R.rightDerivedFunctorPlus) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α R.rightDerivedFunctorPlus)
  exact (cochainAdjunction (inverseDirectAdjunction m)).derivedη_fac_app W α.hom β K

private theorem squareMap_eq_mate {C D E F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (α : G ⋙ L₂ ≅ L₁ ⋙ H) (a : L₂ ⊣ R₂) (b : L₁ ⊣ R₁) (d : D) :
    adjointSquareMap α a b d = (mateEquiv b a α.hom).app d := by
  apply (a.homEquiv _ _).symm.injective
  rw [adjointSquareMap, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact (mateEquiv_counit b a α.hom d).symm

private theorem squareMap_unit {C D E F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (α : G ⋙ L₂ ≅ L₁ ⋙ H) (a : L₂ ⊣ R₂) (b : L₁ ⊣ R₁) (c : C) :
    G.map (b.unit.app c) ≫ adjointSquareMap α a b (L₁.obj c) =
      a.unit.app (G.obj c) ≫ R₂.map (α.hom.app c) := by
  rw [squareMap_eq_mate]
  exact unit_mateEquiv b a α.hom c

open private directImageComparisonIsIso directImageComparisonNaturality
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private def twistIso {H : AnalyticGroup.{0}} {Z : TopCat.{0}} (A : AnalyticAction H Z) :
    Parameters H Z ≅ Parameters H Z where
  hom := twistMap A
  inv := TopCat.ofHom ⟨(actionTwist A).symm, (actionTwist A).symm.continuous⟩
  hom_inv_id := TopCat.ext (actionTwist A).left_inv
  inv_hom_id := TopCat.ext (actionTwist A).right_inv

theorem twistMate_isIso {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {B : AnalyticAction H ordered} (h : Commutes A B)
    (a : DerivedAdjunction (productMap H.space)) (F : BoundedBelow (Parameters H ordered)) :
    IsIso (directImageComparison (twistSquare h) a a F) :=
  directImageComparisonIsIso (twistIso A) (twistIso B) (twistSquare h) a a F

/-- Associativity of inverse image follows from strict composition of the direct images. -/
private theorem inverseImageComposition_assoc
    {V W Y X : TopCat.{0}} (k : V ⟶ W) (f : W ⟶ Y) (g : Y ⟶ X) (F : Sheaves X) :
    (inverseImageComposition k (f ≫ g)).hom.app F ≫
      (inverseImage k).map ((inverseImageComposition f g).hom.app F) =
    (inverseImageComposition (k ≫ f) g).hom.app F ≫
      (inverseImageComposition k f).hom.app ((inverseImage g).obj F) := by
  let A := inverseDirectAdjunction g
  let B := inverseDirectAdjunction f
  let C := inverseDirectAdjunction k
  let D := inverseDirectAdjunction (f ≫ g)
  let E := inverseDirectAdjunction (k ≫ f)
  let S := inverseDirectAdjunction (k ≫ f ≫ g)
  have h := Adjunction.leftAdjointCompIso_assoc A B C D E S
    (Iso.refl (directImage (f ≫ g))) (Iso.refl (directImage (k ≫ f)))
    (Iso.refl (directImage (k ≫ f ≫ g))) (Iso.refl (directImage (k ≫ f ≫ g))) (by
      apply Iso.ext
      apply NatTrans.ext
      funext x
      simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        Iso.refl_hom, NatTrans.id_app, Iso.symm_hom, Functor.associator_inv_app]
      erw [(directImage g).map_id, Category.comp_id])
  exact (congrArg (fun i => i.inv.app F) h).symm

open private derivedComposition_hom
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent

private abbrev factors {W X : TopCat.{0}} (f : W ⟶ X) (K : CochainComplex (Sheaves X) ℤ) :=
  (inverseImage f).mapDerivedCategoryFactors.hom.app K

private abbrev mapComplex {W X : TopCat.{0}} (f : W ⟶ X) :=
  (inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)

private abbrev complexComparison {W Y X : TopCat.{0}} (f : W ⟶ Y) (g : Y ⟶ X)
    (K : CochainComplex (Sheaves X) ℤ) :
    (mapComplex (f ≫ g)).obj K ⟶ (mapComplex f).obj ((mapComplex g).obj K) :=
  ((inverseImageComposition f g).hom.mapHomologicalComplex (.up ℤ)).app K

@[reassoc]
private theorem derivedComposition_factors {W Y X : TopCat.{0}} (f : W ⟶ Y) (g : Y ⟶ X)
    (K : CochainComplex (Sheaves X) ℤ) :
    (derivedInverseImageComposition f g).hom.app (DerivedCategory.Q.obj K) ≫
        (derivedInverseImage f).map (factors g K) ≫ factors f ((mapComplex g).obj K) =
      factors (f ≫ g) K ≫ DerivedCategory.Q.map (complexComparison f g K) := by
  let F := inverseImage g
  let G := inverseImage f
  let e := Functor.mapDerivedCategoryCompIso F G
  have h : e.hom.app (DerivedCategory.Q.obj K) ≫ (F ⋙ G).mapDerivedCategoryFactors.hom.app K =
        (derivedInverseImage f).map (factors g K) ≫ factors f ((mapComplex g).obj K) := by
    rw [Functor.mapDerivedCategoryCompIso_hom_app_Q_obj]
    have hid : ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K) =
        𝟙 _ := by
      ext n
      rfl
    rw [hid]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    let u := G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K)
    let v := G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)
    have hQ := (DerivedCategory.Q (C := Sheaves W)).map_id
      ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj K))
    exact (congrArg (fun t => u ≫ v ≫ t ≫ 𝟙 _) hQ).trans
      ((congrArg (fun t => u ≫ v ≫ t) (Category.id_comp (𝟙 _))).trans
        (congrArg (u ≫ ·) (Category.comp_id v)))
  rw [← h, derivedComposition_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    NatTrans.mapDerivedCategory_app_Q_obj]
  simp only [Category.assoc]
  change factors (f ≫ g) K ≫ DerivedCategory.Q.map (complexComparison f g K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.inv.app K ≫ (F ⋙ G).mapDerivedCategoryFactors.hom.app K = _
  rw [Iso.inv_hom_id_app]
  exact congrArg (fun t => factors (f ≫ g) K ≫ t)
    (Category.comp_id (DerivedCategory.Q.map (complexComparison f g K)))

/-- The cochain comparisons preserve associativity after localization. -/
private theorem derivedComposition_assoc
    {V W Y X : TopCat.{0}} (k : V ⟶ W) (f : W ⟶ Y) (g : Y ⟶ X) (F : Derived X) :
    (derivedInverseImageComposition k (f ≫ g)).hom.app F ≫
      (derivedInverseImage k).map ((derivedInverseImageComposition f g).hom.app F) =
    (derivedInverseImageComposition (k ≫ f) g).hom.app F ≫
      (derivedInverseImageComposition k f).hom.app ((derivedInverseImage g).obj F) := by
  let α := (derivedInverseImageComposition k (f ≫ g)).hom ≫
    Functor.whiskerRight (derivedInverseImageComposition f g).hom (derivedInverseImage k)
  let β := (derivedInverseImageComposition (k ≫ f) g).hom ≫
    Functor.whiskerLeft (derivedInverseImage g) (derivedInverseImageComposition k f).hom
  suffices α = β by exact NatTrans.congr_app this F
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  change (derivedInverseImageComposition k (f ≫ g)).hom.app (DerivedCategory.Q.obj K) ≫
      (derivedInverseImage k).map
        ((derivedInverseImageComposition f g).hom.app (DerivedCategory.Q.obj K)) =
    (derivedInverseImageComposition (k ≫ f) g).hom.app (DerivedCategory.Q.obj K) ≫
      (derivedInverseImageComposition k f).hom.app ((derivedInverseImage g).obj
        (DerivedCategory.Q.obj K))
  apply (cancel_mono ((derivedInverseImage k).map ((derivedInverseImage f).map (factors g K)))).mp
  apply (cancel_mono ((derivedInverseImage k).map (factors f ((mapComplex g).obj K)))).mp
  apply (cancel_mono (factors k ((mapComplex f).obj ((mapComplex g).obj K)))).mp
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  erw [derivedComposition_factors f g K]
  have hn := (inverseImage k).mapDerivedCategoryFactors.hom.naturality (complexComparison f g K)
  change (derivedInverseImage k).map (DerivedCategory.Q.map (complexComparison f g K)) ≫
      factors k ((mapComplex f).obj ((mapComplex g).obj K)) =
    factors k ((mapComplex (f ≫ g)).obj K) ≫
      DerivedCategory.Q.map ((mapComplex k).map (complexComparison f g K)) at hn
  rw [Functor.map_comp, Category.assoc, hn, derivedComposition_factors_assoc]
  have hc := (derivedInverseImageComposition k f).hom.naturality (factors g K)
  change (derivedInverseImage (k ≫ f)).map (factors g K) ≫
      (derivedInverseImageComposition k f).hom.app (DerivedCategory.Q.obj ((mapComplex g).obj K)) =
    (derivedInverseImageComposition k f).hom.app _ ≫
      (derivedInverseImage k).map ((derivedInverseImage f).map (factors g K)) at hc
  rw [← reassoc_of% hc, derivedComposition_factors, derivedComposition_factors_assoc]
  simp only [← Functor.map_comp]
  congr 2
  ext n
  exact inverseImageComposition_assoc k f g (K.X n)

private abbrev pull {Y X : TopCat.{0}} (f : Y ⟶ X) := derivedInverseImage f

private abbrev compPull {W Y X : TopCat.{0}} (f : W ⟶ Y) (g : Y ⟶ X) :=
  derivedInverseImageComposition f g

private abbrev pullCast {Y X : TopCat.{0}} {f g : Y ⟶ X} (e : f = g) (F : Derived X) :
    (pull f).obj F ⟶ (pull g).obj F :=
  eqToHom (congrArg (fun t => (pull t).obj F) e)

@[reassoc]
private theorem compPull_congr_left {W Y X : TopCat.{0}} {f f' : W ⟶ Y}
    (e : f = f') (g : Y ⟶ X) (F : Derived X) :
    (compPull f g).hom.app F ≫ pullCast e ((pull g).obj F) =
      pullCast (congrArg (· ≫ g) e) F ≫ (compPull f' g).hom.app F := by
  subst f'
  simp

@[reassoc]
private theorem compPull_congr_right {W Y X : TopCat.{0}} (f : W ⟶ Y) {g g' : Y ⟶ X}
    (e : g = g') (F : Derived X) :
    (compPull f g).hom.app F ≫ (pull f).map (pullCast e F) =
      pullCast (congrArg (f ≫ ·) e) F ≫ (compPull f g').hom.app F := by
  subst g'
  simp

private theorem pasteSquares {Y₀ X₀ Y₁ X₁ Y₂ X₂ : TopCat.{0}}
    {j₀ : Y₀ ⟶ X₀} {j₁ : Y₁ ⟶ X₁} {j₂ : Y₂ ⟶ X₂}
    {e₁ : X₁ ⟶ X₀} {e₂ : X₂ ⟶ X₁} {v₁ : Y₁ ⟶ Y₀} {v₂ : Y₂ ⟶ Y₁}
    (h₁ : j₁ ≫ e₁ = v₁ ≫ j₀) (h₂ : j₂ ≫ e₂ = v₂ ≫ j₁) :
    j₂ ≫ (e₂ ≫ e₁) = (v₂ ≫ v₁) ≫ j₀ :=
  (congrArg (· ≫ e₁) h₂).trans (congrArg (v₂ ≫ ·) h₁)

private theorem fullSubcategory_eqToHom {C : Type*} [Category C] {P : ObjectProperty C}
    {F G : P.FullSubcategory} (h : F = G) :
    (eqToHom h).hom = eqToHom (congrArg (fun X : P.FullSubcategory => X.obj) h) := by
  subst G
  rfl

private theorem square_hom {Y X Y' X' : TopCat.{0}}
    {j : Y ⟶ X} {k : Y' ⟶ X'} {e : X ⟶ X'} {v : Y ⟶ Y'}
    (h : j ≫ e = v ≫ k) :
    (pullbackSquare (j := j) (k := k) (e := e) (v := v) h).hom =
      (boundedBelowPullbackComposition j e).inv ≫
        (eqToIso (congrArg (fun f => boundedBelowInverseImage f) h)).hom ≫
        (boundedBelowPullbackComposition v k).hom := rfl

private theorem square_comp_app {Y X Y' X' : TopCat.{0}}
    {j : Y ⟶ X} {k : Y' ⟶ X'} {e : X ⟶ X'} {v : Y ⟶ Y'}
    (h : j ≫ e = v ≫ k) (F : BoundedBelow X') :
    ((boundedBelowPullbackComposition j e).inv ≫
        (eqToIso (congrArg (fun f => boundedBelowInverseImage f) h)).hom ≫
        (boundedBelowPullbackComposition v k).hom).app F =
      (boundedBelowPullbackComposition j e).inv.app F ≫
        (eqToIso (congrArg (fun f => boundedBelowInverseImage f) h)).hom.app F ≫
        (boundedBelowPullbackComposition v k).hom.app F := rfl

private theorem square_cast_app {Y X : TopCat.{0}}
    {f g : Y ⟶ X} (h : f = g) (F : BoundedBelow X) :
    (eqToIso (congrArg (fun f => boundedBelowInverseImage f) h)).hom.app F =
      eqToHom (congrArg (fun t => (boundedBelowInverseImage t).obj F) h) := by
  subst g
  simp

private theorem square_app_partial {Y X Y' X' : TopCat.{0}}
    {j : Y ⟶ X} {k : Y' ⟶ X'} {e : X ⟶ X'} {v : Y ⟶ Y'}
    (h : j ≫ e = v ≫ k) (F : BoundedBelow X') :
    (pullbackSquare (j := j) (k := k) (e := e) (v := v) h).hom.app F =
      (boundedBelowPullbackComposition j e).inv.app F ≫
        (eqToIso (congrArg (fun f => boundedBelowInverseImage f) h)).hom.app F ≫
        (boundedBelowPullbackComposition v k).hom.app F :=
  (NatTrans.congr_app (square_hom h) F).trans (square_comp_app h F)

private theorem square_app_hom {Y X Y' X' : TopCat.{0}}
    {j : Y ⟶ X} {k : Y' ⟶ X'} {e : X ⟶ X'} {v : Y ⟶ Y'}
    (h : j ≫ e = v ≫ k) (F : BoundedBelow X') :
    ((pullbackSquare h).hom.app F).hom =
      (compPull j e).inv.app F.obj ≫ pullCast h F.obj ≫ (compPull v k).hom.app F.obj := by
  have hc := congrArg InducedCategory.Hom.hom (square_cast_app h F)
  have ht := fullSubcategory_eqToHom (congrArg (fun t => (boundedBelowInverseImage t).obj F) h)
  rw [square_app_partial h]
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  exact congrArg (fun t => (compPull j e).inv.app F.obj ≫ t ≫ (compPull v k).hom.app F.obj)
    (hc.trans ht)

private theorem square_paste {Y₀ X₀ Y₁ X₁ Y₂ X₂ : TopCat.{0}}
    {j₀ : Y₀ ⟶ X₀} {j₁ : Y₁ ⟶ X₁} {j₂ : Y₂ ⟶ X₂}
    {e₁ : X₁ ⟶ X₀} {e₂ : X₂ ⟶ X₁} {v₁ : Y₁ ⟶ Y₀} {v₂ : Y₂ ⟶ Y₁}
    (h₁ : j₁ ≫ e₁ = v₁ ≫ j₀) (h₂ : j₂ ≫ e₂ = v₂ ≫ j₁) (F : BoundedBelow X₀) :
    (boundedBelowInverseImage j₂).map ((boundedBelowPullbackComposition e₂ e₁).hom.app F) ≫
      (pullbackSquare h₂).hom.app ((boundedBelowInverseImage e₁).obj F) ≫
      (boundedBelowInverseImage v₂).map ((pullbackSquare h₁).hom.app F) =
    (pullbackSquare (pasteSquares h₁ h₂)).hom.app F ≫
      (boundedBelowPullbackComposition v₂ v₁).hom.app ((boundedBelowInverseImage j₀).obj F) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [square_app_hom h₂, square_app_hom (pasteSquares h₁ h₂)]
  have hv : ((boundedBelowInverseImage v₂).map ((pullbackSquare h₁).hom.app F)).hom =
      (pull v₂).map (((pullbackSquare h₁).hom.app F).hom) := rfl
  rw [hv, square_app_hom h₁]
  let K := F.obj
  change (pull j₂).map ((compPull e₂ e₁).hom.app K) ≫
      ((compPull j₂ e₂).inv.app ((pull e₁).obj K) ≫ pullCast h₂ ((pull e₁).obj K) ≫
        (compPull v₂ j₁).hom.app ((pull e₁).obj K)) ≫
      (pull v₂).map ((compPull j₁ e₁).inv.app K ≫ pullCast h₁ K ≫ (compPull v₁ j₀).hom.app K) =
    ((compPull j₂ (e₂ ≫ e₁)).inv.app K ≫ pullCast (pasteSquares h₁ h₂) K ≫
      (compPull (v₂ ≫ v₁) j₀).hom.app K) ≫
      (compPull v₂ v₁).hom.app ((pull j₀).obj K)
  apply (cancel_epi ((compPull j₂ (e₂ ≫ e₁)).hom.app K)).mp
  simp only [Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc (f := (compPull j₂ (e₂ ≫ e₁)).hom.app K),
    derivedComposition_assoc j₂ e₂ e₁ K, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [compPull_congr_left_assoc h₂]
  have he := derivedComposition_assoc v₂ j₁ e₁ K
  erw [← reassoc_of% he]
  rw [← Functor.map_comp_assoc]
  rw [(compPull j₁ e₁).hom_inv_id_app, (pull v₂).map_id, Category.id_comp]
  rw [compPull_congr_right_assoc v₂ h₁]
  rw [derivedComposition_assoc v₂ v₁ j₀ K]
  simp only [pullCast, eqToHom_trans_assoc]

private theorem squareMap_transpose {C D E F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (α : G ⋙ L₂ ≅ L₁ ⋙ H) (a : L₂ ⊣ R₂) (b : L₁ ⊣ R₁) (d : D) :
    L₂.map (adjointSquareMap α a b d) ≫ a.counit.app (H.obj d) =
      α.hom.app (R₁.obj d) ≫ H.map (b.counit.app d) := by
  rw [squareMap_eq_mate]
  exact mateEquiv_counit b a α.hom d

private theorem mate_transpose {Y X Y' X' : TopCat.{0}}
    {j : Y ⟶ X} {k : Y' ⟶ X'} {e : X ⟶ X'} {v : Y ⟶ Y'}
    (h : j ≫ e = v ≫ k) (a : DerivedAdjunction j) (b : DerivedAdjunction k)
    (F : BoundedBelow Y') :
    (boundedBelowInverseImage j).map (directImageComparison h a b F) ≫
        a.counit.app ((boundedBelowInverseImage v).obj F) =
      (pullbackSquare h).hom.app ((derivedDirectImage k).obj F) ≫
        (boundedBelowInverseImage v).map (b.counit.app F) :=
  squareMap_transpose (pullbackSquare h) a b F

private theorem mate_paste {Y₀ X₀ Y₁ X₁ Y₂ X₂ : TopCat.{0}}
    {j₀ : Y₀ ⟶ X₀} {j₁ : Y₁ ⟶ X₁} {j₂ : Y₂ ⟶ X₂}
    {e₁ : X₁ ⟶ X₀} {e₂ : X₂ ⟶ X₁} {v₁ : Y₁ ⟶ Y₀} {v₂ : Y₂ ⟶ Y₁}
    (h₁ : j₁ ≫ e₁ = v₁ ≫ j₀) (h₂ : j₂ ≫ e₂ = v₂ ≫ j₁)
    (a₀ : DerivedAdjunction j₀) (a₁ : DerivedAdjunction j₁) (a₂ : DerivedAdjunction j₂)
    (F : BoundedBelow Y₀) :
    (boundedBelowPullbackComposition e₂ e₁).hom.app ((derivedDirectImage j₀).obj F) ≫
      (boundedBelowInverseImage e₂).map (directImageComparison h₁ a₁ a₀ F) ≫
      directImageComparison h₂ a₂ a₁ ((boundedBelowInverseImage v₁).obj F) =
    directImageComparison (pasteSquares h₁ h₂) a₂ a₀ F ≫
      (derivedDirectImage j₂).map ((boundedBelowPullbackComposition v₂ v₁).hom.app F) := by
  apply (a₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  simp only [Adjunction.homEquiv_counit, mate_transpose, Category.assoc]
  have hn := (pullbackSquare h₂).hom.naturality (directImageComparison h₁ a₁ a₀ F)
  change (boundedBelowInverseImage j₂).map
        ((boundedBelowInverseImage e₂).map (directImageComparison h₁ a₁ a₀ F)) ≫
      (pullbackSquare h₂).hom.app _ =
    (pullbackSquare h₂).hom.app _ ≫
      (boundedBelowInverseImage v₂).map
        ((boundedBelowInverseImage j₁).map (directImageComparison h₁ a₁ a₀ F)) at hn
  rw [reassoc_of% hn, ← Functor.map_comp, mate_transpose, Functor.map_comp]
  rw [← Category.assoc (f := (pullbackSquare h₂).hom.app _),
    ← Category.assoc (f := (boundedBelowInverseImage j₂).map _), square_paste,
    Category.assoc]
  exact congrArg (fun t => (pullbackSquare (pasteSquares h₁ h₂)).hom.app
    ((derivedDirectImage j₀).obj F) ≫ t)
    ((boundedBelowPullbackComposition v₂ v₁).hom.naturality (a₀.counit.app F)).symm

private theorem mate_congr {Y X Y' X' : TopCat.{0}} {j : Y ⟶ X} {k : Y' ⟶ X'}
    {e e' : X ⟶ X'} {v v' : Y ⟶ Y'}
    (he : e = e') (hv : v = v') (h : j ≫ e = v ≫ k) (h' : j ≫ e' = v' ≫ k)
    (a : DerivedAdjunction j) (b : DerivedAdjunction k) (F : BoundedBelow Y') :
    directImageComparison h a b F =
      eqToHom (congrArg (fun t => (boundedBelowInverseImage t).obj
        ((derivedDirectImage k).obj F)) he) ≫ directImageComparison h' a b F ≫
      (derivedDirectImage j).map (eqToHom (congrArg (fun t =>
        (boundedBelowInverseImage t).obj F) hv.symm)) := by
  subst e' v'
  simp only [eqToHom_refl, Category.id_comp]
  erw [(derivedDirectImage j).map_id, Category.comp_id]

theorem actionMate_paste {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {B : AnalyticAction H ordered} (h : Commutes A B)
    (a : DerivedAdjunction (productMap H.space)) (b : DerivedAdjunction convolutionMap) :
    MatePasting h a b := by
  unfold MatePasting
  dsimp only
  erw [mate_paste (projectionSquare H.space) (twistSquare h) b a a orderedFactor,
    mate_congr (twist_projection A) (twist_projection B) _ (actionSquare h)]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private abbrev shiftPull {Y X : TopCat.{0}} (e : Y ⟶ X) :
    (boundedBelowInverseImage e).obj (shiftedConstant X 2) ≅ shiftedConstant Y 2 :=
  ObjectProperty.isoMk _ (shiftedConstantPullback e 2)

private def coefficientMate {Y X Y' X' : TopCat.{0}}
    {j : Y ⟶ X} {k : Y' ⟶ X'} {e : X ⟶ X'} {v : Y ⟶ Y'}
    (h : j ≫ e = v ≫ k) (a : DerivedAdjunction j) (b : DerivedAdjunction k) :
    (boundedBelowInverseImage e).obj ((derivedDirectImage k).obj (shiftedConstant Y' 2)) ⟶
      (derivedDirectImage j).obj (shiftedConstant Y 2) :=
  directImageComparison h a b (shiftedConstant Y' 2) ≫
    (derivedDirectImage j).map (shiftPull v).hom

@[reassoc]
private theorem shiftPull_comp {Y W X : TopCat.{0}} (f : Y ⟶ W) (g : W ⟶ X) :
    (boundedBelowPullbackComposition f g).hom.app (shiftedConstant X 2) ≫
      (boundedBelowInverseImage f).map (shiftPull g).hom ≫ (shiftPull f).hom =
      (shiftPull (f ≫ g)).hom := by
  apply ObjectProperty.hom_ext
  exact ConvolutionConstantDescent.shiftedPullbackComposition f g 2

/-- Pasting of direct-image mates with the coefficient comparisons on the source. -/
private theorem coefficientMate_paste {Y₀ X₀ Y₁ X₁ Y₂ X₂ : TopCat.{0}}
    {j₀ : Y₀ ⟶ X₀} {j₁ : Y₁ ⟶ X₁} {j₂ : Y₂ ⟶ X₂}
    {e₁ : X₁ ⟶ X₀} {e₂ : X₂ ⟶ X₁} {v₁ : Y₁ ⟶ Y₀} {v₂ : Y₂ ⟶ Y₁}
    (h₁ : j₁ ≫ e₁ = v₁ ≫ j₀) (h₂ : j₂ ≫ e₂ = v₂ ≫ j₁)
    (a₀ : DerivedAdjunction j₀) (a₁ : DerivedAdjunction j₁) (a₂ : DerivedAdjunction j₂) :
    (boundedBelowPullbackComposition e₂ e₁).hom.app
        ((derivedDirectImage j₀).obj (shiftedConstant Y₀ 2)) ≫
      (boundedBelowInverseImage e₂).map (coefficientMate h₁ a₁ a₀) ≫
      coefficientMate h₂ a₂ a₁ = coefficientMate (pasteSquares h₁ h₂) a₂ a₀ := by
  simp only [coefficientMate, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (directImageComparisonNaturality h₂ a₂ a₁ (shiftPull v₁).hom)]
  rw [← (derivedDirectImage j₂).map_comp]
  rw [← Category.assoc (f := (boundedBelowInverseImage e₂).map _),
    ← Category.assoc (f := (boundedBelowPullbackComposition e₂ e₁).hom.app _),
    mate_paste h₁ h₂ a₀ a₁ a₂]
  simp only [Category.assoc, ← Functor.map_comp, shiftPull_comp]

private theorem pullbackMorphism_coefficientMate {Y₀ X₀ Y₁ X₁ Y₂ X₂ : TopCat.{0}}
    {j₀ : Y₀ ⟶ X₀} {j₁ : Y₁ ⟶ X₁} {j₂ : Y₂ ⟶ X₂}
    {s t : X₁ ⟶ X₀} {s' t' : Y₁ ⟶ Y₀} {f : X₂ ⟶ X₁} {g : Y₂ ⟶ Y₁}
    (hs : j₁ ≫ s = s' ≫ j₀) (ht : j₁ ≫ t = t' ≫ j₀) (hf : j₂ ≫ f = g ≫ j₁)
    (a₀ : DerivedAdjunction j₀) (a₁ : DerivedAdjunction j₁) (a₂ : DerivedAdjunction j₂)
    (r : (boundedBelowInverseImage s).obj ((derivedDirectImage j₀).obj (shiftedConstant Y₀ 2)) ⟶
      (boundedBelowInverseImage t).obj ((derivedDirectImage j₀).obj (shiftedConstant Y₀ 2)))
    (hr : r ≫ coefficientMate ht a₁ a₀ = coefficientMate hs a₁ a₀) :
    pullbackMorphism f rfl rfl r.hom ≫ (coefficientMate (pasteSquares ht hf) a₂ a₀).hom =
      (coefficientMate (pasteSquares hs hf) a₂ a₀).hom := by
  let F := (derivedDirectImage j₀).obj (shiftedConstant Y₀ 2)
  let R := boundedBelowInverseImage f
  have e := coefficientMate_paste ht hf a₀ a₁ a₂
  have e' := coefficientMate_paste hs hf a₀ a₁ a₂
  have hadj : (boundedBelowPullbackComposition f t).inv.app F ≫
      coefficientMate (pasteSquares ht hf) a₂ a₀ =
      R.map (coefficientMate ht a₁ a₀) ≫ coefficientMate hf a₂ a₁ := by
    rw [← e, Iso.inv_hom_id_app_assoc]
  have hc := congrArg InducedCategory.Hom.hom hadj
  have hc' := congrArg InducedCategory.Hom.hom e'
  have hr' := congrArg InducedCategory.Hom.hom hr
  change (compPull f t).inv.app F.obj ≫ (coefficientMate (pasteSquares ht hf) a₂ a₀).hom =
    (pull f).map (coefficientMate ht a₁ a₀).hom ≫ (coefficientMate hf a₂ a₁).hom at hc
  change (compPull f s).hom.app F.obj ≫
      (pull f).map (coefficientMate hs a₁ a₀).hom ≫ (coefficientMate hf a₂ a₁).hom =
    (coefficientMate (pasteSquares hs hf) a₂ a₀).hom at hc'
  change r.hom ≫ (coefficientMate ht a₁ a₀).hom = (coefficientMate hs a₁ a₀).hom at hr'
  simp only [pullbackMorphism, eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc]
  change (compPull f s).hom.app F.obj ≫ (pull f).map r.hom ≫
      (compPull f t).inv.app F.obj ≫ (coefficientMate (pasteSquares ht hf) a₂ a₀).hom =
        (coefficientMate (pasteSquares hs hf) a₂ a₀).hom
  rw [hc, ← Functor.map_comp_assoc, hr', hc']

private theorem pullbackMorphism_comp {W Y X : TopCat.{0}} (k : W ⟶ Y)
    {f g i : Y ⟶ X} {f' g' i' : W ⟶ X} (hf : k ≫ f = f') (hg : k ≫ g = g')
    (hi : k ≫ i = i') {F : Derived X}
    (a : (pull f).obj F ⟶ (pull g).obj F) (b : (pull g).obj F ⟶ (pull i).obj F) :
    pullbackMorphism k hf hi (a ≫ b) =
      pullbackMorphism k hf hg a ≫ pullbackMorphism k hg hi b := by
  subst f' g' i'
  simp [pullbackMorphism]

private theorem pullbackMorphism_paste {V W Y X : TopCat.{0}}
    (k : V ⟶ W) (l : W ⟶ Y) {f g : Y ⟶ X} {f' g' : W ⟶ X} {f'' g'' : V ⟶ X}
    (hf : l ≫ f = f') (hg : l ≫ g = g') (hf' : k ≫ f' = f'') (hg' : k ≫ g' = g'')
    {F : Derived X} (a : (pull f).obj F ⟶ (pull g).obj F) :
    pullbackMorphism k hf' hg' (pullbackMorphism l hf hg a) =
      pullbackMorphism (k ≫ l) (show (k ≫ l) ≫ f = f'' from (congrArg (k ≫ ·) hf).trans hf')
        (show (k ≫ l) ≫ g = g'' from (congrArg (k ≫ ·) hg).trans hg') a := by
  subst f' g' f'' g''
  simp only [pullbackMorphism, eqToHom_refl, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc (f := (compPull k (l ≫ f)).hom.app F),
    derivedComposition_assoc k l f F]
  apply (cancel_mono ((compPull k (l ≫ g)).hom.app F)).mp
  apply (cancel_mono ((pull k).map ((compPull l g).hom.app F))).mp
  have hg : (compPull (k ≫ l) g).inv.app F ≫ (compPull k (l ≫ g)).hom.app F ≫
      (pull k).map ((compPull l g).hom.app F) =
        (compPull k l).hom.app ((pull g).obj F) := by
    rw [derivedComposition_assoc k l g F, Iso.inv_hom_id_app_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, hg]
  rw [← Functor.map_comp, (compPull l g).inv_hom_id_app]
  erw [(pull k).map_id, Category.comp_id]
  have hn := (compPull k l).hom.naturality a
  exact congrArg (fun t => (compPull (k ≫ l) f).hom.app F ≫ t) hn.symm

theorem actionMate_isIso {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {B : AnalyticAction H ordered} (h : Commutes A B)
    (a : DerivedAdjunction (productMap H.space)) (b : DerivedAdjunction convolutionMap)
    [IsIso (projectionMate H.space a b)] : IsIso (actionMate h a b) := by
  let q := projection H ordered
  let p := projection H surface
  let c := (boundedBelowPullbackComposition (twistMap A) p).hom.app convolution
  let d := (boundedBelowInverseImage (twistMap A)).map (projectionMate H.space a b)
  let l := directImageComparison (twistSquare h) a a ((boundedBelowInverseImage q).obj orderedFactor)
  let s := eqToHom (congrArg (fun f => (boundedBelowInverseImage f).obj convolution)
    (twist_projection A))
  let t := (derivedDirectImage (productMap H.space)).map
    (eqToHom (congrArg (fun f => (boundedBelowInverseImage f).obj orderedFactor)
      (twist_projection B).symm) ≫
      (boundedBelowPullbackComposition (twistMap B) q).hom.app orderedFactor)
  have : IsIso l := twistMate_isIso h a _
  have : IsIso (c ≫ d ≫ l) := by dsimp only [c, d]; infer_instance
  have hp : c ≫ d ≫ l = s ≫ actionMate h a b ≫ t := actionMate_paste h a b
  have : IsIso (s ≫ actionMate h a b ≫ t) := hp ▸ inferInstance
  have : IsIso s := by dsimp only [s]; infer_instance
  have : IsIso t := by dsimp only [t]; infer_instance
  have : IsIso (actionMate h a b ≫ t) := IsIso.of_isIso_comp_left s _
  exact IsIso.of_isIso_comp_right _ t

private def normalizedUnit {Y X : TopCat.{0}} {j : Y ⟶ X} (a : DerivedAdjunction j) :
    shiftedConstant X 2 ⟶ (derivedDirectImage j).obj (shiftedConstant Y 2) :=
  a.unit.app _ ≫ (derivedDirectImage j).map (shiftPull j).hom

@[reassoc]
private theorem square_shiftPull {Y X Y' X' : TopCat.{0}}
    {j : Y ⟶ X} {k : Y' ⟶ X'} {e : X ⟶ X'} {v : Y ⟶ Y'}
    (h : j ≫ e = v ≫ k) :
    (pullbackSquare h).hom.app (shiftedConstant X' 2) ≫
      (boundedBelowInverseImage v).map (shiftPull k).hom ≫ (shiftPull v).hom =
    (boundedBelowInverseImage j).map (shiftPull e).hom ≫ (shiftPull j).hom := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, square_app_hom h, Category.assoc]
  let F := (shiftedConstant X' 2).obj
  change (compPull j e).inv.app F ≫ pullCast h F ≫
      (compPull v k).hom.app F ≫ (pull v).map (shiftedConstantPullback k 2).hom ≫
          (shiftedConstantPullback v 2).hom =
    (pull j).map (shiftedConstantPullback e 2).hom ≫ (shiftedConstantPullback j 2).hom
  apply (cancel_epi ((compPull j e).hom.app F)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [ConvolutionConstantDescent.shiftedPullbackComposition v k 2,
    ConvolutionConstantDescent.shiftedPullbackComposition j e 2]
  generalize j ≫ e = u at h ⊢
  subst u
  simp only [eqToHom_refl, Category.id_comp]

open private adjointComparisonNaturality from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private theorem adjointSquare_unit_compatible {C D E F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    {G : C ⥤ E} {H : D ⥤ F} {L : C ⥤ D} {R : D ⥤ C} {M : E ⥤ F} {S : F ⥤ E}
    (α : G ⋙ M ≅ L ⋙ H) (a : M ⊣ S) (b : L ⊣ R)
    {X : C} {Y : D} {X' : E} {Y' : F}
    (p : L.obj X ⟶ Y) (q : M.obj X' ⟶ Y')
    (r : G.obj X ⟶ X') (s : H.obj Y ⟶ Y')
    (comm : α.hom.app X ≫ H.map p ≫ s = M.map r ≫ q) :
    G.map (b.unit.app X ≫ R.map p) ≫ adjointSquareMap α a b Y ≫ S.map s =
      r ≫ a.unit.app X' ≫ S.map q := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (adjointComparisonNaturality α a b p), reassoc_of% (squareMap_unit α a b X)]
  have hu : r ≫ a.unit.app X' = a.unit.app (G.obj X) ≫ S.map (M.map r) :=
    a.unit.naturality r
  rw [reassoc_of% hu, ← S.map_comp_assoc, ← S.map_comp, ← S.map_comp]
  simp only [Category.assoc, comm]

private theorem normalizedUnit_square {Y X Y' X' : TopCat.{0}}
    {j : Y ⟶ X} {k : Y' ⟶ X'} {e : X ⟶ X'} {v : Y ⟶ Y'}
    (h : j ≫ e = v ≫ k) (a : DerivedAdjunction j) (b : DerivedAdjunction k) :
    (boundedBelowInverseImage e).map (normalizedUnit b) ≫ coefficientMate h a b =
      (shiftPull e).hom ≫ normalizedUnit a :=
  adjointSquare_unit_compatible (pullbackSquare h) a b (shiftPull k).hom
    (shiftPull j).hom (shiftPull e).hom (shiftPull v).hom (square_shiftPull h)

section SingleDegreeUnit

open HomologicalComplex

private theorem single_unit_map {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (a : L ⊣ R)
    (n : ℤ) {U : C} {V : D} (u : L.obj U ⟶ V) :
    (a.unit.mapHomologicalComplex (.up ℤ)).app ((single C (.up ℤ) n).obj U) ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        ((singleMapHomologicalComplex L (.up ℤ) n).hom.app U ≫
          (single D (.up ℤ) n).map u) =
    (single C (.up ℤ) n).map (a.unit.app U ≫ R.map u) ≫
      (singleMapHomologicalComplex R (.up ℤ) n).inv.app V := by
  ext i
  by_cases h : i = n
  · subst i
    simp only [comp_f, NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
      singleMapHomologicalComplex_hom_app_self, singleMapHomologicalComplex_inv_app_self,
      single_map_f_self, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
    have hn := a.unit.naturality (singleObjXSelf (.up ℤ) n U).hom
    change (singleObjXSelf (.up ℤ) n U).hom ≫ a.unit.app U =
      a.unit.app (((single C (.up ℤ) n).obj U).X n) ≫
        R.map (L.map (singleObjXSelf (.up ℤ) n U).hom) at hn
    rw [← reassoc_of% hn, ← R.map_comp_assoc, Iso.inv_hom_id, R.map_id, Category.id_comp]
    rfl
  · exact (isZero_single_obj_X (.up ℤ) n U i h).eq_of_src _ _

private def singlePull {Y X : TopCat.{0}} (m : Y ⟶ X) (n : ℤ) :
    (boundedBelowInverseImage m).obj (DerivedCategory.Plus.Q.obj (coefficientComplex X n)) ⟶
      DerivedCategory.Plus.Q.obj (coefficientComplex Y n) :=
  let L := inverseImage m
  let K := coefficientComplex X n
  (exactPlusFactors L).hom.app K ≫ DerivedCategory.Plus.Q.map
    (ObjectProperty.homMk ((singleMapHomologicalComplex L (.up ℤ) n).hom.app (rational X) ≫
      (single (Sheaves Y) (.up ℤ) n).map (constantPullback m).hom))

/-- The cochain description of the unit in a single degree agrees with the normalized adjunction. -/
private theorem derivedConstantUnit_eq_unit {Y X : TopCat.{0}} (m : Y ⟶ X)
    (a : DerivedAdjunction m) (ha : IsDerivedDirectAdjunction m a) (n : ℤ) :
    derivedConstantUnit m n =
      (a.unit.app (DerivedCategory.Plus.Q.obj (coefficientComplex X n)) ≫
        (derivedDirectImage m).map (singlePull m n)).hom := by
  let K := coefficientComplex X n
  let P := coefficientComplex Y n
  let L := inverseImage m
  let R := directImage m
  let d : L.mapCochainComplexPlus.obj K ⟶ P := ObjectProperty.homMk
    ((singleMapHomologicalComplex L (.up ℤ) n).hom.app (rational X) ≫
        (single (Sheaves Y) (.up ℤ) n).map (constantPullback m).hom)
  let η := (inverseDirectAdjunction m).unit.mapCochainComplexPlus
  let β := R.rightDerivedFunctorPlusUnit
  have ha' := ha K
  change a.unit.app (DerivedCategory.Plus.Q.obj K) ≫
    (derivedDirectImage m).map ((exactPlusFactors L).hom.app K) =
    DerivedCategory.Plus.Q.map (η.app K) ≫ β.app (L.mapCochainComplexPlus.obj K) at ha'
  have hb := β.naturality d
  change DerivedCategory.Plus.Q.map (R.mapCochainComplexPlus.map d) ≫ β.app P =
    β.app (L.mapCochainComplexPlus.obj K) ≫ (derivedDirectImage m).map
      (DerivedCategory.Plus.Q.map d) at hb
  have hc : η.app K ≫ R.mapCochainComplexPlus.map d = ObjectProperty.homMk
      ((single (Sheaves X) (.up ℤ) n).map ((inverseDirectAdjunction m).unit.app (rational X) ≫
        R.map (constantPullback m).hom) ≫
        (singleMapHomologicalComplex R (.up ℤ) n).inv.app (rational Y)) := by
    apply ObjectProperty.hom_ext
    exact single_unit_map (inverseDirectAdjunction m) n (constantPullback m).hom
  let f : K ⟶ R.mapCochainComplexPlus.obj P := ObjectProperty.homMk
    ((single (Sheaves X) (.up ℤ) n).map ((inverseDirectAdjunction m).unit.app (rational X) ≫
      R.map (constantPullback m).hom) ≫
      (singleMapHomologicalComplex R (.up ℤ) n).inv.app (rational Y))
  change (DerivedCategory.Plus.Q.map f ≫ β.app P).hom =
    (a.unit.app (DerivedCategory.Plus.Q.obj K) ≫ (derivedDirectImage m).map
      ((exactPlusFactors L).hom.app K ≫ DerivedCategory.Plus.Q.map d)).hom
  apply congrArg InducedCategory.Hom.hom
  let Q := DerivedCategory.Plus.Q (C := Sheaves X)
  let D := derivedDirectImage m
  calc
    Q.map f ≫ β.app P = Q.map (η.app K ≫ R.mapCochainComplexPlus.map d) ≫ β.app P :=
      congrArg (fun t => Q.map t ≫ β.app P) hc.symm
    _ = Q.map (η.app K) ≫ Q.map (R.mapCochainComplexPlus.map d) ≫ β.app P := by
      rw [Q.map_comp, Category.assoc]
    _ = Q.map (η.app K) ≫ β.app (L.mapCochainComplexPlus.obj K) ≫
        D.map (DerivedCategory.Plus.Q.map d) :=
      congrArg (Q.map (η.app K) ≫ ·) hb
    _ = (Q.map (η.app K) ≫ β.app (L.mapCochainComplexPlus.obj K)) ≫
        D.map (DerivedCategory.Plus.Q.map d) := (Category.assoc _ _ _).symm
    _ = (a.unit.app (Q.obj K) ≫ D.map ((exactPlusFactors L).hom.app K)) ≫
        D.map (DerivedCategory.Plus.Q.map d) :=
      congrArg (· ≫ D.map (DerivedCategory.Plus.Q.map d)) ha'.symm
    _ = _ := by rw [Category.assoc, ← D.map_comp]

end SingleDegreeUnit


section ShiftComparison

open HomologicalComplex

private abbrev complexShiftFromSingle (C : Type*) [Category* C] [Abelian C] (U : C) :
    (CochainComplex.singleFunctor C (-2)).obj U ≅
      (CochainComplex.singleFunctor C 0).obj U⟦(2 : ℤ)⟧ :=
  (((CochainComplex.singleFunctors C).shiftIso 2 (-2) 0 (by decide)).app U).symm

private theorem complexShiftFromSingle_f (C : Type*) [Category* C] [Abelian C] (U : C) :
    (complexShiftFromSingle C U).hom.f (-2) =
      (singleObjXSelf (.up ℤ) (-2) U).hom ≫
        (singleObjXSelf (.up ℤ) 0 U).inv := by
  simp [complexShiftFromSingle, CochainComplex.singleFunctors, singleObjXSelf, singleObjXIsoOfEq]

private theorem singleMap_shift_components {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) {A B U : C} {P Q : D}
    (u : A ≅ U) (v : B ≅ U) (w : P ≅ L.obj U) (z : Q ≅ L.obj U) :
    L.map (u.hom ≫ v.inv) ≫ 𝟙 (L.obj B) ≫ L.map v.hom ≫ w.inv =
      (L.map u.hom ≫ z.inv) ≫ z.hom ≫ w.inv := by
  simp only [Category.id_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, Iso.inv_hom_id_assoc]

private theorem singleMap_shift {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (L : C ⥤ D) [L.Additive] (U : C) :
    let F := L.mapHomologicalComplex (.up ℤ)
    F.map (complexShiftFromSingle C U).hom ≫
      (F.commShiftIso (2 : ℤ)).hom.app ((CochainComplex.singleFunctor C 0).obj U) ≫
      (shiftFunctor (CochainComplex D ℤ) (2 : ℤ)).map
        ((singleMapHomologicalComplex L (.up ℤ) 0).hom.app U) =
      (singleMapHomologicalComplex L (.up ℤ) (-2)).hom.app U ≫
        (complexShiftFromSingle D (L.obj U)).hom := by
  dsimp only
  ext i
  by_cases h : i = -2
  · subst i
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, complexShiftFromSingle_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, CochainComplex.shiftFunctor_map_f',
      singleMapHomologicalComplex_hom_app_self]
    let u := singleObjXSelf (.up ℤ) (-2) U
    let v := singleObjXSelf (.up ℤ) 0 U
    let w := singleObjXSelf (.up ℤ) 0 (L.obj U)
    let z := singleObjXSelf (.up ℤ) (-2) (L.obj U)
    have hs : ((singleMapHomologicalComplex L (.up ℤ) 0).hom.app U).f ((-2 : ℤ) + 2) =
        L.map v.hom ≫ w.inv := singleMapHomologicalComplex_hom_app_self L (.up ℤ) 0 U
    rw [hs]
    exact singleMap_shift_components L u v w z
  · exact (L.map_isZero (isZero_single_obj_X (.up ℤ) (-2) U i h)).eq_of_src _ _

private theorem shiftComparison_of_localization
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (Q : C ⥤ C') (P : D ⥤ D') (F : C ⥤ D) (G : C' ⥤ D')
    [Q.CommShift ℤ] [P.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
    (η : Q ⋙ G ⟶ F ⋙ P) [NatTrans.CommShift η ℤ]
    {X W : C} {Y Z : D} (n : ℤ) (a : X ⟶ W⟦n⟧) (b : Y ⟶ Z⟦n⟧)
    (p : F.obj W ⟶ Z) (q : F.obj X ⟶ Y)
    (h : F.map a ≫ (F.commShiftIso n).hom.app W ≫ p⟦n⟧' = q ≫ b) :
    G.map (Q.map a ≫ (Q.commShiftIso n).hom.app W) ≫
      (G.commShiftIso n).hom.app (Q.obj W) ≫ (η.app W ≫ P.map p)⟦n⟧' =
      η.app X ≫ P.map q ≫ P.map b ≫ (P.commShiftIso n).hom.app Z := by
  simp only [Functor.map_comp, Category.assoc]
  have hQ := Functor.commShiftIso_comp_hom_app Q G n W
  rw [← reassoc_of% hQ, NatTrans.shift_app_comm_assoc η, Functor.commShiftIso_comp_hom_app]
  have ha : G.map (Q.map a) ≫ η.app (W⟦n⟧) = η.app X ≫ P.map (F.map a) :=
    η.naturality a
  have hp := (P.commShiftIso n).hom.naturality p
  change P.map (p⟦n⟧') ≫ (P.commShiftIso n).hom.app Z =
    (P.commShiftIso n).hom.app (F.obj W) ≫ (P.map p)⟦n⟧' at hp
  simp only [Category.assoc]
  rw [reassoc_of% ha, ← hp, ← P.map_comp_assoc, ← P.map_comp_assoc]
  simp only [Category.assoc, h, Functor.map_comp]

private abbrev derivedShiftFromSingle (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]
    (U : C) :
    (DerivedCategory.singleFunctor C (-2)).obj U ≅
      (DerivedCategory.singleFunctor C 0).obj U⟦(2 : ℤ)⟧ :=
  (((DerivedCategory.singleFunctors C).shiftIso 2 (-2) 0 (by decide)).app U).symm

private theorem derivedShiftFromSingle_hom (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory C] (U : C) :
    (derivedShiftFromSingle C U).hom =
      DerivedCategory.Q.map (complexShiftFromSingle C U).hom ≫
        (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
          ((CochainComplex.singleFunctor C 0).obj U) := by
  change (((CochainComplex.singleFunctors C).postcomp DerivedCategory.Q).shiftIso
      2 (-2) 0 (by decide)).inv.app U = _
  simp only [SingleFunctors.postcomp_shiftIso_inv_app]
  rfl

private theorem derivedSingleMap_hom {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    (n : ℤ) (U : C) :
    (L.mapDerivedCategorySingleFunctor n).hom.app U =
      L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C n).obj U) ≫
      DerivedCategory.Q.map ((singleMapHomologicalComplex L (.up ℤ) n).hom.app U) := by
  simp only [Functor.mapDerivedCategorySingleFunctor_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_hom_app, DerivedCategory.singleFunctorIsoCompQ_inv_app,
    Category.comp_id]
  erw [L.mapDerivedCategory.map_id, Category.id_comp]

private theorem derivedSingleMap_shift {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    (U : C) :
    L.mapDerivedCategory.map (derivedShiftFromSingle C U).hom ≫
      (L.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor C 0).obj U) ≫
      ((L.mapDerivedCategorySingleFunctor 0).hom.app U)⟦(2 : ℤ)⟧' =
    (L.mapDerivedCategorySingleFunctor (-2)).hom.app U ≫
      (derivedShiftFromSingle D (L.obj U)).hom := by
  rw [derivedShiftFromSingle_hom, derivedShiftFromSingle_hom, derivedSingleMap_hom,
    derivedSingleMap_hom]
  simp only [Category.assoc]
  exact shiftComparison_of_localization DerivedCategory.Q DerivedCategory.Q
    (L.mapHomologicalComplex (.up ℤ)) L.mapDerivedCategory L.mapDerivedCategoryFactors.hom
    2 (complexShiftFromSingle C U).hom (complexShiftFromSingle D (L.obj U)).hom
    ((singleMapHomologicalComplex L (.up ℤ) 0).hom.app U)
    ((singleMapHomologicalComplex L (.up ℤ) (-2)).hom.app U) (singleMap_shift L U)

end ShiftComparison


open HomologicalComplex

private theorem singlePull_hom {Y X : TopCat.{0}} (m : Y ⟶ X) (n : ℤ) :
    (singlePull m n).hom =
      ((inverseImage m).mapDerivedCategorySingleFunctor n).hom.app (rational X) ≫
        (DerivedCategory.singleFunctor (Sheaves Y) n).map (constantPullback m).hom := by
  rw [derivedSingleMap_hom]
  let L := inverseImage m
  let K := coefficientComplex X n
  let d : L.mapCochainComplexPlus.obj K ⟶ coefficientComplex Y n :=
    ObjectProperty.homMk ((singleMapHomologicalComplex L (.up ℤ) n).hom.app (rational X) ≫
      (single (Sheaves Y) (.up ℤ) n).map (constantPullback m).hom)
  change (DerivedCategory.Plus.ι (C := Sheaves Y)).map
    ((exactPlusFactors L).hom.app K ≫ DerivedCategory.Plus.Q.map d) = _
  rw [Functor.map_comp]
  have hf : (DerivedCategory.Plus.ι (C := Sheaves Y)).map ((exactPlusFactors L).hom.app K) =
      factors m K.obj := by
    unfold exactPlusFactors
    simp only [NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage]
    rfl
  rw [hf]
  change factors m K.obj ≫ (DerivedCategory.Q (C := Sheaves Y)).map
      ((singleMapHomologicalComplex L (.up ℤ) n).hom.app (rational X) ≫
        (single (Sheaves Y) (.up ℤ) n).map (constantPullback m).hom) = _
  rw [(DerivedCategory.Q (C := Sheaves Y)).map_comp]
  exact (Category.assoc _ _ _).symm

private theorem coefficientShift_hom (X : TopCat.{0}) :
    (coefficientShiftIso X 2).hom.hom = (derivedShiftFromSingle (Sheaves X) (rational X)).hom := by
  unfold coefficientShiftIso
  change (DerivedCategory.Plus.ι (C := Sheaves X)).map _ = _
  rw [Functor.preimageIso_hom, Functor.map_preimage]
  rfl

private theorem singlePull_shift {Y X : TopCat.{0}} (m : Y ⟶ X) :
    (boundedBelowInverseImage m).map (coefficientShiftIso X 2).hom ≫ (shiftPull m).hom =
      singlePull m (-2) ≫ (coefficientShiftIso Y 2).hom := by
  apply ObjectProperty.hom_ext
  let L := inverseImage m
  let U := rational X
  let V := rational Y
  let f := (constantPullback m).hom
  have hc := singlePull_hom m (-2)
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  have hl : ((boundedBelowInverseImage m).map (coefficientShiftIso X 2).hom).hom =
      L.mapDerivedCategory.map (coefficientShiftIso X 2).hom.hom := rfl
  rw [hl, coefficientShift_hom X, coefficientShift_hom Y]
  change L.mapDerivedCategory.map (derivedShiftFromSingle (Sheaves X) U).hom ≫
      (shiftedConstantPullback m 2).hom =
    (singlePull m (-2)).hom ≫ (derivedShiftFromSingle (Sheaves Y) V).hom
  rw [hc]
  change L.mapDerivedCategory.map (derivedShiftFromSingle (Sheaves X) U).hom ≫
      (L.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Sheaves X) 0).obj U) ≫
      (((L.mapDerivedCategorySingleFunctor 0).hom.app U) ≫
        (DerivedCategory.singleFunctor (Sheaves Y) 0).map f)⟦(2 : ℤ)⟧' =
    (((L.mapDerivedCategorySingleFunctor (-2)).hom.app U) ≫
      (DerivedCategory.singleFunctor (Sheaves Y) (-2)).map f) ≫
      (derivedShiftFromSingle (Sheaves Y) V).hom
  have hn : (DerivedCategory.singleFunctor (Sheaves Y) (-2)).map f ≫
      (derivedShiftFromSingle (Sheaves Y) V).hom =
    (derivedShiftFromSingle (Sheaves Y) (L.obj U)).hom ≫
      ((DerivedCategory.singleFunctor (Sheaves Y) 0).map f)⟦(2 : ℤ)⟧' :=
    (((DerivedCategory.singleFunctors (Sheaves Y)).shiftIso 2 (-2) 0
      (by decide)).inv.naturality f)
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, ← reassoc_of% (derivedSingleMap_shift L U)]

private def shiftedUnitFor {Y X : TopCat.{0}} (m : Y ⟶ X) :
    (shiftedConstant X 2).obj ⟶ ((derivedDirectImage m).obj (shiftedConstant Y 2)).obj :=
  (coefficientShiftIso X 2).inv.hom ≫ derivedConstantUnit m (-2) ≫
    ((derivedDirectImage m).map (coefficientShiftIso Y 2).hom).hom

/-- Comparing a negative single degree with the shift of degree zero preserves the unit. -/
private theorem normalizedUnit_eq_shiftedUnit {Y X : TopCat.{0}} (m : Y ⟶ X)
    (a : DerivedAdjunction m) (ha : IsDerivedDirectAdjunction m a) :
    (normalizedUnit a).hom = shiftedUnitFor m := by
  unfold shiftedUnitFor
  rw [derivedConstantUnit_eq_unit m a ha]
  let D := derivedDirectImage m
  let c := coefficientShiftIso X 2
  let d := coefficientShiftIso Y 2
  let L := boundedBelowInverseImage m
  have hu : c.hom ≫ a.unit.app (shiftedConstant X 2) =
      a.unit.app (DerivedCategory.Plus.Q.obj (coefficientComplex X (-2))) ≫
        D.map (L.map c.hom) := a.unit.naturality c.hom
  have hm : c.hom ≫ normalizedUnit a =
      a.unit.app (DerivedCategory.Plus.Q.obj (coefficientComplex X (-2))) ≫
        D.map (singlePull m (-2)) ≫ D.map d.hom := by
    unfold normalizedUnit
    erw [reassoc_of% hu, ← D.map_comp, singlePull_shift, D.map_comp]
  have hm' := congrArg InducedCategory.Hom.hom hm
  change c.hom.hom ≫ (normalizedUnit a).hom =
    (a.unit.app (DerivedCategory.Plus.Q.obj (coefficientComplex X (-2))) ≫
      D.map (singlePull m (-2)) ≫ D.map d.hom).hom at hm'
  apply (cancel_epi c.hom.hom).mp
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc] at hm' ⊢
  have hc : c.hom.hom ≫ c.inv.hom = 𝟙 _ :=
    congrArg InducedCategory.Hom.hom c.hom_inv_id
  rw [reassoc_of% hc]
  exact hm'

open private unitCocone from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionUnitCone

theorem projectionTriangle {T : TopCat.{0}}
    (a : DerivedAdjunction (productMap T)) (b : DerivedAdjunction convolutionMap)
    [IsIso (projectionComparison T a b)]
    (comm : (derivedInverseImage (productProjection T surface)).map unit ≫
        projectionComparison T a b =
      (shiftedConstantPullback (productProjection T surface) 2).hom ≫ productUnit T) :
    let p := productProjection T surface
    letI : (derivedInverseImage p).CommShift ℤ :=
      inferInstanceAs (((inverseImage p).mapDerivedCategory).CommShift ℤ)
    ∃ (C : Derived (TopCat.of (T × surface))) (v : (productConvolution T).obj ⟶ C)
      (δ : C ⟶ (shiftedConstant (TopCat.of (T × surface)) 2).obj⟦(1 : ℤ)⟧)
      (e : (derivedInverseImage p).mapTriangle.obj unitTriangle ≅
        Triangle.mk (productUnit T) v δ),
      Triangle.mk (productUnit T) v δ ∈ distTriang (Derived (TopCat.of (T × surface))) ∧
      e.hom.hom₁ = (shiftedConstantPullback p 2).hom ∧
      e.hom.hom₂ = projectionComparison T a b := by
  dsimp only
  let p := productProjection T surface
  let F := (inverseImage p).mapDerivedCategory
  let S := F.mapTriangle.obj unitTriangle
  obtain ⟨C, v, δ, hd⟩ := distinguished_cocone_triangle (productUnit T)
  have hd' : S ∈ distTriang _ := F.map_distinguished _
    unitCocone.choose_spec.choose_spec.choose_spec
  let e := isoTriangleOfIso₁₂ S (Triangle.mk (productUnit T) v δ) hd' hd
    (shiftedConstantPullback p 2) (asIso (projectionComparison T a b)) comm
  exact ⟨C, v, δ, e, hd, rfl, rfl⟩

private theorem pullbackMorphism_congr {W Y X : TopCat.{0}} {k l : W ⟶ Y}
    (h : k = l) {f g : Y ⟶ X} {s t : W ⟶ X}
    (hk : k ≫ f = s) (hk' : k ≫ g = t) (hl : l ≫ f = s) (hl' : l ≫ g = t)
    {F : Derived X} (r : (pull f).obj F ⟶ (pull g).obj F) :
    pullbackMorphism k hk hk' r = pullbackMorphism l hl hl' r := by
  subst l
  rfl

private theorem pullbackMorphism_commute {W U V Y X : TopCat.{0}}
    (k : W ⟶ U) (l : U ⟶ Y) (k' : W ⟶ V) (l' : V ⟶ Y) (h : k ≫ l = k' ≫ l')
    {f g : Y ⟶ X} {s t : U ⟶ X} {s' t' : V ⟶ X} {s'' t'' : W ⟶ X}
    (hf : l ≫ f = s) (hg : l ≫ g = t) (hf' : l' ≫ f = s') (hg' : l' ≫ g = t')
    (hs : k ≫ s = s'') (ht : k ≫ t = t'') (hs' : k' ≫ s' = s'') (ht' : k' ≫ t' = t'')
    {F : Derived X} (r : (pull f).obj F ⟶ (pull g).obj F) :
    pullbackMorphism k hs ht (pullbackMorphism l hf hg r) =
      pullbackMorphism k' hs' ht' (pullbackMorphism l' hf' hg' r) := by
  rw [pullbackMorphism_paste, pullbackMorphism_paste]
  exact pullbackMorphism_congr h _ _ _ _ r

open AnalyticAction (TwoParameters identitySection identity_act identity_projection
  multiplyParameters secondParameter firstAfterSecond multiply_act first_projection multiply_projection)

private def pairParameterMap {K H : AnalyticGroup.{0}} (φ : K.space →* H.space)
    (hc : Continuous φ) (X : TopCat.{0}) : TwoParameters K X ⟶ TwoParameters H X :=
  TopCat.ofHom ⟨fun p => (φ p.1, (φ p.2.1, p.2.2)),
    (hc.comp continuous_fst).prodMk ((parameterMap φ hc X).hom.continuous.comp continuous_snd)⟩

private def restrictEquivariance {K H : AnalyticGroup.{0}} {X : TopCat.{0}}
    (φ : K.space →* H.space) (hc : Continuous φ) (A : AnalyticAction H X)
    {F : Derived X} (α : A.Equivariance F) : (restrictAction φ hc A).Equivariance F := by
  let p := parameterMap φ hc X
  let A' := restrictAction φ hc A
  let hp : p ≫ projection H X = projection K X := TopCat.ext (fun _ => rfl)
  let r := pullbackMorphism p (show p ≫ A.act = A'.act from rfl) hp α.iso.hom
  haveI : IsIso r := by
    unfold r pullbackMorphism
    infer_instance
  refine { iso := asIso r, identity := ?_, multiplication := ?_ }
  · change pullbackMorphism (identitySection K X) (identity_act A') identity_projection r = _
    dsimp only [r]
    rw [pullbackMorphism_paste]
    have hi : identitySection K X ≫ p = identitySection H X :=
      TopCat.ext (fun x => Prod.ext (φ.map_one) (rfl : x = x))
    exact (pullbackMorphism_congr hi _ _ (identity_act A) identity_projection α.iso.hom).trans
      α.identity
  · let q := pairParameterMap φ hc X
    let mulK := multiplyParameters K X
    let mulH := multiplyParameters H X
    let fstK := firstAfterSecond A'
    let fstH := firstAfterSecond A
    let sndK := secondParameter K X
    let sndH := secondParameter H X
    have hm : mulK ≫ p = q ≫ mulH := TopCat.ext
      (fun a => Prod.ext (φ.map_mul a.1 a.2.1) (rfl : a.2.2 = a.2.2))
    have hf : fstK ≫ p = q ≫ fstH := TopCat.ext (fun _ => rfl)
    have hs : sndK ≫ p = q ≫ sndH := TopCat.ext (fun _ => rfl)
    let hsA : q ≫ (mulH ≫ A.act) = mulK ≫ A'.act :=
      congrArg (· ≫ A.act) hm.symm
    let hsP : q ≫ (mulH ≫ projection H X) = mulK ≫ projection K X :=
      (congrArg (· ≫ projection H X) hm.symm).trans (congrArg (mulK ≫ ·) hp)
    let hsM : q ≫ (sndH ≫ A.act) = sndK ≫ A'.act := congrArg (· ≫ A.act) hs.symm
    have he := congrArg (pullbackMorphism q hsA hsP) α.multiplication
    rw [pullbackMorphism_comp q hsA hsM hsP] at he
    change pullbackMorphism mulK rfl rfl r =
      pullbackMorphism fstK (multiply_act A') (first_projection A') r ≫
        pullbackMorphism sndK rfl multiply_projection r
    dsimp only [r]
    rw [pullbackMorphism_commute mulK p q mulH hm rfl hp rfl rfl rfl rfl hsA hsP,
      pullbackMorphism_commute fstK p q fstH hf rfl hp (multiply_act A)
        (first_projection A) (multiply_act A') (first_projection A') hsA hsM,
      pullbackMorphism_commute sndK p q sndH hs rfl hp rfl multiply_projection
        rfl multiply_projection hsM hsP]
    exact he


private theorem coefficientMate_isIso {Y X Y' X' : TopCat.{0}}
    {j : Y ⟶ X} {k : Y' ⟶ X'} {e : X ⟶ X'} {v : Y ⟶ Y'}
    (h : j ≫ e = v ≫ k) (a : DerivedAdjunction j) (b : DerivedAdjunction k)
    (he : IsIso (directImageComparison h a b (shiftedConstant Y' 2))) :
    IsIso ((coefficientMate h a b).hom) := by
  change IsIso (DerivedCategory.Plus.ι.map
    (directImageComparison h a b (shiftedConstant Y' 2) ≫
      (derivedDirectImage j).map (shiftPull v).hom))
  infer_instance

private theorem pullbackMorphism_coefficientMate_of_eq {Y₀ X₀ Y₁ X₁ Y₂ X₂ : TopCat.{0}}
    {j₀ : Y₀ ⟶ X₀} {j₁ : Y₁ ⟶ X₁} {j₂ : Y₂ ⟶ X₂}
    {s t : X₁ ⟶ X₀} {s' t' : Y₁ ⟶ Y₀} {f : X₂ ⟶ X₁} {g : Y₂ ⟶ Y₁}
    (hs : j₁ ≫ s = s' ≫ j₀) (ht : j₁ ≫ t = t' ≫ j₀) (hf : j₂ ≫ f = g ≫ j₁)
    (a₀ : DerivedAdjunction j₀) (a₁ : DerivedAdjunction j₁) (a₂ : DerivedAdjunction j₂)
    {S T : X₂ ⟶ X₀} {S' T' : Y₂ ⟶ Y₀}
    (hS : f ≫ s = S) (hT : f ≫ t = T) (hS' : g ≫ s' = S') (hT' : g ≫ t' = T')
    (hSq : j₂ ≫ S = S' ≫ j₀) (hTq : j₂ ≫ T = T' ≫ j₀)
    (r : (boundedBelowInverseImage s).obj ((derivedDirectImage j₀).obj (shiftedConstant Y₀ 2)) ⟶
      (boundedBelowInverseImage t).obj ((derivedDirectImage j₀).obj (shiftedConstant Y₀ 2)))
    (hr : r ≫ coefficientMate ht a₁ a₀ = coefficientMate hs a₁ a₀) :
    pullbackMorphism f hS hT r.hom ≫ (coefficientMate hTq a₂ a₀).hom =
      (coefficientMate hSq a₂ a₀).hom := by
  subst S T S' T'
  exact pullbackMorphism_coefficientMate hs ht hf a₀ a₁ a₂ r hr

private def nestedProductMap (H : AnalyticGroup.{0}) :
    TwoParameters H ordered ⟶ TwoParameters H surface :=
  TopCat.ofHom ⟨fun p => (p.1, (p.2.1, convolutionMap p.2.2)),
    continuous_fst.prodMk
      ((productMap H.space).hom.continuous.comp continuous_snd)⟩

private def flatToNested (H : AnalyticGroup.{0}) (X : TopCat.{0}) :
    TopCat.of ((H.space × H.space) × X) ≅ TwoParameters H X where
  hom := TopCat.ofHom ⟨fun p => (p.1.1, (p.1.2, p.2)),
    (continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk
      continuous_snd)⟩
  inv := TopCat.ofHom ⟨fun p => ((p.1, p.2.1), p.2.2),
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)⟩
  hom_inv_id := TopCat.ext (fun _ => rfl)
  inv_hom_id := TopCat.ext (fun _ => rfl)

private theorem nestedProjectionSquare (H : AnalyticGroup.{0}) :
    nestedProductMap H ≫ (multiplyParameters H surface ≫ projection H surface) =
      (multiplyParameters H ordered ≫ projection H ordered) ≫ convolutionMap :=
  TopCat.ext (fun _ => rfl)

private theorem nestedProjection_isIso {H : AnalyticGroup.{0}}
    (a : DerivedAdjunction (productMap (TopCat.of (H.space × H.space))))
    (c : DerivedAdjunction (nestedProductMap H)) (b : DerivedAdjunction convolutionMap)
    (ha : IsIso (projectionMate (TopCat.of (H.space × H.space)) a b)) :
    IsIso (directImageComparison (nestedProjectionSquare H) c b orderedFactor) := by
  let T := TopCat.of (H.space × H.space)
  let e := (flatToNested H surface).symm
  let v := (flatToNested H ordered).symm
  let he : nestedProductMap H ≫ e.hom = v.hom ≫ productMap T := TopCat.ext (fun _ => rfl)
  let hm := directImageComparison he c a
    ((boundedBelowInverseImage (productProjection T ordered)).obj orderedFactor)
  have : IsIso hm := directImageComparisonIsIso e v he c a _
  have hp := mate_paste (projectionSquare T) he b a c orderedFactor
  let m := directImageComparison (nestedProjectionSquare H) c b orderedFactor
  let q := (derivedDirectImage (nestedProductMap H)).map
    ((boundedBelowPullbackComposition v.hom (productProjection T ordered)).hom.app orderedFactor)
  have heq : (boundedBelowPullbackComposition e.hom (productProjection T surface)).hom.app
        convolution ≫ (boundedBelowInverseImage e.hom).map (projectionMate T a b) ≫ hm =
      m ≫ q := hp
  have : IsIso (m ≫ q) := heq ▸ inferInstance
  have : IsIso q := by dsimp only [q]; infer_instance
  exact IsIso.of_isIso_comp_right _ q

private theorem actionEquivariance_identity {H : AnalyticGroup.{0}}
    {A : AnalyticAction H surface} {B : AnalyticAction H ordered} (h : Commutes A B)
    (a : DerivedAdjunction (productMap H.space)) (b : DerivedAdjunction convolutionMap)
    (r : (boundedBelowInverseImage A.act).obj convolution ⟶
      (boundedBelowInverseImage (projection H surface)).obj convolution)
    (hr : r ≫ coefficientMate (projectionSquare H.space) a b =
      coefficientMate (actionSquare h) a b) :
    pullbackMorphism (identitySection H surface) (identity_act A) identity_projection r.hom = 𝟙 _ := by
  let hI : convolutionMap ≫ identitySection H surface =
      identitySection H ordered ≫ productMap H.space := TopCat.ext (fun _ => rfl)
  let hOne : convolutionMap ≫ 𝟙 surface = 𝟙 ordered ≫ convolutionMap :=
    TopCat.ext (fun _ => rfl)
  have hx := directImageComparisonIsIso (Iso.refl surface) (Iso.refl ordered) hOne b b orderedFactor
  have : IsIso ((coefficientMate hOne b b).hom) := coefficientMate_isIso _ _ _ hx
  apply (cancel_mono ((coefficientMate hOne b b).hom)).mp
  rw [Category.id_comp]
  exact pullbackMorphism_coefficientMate_of_eq (actionSquare h) (projectionSquare H.space)
    hI b a b (identity_act A) identity_projection
    (identity_act B) identity_projection hOne hOne r hr

private theorem actionEquivariance_multiplication {H : AnalyticGroup.{0}}
    {A : AnalyticAction H surface} {B : AnalyticAction H ordered} (h : Commutes A B)
    (a : DerivedAdjunction (productMap H.space)) (b : DerivedAdjunction convolutionMap)
    (a₂ : DerivedAdjunction (productMap (TopCat.of (H.space × H.space))))
    (hp₂ : IsIso (projectionMate (TopCat.of (H.space × H.space)) a₂ b))
    (r : (boundedBelowInverseImage A.act).obj convolution ⟶
      (boundedBelowInverseImage (projection H surface)).obj convolution)
    (hr : r ≫ coefficientMate (projectionSquare H.space) a b =
      coefficientMate (actionSquare h) a b) :
    pullbackMorphism (multiplyParameters H surface) rfl rfl r.hom =
      pullbackMorphism (firstAfterSecond A) (multiply_act A) (first_projection A) r.hom ≫
      pullbackMorphism (secondParameter H surface) rfl multiply_projection r.hom := by
  let c := DerivedLocalSheaves.derivedInverseDirectAdjunctionData (nestedProductMap H)
  let hm : nestedProductMap H ≫ multiplyParameters H surface =
      multiplyParameters H ordered ≫ productMap H.space := TopCat.ext (fun _ => rfl)
  let hf : nestedProductMap H ≫ firstAfterSecond A =
      firstAfterSecond B ≫ productMap H.space := TopCat.ext (fun p => Prod.ext rfl (h p.2.1 p.2.2).symm)
  let hs : nestedProductMap H ≫ secondParameter H surface =
      secondParameter H ordered ≫ productMap H.space := TopCat.ext (fun _ => rfl)
  let hP := nestedProjectionSquare H
  let hA := pasteSquares (actionSquare h) hm
  let hM := pasteSquares (actionSquare h) hs
  have hc := coefficientMate_isIso hP c b (nestedProjection_isIso a₂ c b hp₂)
  apply (cancel_mono ((coefficientMate hP c b).hom)).mp
  have h₁ := pullbackMorphism_coefficientMate_of_eq (actionSquare h) (projectionSquare H.space)
    hm b a c rfl rfl rfl rfl hA hP r hr
  have h₂ := pullbackMorphism_coefficientMate_of_eq (actionSquare h) (projectionSquare H.space)
    hs b a c rfl multiply_projection rfl multiply_projection hM hP r hr
  have h₃ := pullbackMorphism_coefficientMate_of_eq (actionSquare h) (projectionSquare H.space)
    hf b a c (multiply_act A) (first_projection A) (multiply_act B) (first_projection B)
    hA hM r hr
  rw [Category.assoc, h₂, h₁, h₃]

theorem parameterTransport : Expected.ParameterTransport := by
  intro K H A B h φ hφ a a' b α _ha _ha' _hb _hproj _hproj' hα
  let p := parameterMap φ hφ surface
  let q := parameterMap φ hφ ordered
  let α' := restrictEquivariance φ hφ A α
  have hp : productMap K.space ≫ p = q ≫ productMap H.space :=
    TopCat.ext (fun _ => rfl)
  let r : (boundedBelowInverseImage A.act).obj convolution ⟶
      (boundedBelowInverseImage (projection H surface)).obj convolution :=
    ObjectProperty.homMk α.iso.hom
  have hr : r ≫ coefficientMate (projectionSquare H.space) a b =
      coefficientMate (actionSquare h) a b := by
    apply ObjectProperty.hom_ext
    exact hα
  have hpp : p ≫ projection H surface = productProjection K.space surface :=
    TopCat.ext (fun _ => rfl)
  have hqq : q ≫ projection H ordered = productProjection K.space ordered :=
    TopCat.ext (fun _ => rfl)
  refine ⟨α', ?_, rfl⟩
  exact pullbackMorphism_coefficientMate_of_eq (actionSquare h) (projectionSquare H.space)
    hp b a a' rfl hpp rfl hqq (actionSquare (restrict_commutes h φ hφ))
    (projectionSquare K.space) r hr

theorem actionTransport : Expected.ActionTransport := by
  intro H A B h a b a₂ ha hb _ha₂ hP hP₂
  have hA : IsIso (actionMate h a b) := actionMate_isIso h a b
  have hP' : IsIso (projectionComparison H.space a b) :=
    coefficientMate_isIso (projectionSquare H.space) a b hP
  have hA' : IsIso (actionComparison h a b) :=
    coefficientMate_isIso (actionSquare h) a b hA
  let iso := asIso (actionComparison h a b) ≪≫ (asIso (projectionComparison H.space a b)).symm
  have he : iso.hom ≫ projectionComparison H.space a b = actionComparison h a b := by
    let pIso := asIso (projectionComparison H.space a b)
    change (actionComparison h a b ≫ pIso.inv) ≫ pIso.hom = actionComparison h a b
    rw [Category.assoc, pIso.inv_hom_id, Category.comp_id]
  let r : (boundedBelowInverseImage A.act).obj convolution ⟶
      (boundedBelowInverseImage (projection H surface)).obj convolution :=
    ObjectProperty.homMk iso.hom
  have hr : r ≫ coefficientMate (projectionSquare H.space) a b =
      coefficientMate (actionSquare h) a b := by
    apply ObjectProperty.hom_ext
    exact he
  let α : A.Equivariance convolution.obj :=
    ⟨iso, actionEquivariance_identity h a b r hr,
      actionEquivariance_multiplication h a b a₂ hP₂ r hr⟩
  have h0 : (normalizedUnit b).hom = unit := normalizedUnit_eq_shiftedUnit convolutionMap b hb
  have h1 : (normalizedUnit a).hom = productUnit H.space :=
    normalizedUnit_eq_shiftedUnit (productMap H.space) a ha
  have huA := congrArg InducedCategory.Hom.hom (normalizedUnit_square (actionSquare h) a b)
  change (derivedInverseImage A.act).map (normalizedUnit b).hom ≫ actionComparison h a b =
    (shiftedConstantPullback A.act 2).hom ≫ (normalizedUnit a).hom at huA
  rw [h0, h1] at huA
  have huP := congrArg InducedCategory.Hom.hom (normalizedUnit_square (projectionSquare H.space) a b)
  change (derivedInverseImage (projection H surface)).map (normalizedUnit b).hom ≫
    projectionComparison H.space a b =
    (shiftedConstantPullback (projection H surface) 2).hom ≫ (normalizedUnit a).hom at huP
  rw [h0, h1] at huP
  have hu : (derivedInverseImage A.act).map unit ≫ iso.hom =
      (shiftedConstantPullback A.act 2 ≪≫
        (shiftedConstantPullback (projection H surface) 2).symm).hom ≫
        (derivedInverseImage (projection H surface)).map unit := by
    apply (cancel_mono (projectionComparison H.space a b)).mp
    rw [Category.assoc, he, huA, Category.assoc, huP]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  obtain ⟨C, v, δ, e, hT, he₁, he₂⟩ := projectionTriangle a b huP
  exact ⟨actionMate_paste h a b, hA, α, he, huA, hu, C, v, δ, e, hT, he₁, he₂, huP⟩

end RepTheorySurvey.Geometric.ConvolutionActionComparisons
