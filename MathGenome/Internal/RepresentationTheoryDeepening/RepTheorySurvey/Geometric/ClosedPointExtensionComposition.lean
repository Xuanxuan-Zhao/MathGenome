import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedPointExtensionComposition
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportPullbackPasting
noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.ClosedPointExtensionComposition

open Analytic Analytic.IntersectionComplex LocalSheaf
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open AnalyticAction (projection)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open ClosedPointExtensionCompositionSpecs (closedPointComposition)
open ClosedSupportPullbackPastingSpecs (SquareRestriction)

set_option allowUnsafeReducibility true in
attribute [local reducible] Analytic.DerivedPullbackPasting.Expected.SquareType

open private derivedClosedImage_supported derivedClosedImageCounit_isIso pullback_supported
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
open private parameterInclusion_closed adjointSquareMap_counit
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension

private theorem parameterInclusion_range {U V : TopCat.{0}} (H : AnalyticGroup.{0}) (j : U ⟶ V) :
    Set.range (parameterInclusion H j) =
      (AnalyticAction.projection H V) ⁻¹' Set.range j := by
  ext ⟨g, x⟩
  change (∃ p : H.space × U, (p.1, j p.2) = (g, x)) ↔ ∃ u : U, j u = x
  constructor
  · rintro ⟨⟨_, u⟩, h⟩
    exact ⟨u, congrArg Prod.snd h⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(g, u), rfl⟩

private theorem compositeCounit {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ C} {R : C ⥤ A} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ S : C ⥤ B}
    (a : L ⊣ R) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b : L₂ ⊣ S)
    (e : L ≅ L₁ ⋙ L₂) (F : C) :
    let u := a.rightAdjointUniq ((a₁.comp a₂).ofNatIsoLeft e.symm)
    let w := a₂.rightAdjointUniq b
    let c := u.hom.app F ≫ R₁.map (w.hom.app F)
    L.map c ≫ e.hom.app (R₁.obj (S.obj F)) ≫
      L₂.map (a₁.counit.app (S.obj F)) ≫ b.counit.app F = a.counit.app F := by
  intro u w c
  have h₁ := a.rightAdjointUniq_hom_app_counit ((a₁.comp a₂).ofNatIsoLeft e.symm) F
  have h₂ := a₂.rightAdjointUniq_hom_app_counit b F
  have hn : L.map (R₁.map (w.hom.app F)) ≫ e.hom.app (R₁.obj (S.obj F)) =
    e.hom.app (R₁.obj (R₂.obj F)) ≫ L₂.map (L₁.map (R₁.map (w.hom.app F))) :=
    e.hom.naturality (R₁.map (w.hom.app F))
  have hn' : L₁.map (R₁.map (w.hom.app F)) ≫ a₁.counit.app (S.obj F) =
      a₁.counit.app (R₂.obj F) ≫ w.hom.app F := a₁.counit.naturality (w.hom.app F)
  change L.map (u.hom.app F) ≫ e.hom.app (R₁.obj (R₂.obj F)) ≫
      (a₁.comp a₂).counit.app F = _ at h₁
  rw [Adjunction.comp_counit_app] at h₁
  simp only [c, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, hn', Functor.map_comp, Category.assoc, h₂]
  exact h₁

private theorem pointCompositionCounit {X Y : TopCat.{0}} {x : Y}
    (hx : IsClosed ({x} : Set Y)) (i : Y ⟶ X) (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion ({x} : Set Y)) ⊣ closedExtensionPlus hx)
    (F : BoundedBelow (TopCat.of ({x} : Set Y))) :
    let p := closedInclusion ({x} : Set Y)
    let G := (derivedDirectImage i).obj ((closedExtensionPlus hx).obj F)
    let c := ((closedPointComposition hx i a b).hom.app F).hom
    (derivedInverseImage (p ≫ i)).map c ≫
      (derivedInverseImageComposition p i).hom.app G.obj ≫
      (derivedInverseImage p).map ((a i).counit.app ((closedExtensionPlus hx).obj F)).hom ≫
      (b.counit.app F).hom = ((a (p ≫ i)).counit.app F).hom := by
  dsimp only
  let p := closedInclusion ({x} : Set Y)
  let c := (closedPointComposition hx i a b).hom.app F
  let G := (derivedDirectImage i).obj ((closedExtensionPlus hx).obj F)
  have h := compositeCounit (a (p ≫ i)) (a i) (a p) b (boundedBelowPullbackComposition p i) F
  change (boundedBelowInverseImage (p ≫ i)).map c ≫
      (boundedBelowPullbackComposition p i).hom.app G ≫
      (boundedBelowInverseImage p).map ((a i).counit.app ((closedExtensionPlus hx).obj F)) ≫
      b.counit.app F = (a (p ≫ i)).counit.app F at h
  have hh := congrArg (fun f : (boundedBelowInverseImage (p ≫ i)).obj
      ((derivedDirectImage (p ≫ i)).obj F) ⟶ F => f.hom) h
  simpa only [ObjectProperty.FullSubcategory.comp_hom] using! hh

set_option maxHeartbeats 1200000 in
private theorem squareTranspose {U X V Y : TopCat.{0}} {j : U ⟶ X} {i : V ⟶ Y}
    {e : X ⟶ Y} {v : U ⟶ V} (h : j ≫ e = v ≫ i)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    {R : BoundedBelow V ⥤ BoundedBelow Y} (b : boundedBelowInverseImage i ⊣ R)
    (F : BoundedBelow V) :
    ((boundedBelowInverseImage j).map (adjointSquareMap (pullbackSquare h) a b F) ≫
        a.counit.app ((boundedBelowInverseImage v).obj F)).hom =
      (squareValue h).hom.app (R.obj F).obj ≫ (derivedInverseImage v).map (b.counit.app F).hom := by
  have hh := adjointSquareMap_counit (pullbackSquare h) a b F
  have he := congrArg (fun f : (boundedBelowInverseImage j).obj ((boundedBelowInverseImage e).obj (R.obj F)) ⟶
    (boundedBelowInverseImage v).obj F => f.hom) hh
  have hc := RepTheorySurvey.Geometric.DerivedPullbackPasting.squareBoundedBelowCompatibility h (R.obj F)
  simp only [ObjectProperty.FullSubcategory.comp_hom] at he
  rw [hc] at he
  exact he

set_option maxHeartbeats 1500000 in
private theorem pointStageCounit {X Y Z V W U : TopCat.{0}}
    {p : U ⟶ Y} {i : Y ⟶ X}
    {j : W ⟶ Z} {l : V ⟶ W} {t : Z ⟶ X} {v : W ⟶ Y} {v' : V ⟶ U}
    (hD : j ≫ t = v ≫ i) (hI : l ≫ v = v' ≫ p)
    (hP : (l ≫ j) ≫ t = v' ≫ (p ≫ i))
    {E E' : Derived X} {F : Derived Y} {K : Derived U}
    (c : E ⟶ E') (εD : (derivedInverseImage i).obj E' ⟶ F)
    (εI : (derivedInverseImage p).obj F ⟶ K)
    (εP : (derivedInverseImage (p ≫ i)).obj E ⟶ K)
    (hc : (derivedInverseImage (p ≫ i)).map c ≫
      (derivedInverseImageComposition p i).hom.app E' ≫ (derivedInverseImage p).map εD ≫ εI = εP) :
    (derivedInverseImage (l ≫ j)).map ((derivedInverseImage t).map c) ≫
      (derivedInverseImageComposition l j).hom.app ((derivedInverseImage t).obj E') ≫
      (derivedInverseImage l).map ((squareValue hD).hom.app E' ≫ (derivedInverseImage v).map εD) ≫
      (squareValue hI).hom.app F ≫ (derivedInverseImage v').map εI =
      (squareValue hP).hom.app E ≫ (derivedInverseImage v').map εP := by
  let f := derivedInverseImage (l ≫ j)
  let h := derivedInverseImage v'
  have hn : f.map ((derivedInverseImage t).map c) ≫ (squareValue hP).hom.app E' =
      (squareValue hP).hom.app E ≫ h.map ((derivedInverseImage (p ≫ i)).map c) :=
    (squareValue hP).hom.naturality c
  have hn' : (derivedInverseImage l).map ((derivedInverseImage v).map εD) ≫
      (squareValue hI).hom.app F = (squareValue hI).hom.app ((derivedInverseImage i).obj E') ≫
        h.map ((derivedInverseImage p).map εD) := (squareValue hI).hom.naturality εD
  have hh := RepTheorySurvey.Geometric.DerivedPullbackPasting.squareHorizontalPasting hI hD E'
  have hsq : (squareValue hP).hom.app E' ≫ h.map ((derivedInverseImageComposition p i).hom.app E') =
      (derivedInverseImageComposition l j).hom.app ((derivedInverseImage t).obj E') ≫
      (derivedInverseImage l).map ((squareValue hD).hom.app E') ≫
      (squareValue hI).hom.app ((derivedInverseImage i).obj E') := by
    rw [show (squareValue hP).hom.app E' = _ from hh]
    simp only [Category.assoc]
    change _ ≫ _ ≫ _ ≫ h.map ((derivedInverseImageComposition p i).inv.app E') ≫
      h.map ((derivedInverseImageComposition p i).hom.app E') = _
    rw [← h.map_comp, Iso.inv_hom_id_app, h.map_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% hn']
  rw [← reassoc_of% hsq, reassoc_of% hn, ← h.map_comp_assoc, ← h.map_comp_assoc,
    ← h.map_comp]
  simp only [Category.assoc, hc, h]

set_option maxHeartbeats 800000 in
private theorem mateRestriction
    (transpose : ClosedSupportBaseChangeSpecs.Expected.MateEquationIff)
    {U X V Y : TopCat.{0}} {j : U ⟶ X} {i : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V}
    (h : j ≫ e = v ≫ i) (a : DerivedAdjunctions.{0})
    {R : BoundedBelow V ⥤ BoundedBelow Y} (b : boundedBelowInverseImage i ⊣ R)
    (F : BoundedBelow V) {H : AnalyticGroup.{0}}
    {A : AnalyticAction H X} {B : AnalyticAction H U}
    (ha : parameterInclusion H j ≫ A.act = B.act ≫ j)
    (α : (derivedInverseImage A.act).obj ((derivedInverseImage e).obj (R.obj F).obj) ⟶
      (derivedInverseImage (projection H X)).obj ((derivedInverseImage e).obj (R.obj F).obj))
    (β : (derivedInverseImage B.act).obj ((derivedInverseImage v).obj F.obj) ⟶
      (derivedInverseImage (projection H U)).obj ((derivedInverseImage v).obj F.obj))
    (hm : ClosedSupportBaseChangeSpecs.MateCommutes ha (projectionSquare H j)
      (a (parameterInclusion H j)) (a j) (adjointSquareMap (pullbackSquare h) (a j) b F) α β) :
    SquareRestriction ha (projectionSquare H j)
      ((squareValue h).hom.app (R.obj F).obj ≫ (derivedInverseImage v).map (b.counit.app F).hom)
      α β := by
  have hres := (transpose ha (projectionSquare H j) (a (parameterInclusion H j)) (a j)
    (adjointSquareMap (pullbackSquare h) (a j) b F) α β).mp hm
  rw [squareTranspose h (a j) b F] at hres
  exact hres

private theorem projectionPullbackSupported
    {X Y Z V : TopCat.{0}} {H : AnalyticGroup.{0}} {t : Z ⟶ X} {m : V ⟶ Z}
    {i : Y ⟶ X} (hRange : Set.range m = t ⁻¹' Set.range i)
    {E G : BoundedBelow X} (hE : DerivedSupportedOn (Set.range i) E) (c : E ≅ G) :
    DerivedSupportedOn (Set.range (parameterInclusion H m))
      ((boundedBelowInverseImage (projection H Z)).obj ((boundedBelowInverseImage t).obj G)) := by
  have hG : DerivedSupportedOn (Set.range i) G := by
    intro n x hx
    exact (hE n x hx).of_iso
      ((cohomology X n ⋙ stalk x).mapIso ((DerivedCategory.Plus.ι (C := Sheaves X)).mapIso c)).symm
  rw [parameterInclusion_range, hRange]
  exact pullback_supported (projection H Z) _ _ (pullback_supported t _ G hG)

set_option maxHeartbeats 1500000 in
private theorem pasteRestrictions {U X Z V Y W : TopCat.{0}}
    {j : U ⟶ X} {j' : X ⟶ Z} {i : V ⟶ Y} {i' : Y ⟶ W}
    {v q : U ⟶ V} {e p : X ⟶ Y} {e' p' : Z ⟶ W}
    (h : j ≫ e = v ≫ i) (k : j ≫ p = q ≫ i)
    (h' : j' ≫ e' = e ≫ i') (k' : j' ≫ p' = p ≫ i')
    {G : Derived W} {F : Derived Y} {K : Derived V}
    (ε : (derivedInverseImage i').obj G ⟶ F) (η : (derivedInverseImage i).obj F ⟶ K)
    {α : (derivedInverseImage e').obj G ⟶ (derivedInverseImage p').obj G}
    {β : (derivedInverseImage e).obj F ⟶ (derivedInverseImage p).obj F}
    {γ : (derivedInverseImage v).obj K ⟶ (derivedInverseImage q).obj K}
    (hr : SquareRestriction h' k' ε α β) (hs : SquareRestriction h k η β γ) :
    SquareRestriction (ClosedSupportPullbackPastingSpecs.horizontalSquare h h') (ClosedSupportPullbackPastingSpecs.horizontalSquare k k')
      ((derivedInverseImageComposition i i').hom.app G ≫ (derivedInverseImage i).map ε ≫ η)
      α γ := by
  let u (z : Z ⟶ W) := (derivedInverseImageComposition j j').hom.app ((derivedInverseImage z).obj G)
  let c (z : X ⟶ Y) (z' : Z ⟶ W) (hz : j' ≫ z' = z ≫ i') :=
    (squareValue hz).hom.app G ≫ (derivedInverseImage z).map ε
  let d (z : U ⟶ V) (z' : X ⟶ Y) (hz : j ≫ z' = z ≫ i) :=
    (squareValue hz).hom.app F ≫ (derivedInverseImage z).map η
  have hbridge {z : U ⟶ V} {z' : X ⟶ Y} {z'' : Z ⟶ W}
      (hz : j ≫ z' = z ≫ i) (hz' : j' ≫ z'' = z' ≫ i') :
      (squareValue (ClosedSupportPullbackPastingSpecs.horizontalSquare hz hz')).hom.app G ≫
        (derivedInverseImage z).map
          ((derivedInverseImageComposition i i').hom.app G ≫ (derivedInverseImage i).map ε ≫ η) =
      u z'' ≫ (derivedInverseImage j).map (c z' z'' hz') ≫ d z z' hz := by
    have hn : (derivedInverseImage j).map ((derivedInverseImage z').map ε) ≫
        (squareValue hz).hom.app F = (squareValue hz).hom.app ((derivedInverseImage i').obj G) ≫
          (derivedInverseImage z).map ((derivedInverseImage i).map ε) :=
      (squareValue hz).hom.naturality ε
    have hh := RepTheorySurvey.Geometric.DerivedPullbackPasting.squareHorizontalPasting hz hz' G
    rw [show (squareValue (ClosedSupportPullbackPastingSpecs.horizontalSquare hz hz')).hom.app G = _ from hh]
    simp only [u, c, d, Functor.map_comp, Category.assoc]
    rw [← (derivedInverseImage z).map_comp_assoc ((derivedInverseImageComposition i i').inv.app G)
      ((derivedInverseImageComposition i i').hom.app G), Iso.inv_hom_id_app,
      (derivedInverseImage z).map_id, Category.id_comp, reassoc_of% hn]
  unfold SquareRestriction
  rw [hbridge k k', reassoc_of% (hbridge h h')]
  change (derivedInverseImage (j ≫ j')).map α ≫ u p' ≫
    (derivedInverseImage j).map (c p p' k') ≫ d q p k =
      u e' ≫ (derivedInverseImage j).map (c e e' h') ≫ d v e h ≫ γ
  have hn : (derivedInverseImage (j ≫ j')).map α ≫ u p' =
      u e' ≫ (derivedInverseImage j).map ((derivedInverseImage j').map α) :=
    (derivedInverseImageComposition j j').hom.naturality α
  have hr' : (derivedInverseImage j').map α ≫ c p p' k' = c e e' h' ≫ β := by
    simpa only [c, Category.assoc] using! hr
  have hs' : (derivedInverseImage j).map β ≫ d q p k = d v e h ≫ γ := by
    simpa only [d, Category.assoc] using! hs
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, hr', Functor.map_comp]
  simp only [Category.assoc, hs']

set_option maxHeartbeats 1200000 in
private theorem compareRestrictions {U X V W : TopCat.{0}}
    {j : U ⟶ X} {i : V ⟶ W} {e p : X ⟶ W} {v q : U ⟶ V}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {G G' : Derived W} {F : Derived V} (c : G ⟶ G')
    {ε : (derivedInverseImage i).obj G ⟶ F} {ε' : (derivedInverseImage i).obj G' ⟶ F}
    (hc : (derivedInverseImage i).map c ≫ ε' = ε)
    (α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G)
    (α' : (derivedInverseImage e).obj G' ⟶ (derivedInverseImage p).obj G')
    (β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F)
    (h : SquareRestriction he hp ε α β) (h' : SquareRestriction he hp ε' α' β) :
    (derivedInverseImage j).map ((derivedInverseImage e).map c ≫ α') ≫
        ((squareValue hp).hom.app G' ≫ (derivedInverseImage q).map ε') =
      (derivedInverseImage j).map (α ≫ (derivedInverseImage p).map c) ≫
        ((squareValue hp).hom.app G' ≫ (derivedInverseImage q).map ε') := by
  have he' : (derivedInverseImage j).map ((derivedInverseImage e).map c) ≫
      (squareValue he).hom.app G' = (squareValue he).hom.app G ≫
        (derivedInverseImage v).map ((derivedInverseImage i).map c) :=
    (squareValue he).hom.naturality c
  have hp' : (derivedInverseImage j).map ((derivedInverseImage p).map c) ≫
      (squareValue hp).hom.app G' = (squareValue hp).hom.app G ≫
        (derivedInverseImage q).map ((derivedInverseImage i).map c) :=
    (squareValue hp).hom.naturality c
  unfold SquareRestriction at h h'
  simp only [Functor.map_comp, Category.assoc]
  rw [h', reassoc_of% he', ← (derivedInverseImage v).map_comp_assoc, hc,
    reassoc_of% hp', ← (derivedInverseImage q).map_comp, hc]
  exact h.symm

universe u

set_option maxHeartbeats 1800000 in
/-- The stage equation follows by transposing the actual mates and pasting the
restricted arrows. The pullback premises retain their general universe, while
the stage diagram uses the pullback calculations for TopCat.{0}. -/
theorem closedPointCompositionEquivariant_conditional
    (_actionProjectionMatesAreIso : ClosedSupportBaseChangeSpecs.Expected.ActionProjectionMatesAreIso)
    (_closedBaseChange : ClosedSupportBaseChangeSpecs.Expected.ClosedBaseChange)
    (_derivedDirectImageMateEquationIff : ClosedSupportBaseChangeSpecs.Expected.DerivedDirectImageMateEquationIff)
    (transpose : ClosedSupportBaseChangeSpecs.Expected.MateEquationIff)
    (_stageDatum : ClosedSupportBaseChangeSpecs.Expected.StageDatum)
    (supportedRestriction : ClosedSupportBaseChangeSpecs.Expected.SupportedRestrictionBijective)
    (_flattenInjective : ClosedSupportPullbackPastingSpecs.Expected.FlattenInjective.{u})
    (_flattenPullback : ClosedSupportPullbackPastingSpecs.Expected.FlattenPullback.{u})
    (_flattenRestriction : ClosedSupportPullbackPastingSpecs.Expected.FlattenRestriction.{u})
    (_mateNaturality : ClosedSupportPullbackPastingSpecs.Expected.MateNaturality.{u})
    (_mateVerticalPasting : ClosedSupportPullbackPastingSpecs.Expected.MateVerticalPasting.{u})
    (_pullbackComparisonAtUnderlying :
      ClosedSupportPullbackPastingSpecs.Expected.PullbackComparisonAtUnderlying.{u})
    (_squareRestrictionFlatten : ClosedSupportPullbackPastingSpecs.Expected.SquareRestrictionFlatten.{u})
    (_squareRestrictionHorizontalPasting : ClosedSupportPullbackPastingSpecs.Expected.SquareRestrictionHorizontalPasting.{u})
    (_squareRestrictionNaturality : ClosedSupportPullbackPastingSpecs.Expected.SquareRestrictionNaturality.{u})
    (_squareRestrictionParameterChange :
      ClosedSupportPullbackPastingSpecs.Expected.SquareRestrictionParameterChange.{u})
    (_squareRestrictionPullbackForm :
      ClosedSupportPullbackPastingSpecs.Expected.SquareRestrictionPullbackForm.{u}) :
    ClosedPointExtensionCompositionSpecs.Expected.ClosedPointCompositionEquivariant := by
  intro X Y Z U V x hx i hi t j m l v w hj hm hSurface rSurface hPoint rPoint hStage hIntersection
  subst m
  intro H A B C hA hB hC a b F
  intro E K G c E₀ G₀ K₀ F₀ q r s cSurface cPoint cIntersection α β γ δ hα hβ hγ
  let m := l ≫ j
  let p := closedInclusion ({x} : Set Y)
  let z := (derivedInverseImage t).map c
  let εSurface := (squareValue hSurface).hom.app G.obj ≫
    (derivedInverseImage v).map ((a i).counit.app K).hom
  let εIntersection := (squareValue hIntersection).hom.app K.obj ≫
    (derivedInverseImage w).map (b.counit.app F).hom
  let εPoint := (squareValue hPoint).hom.app E.obj ≫
    (derivedInverseImage w).map ((a (p ≫ i)).counit.app F).hom
  let κ := (derivedInverseImageComposition l j).hom.app G₀ ≫
    (derivedInverseImage l).map εSurface ≫ εIntersection
  have hrE : SquareRestriction hB (projectionSquare H m) εPoint α δ :=
    mateRestriction transpose hPoint a (a (p ≫ i)) F hB α δ hα
  have hrG : SquareRestriction hA (projectionSquare H j) εSurface β γ :=
    mateRestriction transpose hSurface a (a i) K hA β γ hβ
  have hrK : SquareRestriction hC (projectionSquare H l) εIntersection γ δ :=
    mateRestriction transpose hIntersection a b F hC γ δ hγ
  have hrPasted : SquareRestriction hB (projectionSquare H m) κ β δ := by
    exact pasteRestrictions hC (projectionSquare H l) hA (projectionSquare H j)
      εSurface εIntersection hrG hrK
  have hε : (derivedInverseImage m).map z ≫ κ = εPoint :=
    pointStageCounit hSurface hIntersection hPoint c
      ((a i).counit.app K).hom (b.counit.app F).hom ((a (p ≫ i)).counit.app F).hom
      (pointCompositionCounit hx i a b F)
  have hp : IsClosedEmbedding (p ≫ i) :=
    hi.comp (show IsClosedEmbedding p from hx.isClosedEmbedding_subtypeVal)
  letI : IsIso ((a (p ≫ i)).counit.app F) :=
    derivedClosedImageCounit_isIso hp (a (p ≫ i)) F
  letI : IsIso ((a (p ≫ i)).counit.app F).hom :=
    (DerivedCategory.Plus.ι (C := Sheaves (TopCat.of ({x} : Set Y)))).map_isIso _
  letI : IsIso εPoint := by
    dsimp only [εPoint]
    infer_instance
  let τ := (closedPointComposition hx i a b).app F
  letI : IsIso c :=
    (DerivedCategory.Plus.ι (C := Sheaves X)).map_isIso τ.hom
  letI : IsIso ((derivedInverseImage m).map z ≫ κ) :=
    hε.symm ▸ inferInstanceAs (IsIso εPoint)
  letI : IsIso κ := IsIso.of_isIso_comp_left ((derivedInverseImage m).map z) κ
  have hproj : DerivedSupportedOn (Set.range (parameterInclusion H m))
      ((boundedBelowInverseImage q).obj ((boundedBelowInverseImage t).obj G)) :=
    projectionPullbackSupported rPoint (derivedClosedImage_supported hp F) τ
  have hr := compareRestrictions hB (projectionSquare H m) z hε α β δ hrE hrPasted
  have hr' := (cancel_mono ((squareValue (projectionSquare H m)).hom.app G₀ ≫
    (derivedInverseImage s).map κ)).mp hr
  exact (supportedRestriction (parameterInclusion_closed H hm) a
    ((boundedBelowInverseImage A.act).obj ((boundedBelowInverseImage t).obj E))
    ((boundedBelowInverseImage q).obj ((boundedBelowInverseImage t).obj G)) hproj).1 hr'

end RepTheorySurvey.Geometric.ClosedPointExtensionComposition

theorem _root_.«RepTheorySurvey».«Geometric».«ClosedPointExtensionComposition».«closedPointCompositionEquivariant» : _root_.«RepTheorySurvey».«Geometric».«ClosedPointExtensionCompositionSpecs».«Expected».«ClosedPointCompositionEquivariant» :=
  @_root_.«RepTheorySurvey».«Geometric».«ClosedPointExtensionComposition».«closedPointCompositionEquivariant_conditional».{0} (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«actionProjectionMatesAreIso») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«closedBaseChange») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«derivedDirectImageMateEquationIff») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«mateEquationIff») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«stageDatum») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«supportedRestrictionBijective») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«flattenInjective».{0}) (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«flattenPullback».{0}) (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«flattenRestriction».{0}) (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«mateNaturality».{0}) (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«mateVerticalPasting».{0}) (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«pullbackComparisonAtUnderlying».{0}) (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«squareRestrictionFlatten».{0}) (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«squareRestrictionHorizontalPasting».{0}) (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«squareRestrictionNaturality».{0}) (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«squareRestrictionParameterChange».{0}) (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPullbackPasting».«squareRestrictionPullbackForm».{0})
