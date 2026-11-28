import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionPointCoefficients
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepLocalCohomology
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open TopCat.Presheaf

namespace RepTheorySurvey.Geometric.ConvolutionPointCoefficients

open Analytic AnalyticAction ConvolutionUnitConeSpecs ConvolutionPointCoefficientsSpecs
open ConvolutionConstantDescentSpec

set_option backward.isDefEq.respectTransparency false

open private stalkPushforward_naturality from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels
open private derivedComposition_single from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent

theorem closedPointPullback : Expected.ClosedPointPullback := by
  intro Y f W x hx hW h
  let F := (inverseImage f).obj (pointSheaf x)
  have hs : SupportedOn W F := by
    intro y hy
    have hp : f y ∉ ({x} : Set surface) := by rwa [hW] at hy
    exact (closedDirectImage_supported hx _ (f y) hp).of_iso
      (inverseImageStalkIso f (pointSheaf x) y).symm
  have hclosed : IsClosed W := hW ▸ hx.preimage f.hom.continuous
  have := closedInverseDirectUnit_isIso hclosed F hs
  have := inducedCounit_isIso (f := closedInclusion ({x} : Set surface))
    IsInducing.subtypeVal (rational (TopCat.of ({x} : Set surface)))
  have ho : IsIso (ordinaryPointPullback h) := by
    unfold ordinaryPointPullback
    rw [Adjunction.homEquiv_unit]
    infer_instance
  exact ⟨ho, by unfold derivedPointPullback; infer_instance⟩

private theorem stalkInverse_naturality {Y X : TopCat.{0}} (f : Y ⟶ X)
    {F G : Sheaves X} (v : F ⟶ G) (y : Y) :
    inverseImageStalkMap f F y ≫ (stalk y).map ((inverseImage f).map v) =
      (stalk (f y)).map v ≫ inverseImageStalkMap f G y := by
  let a := inverseDirectAdjunction f
  unfold inverseImageStalkMap
  rw [Category.assoc]
  erw [← stalkPushforward_naturality f ((inverseImage f).map v).hom y]
  change (stalk (f y)).map (a.unit.app F) ≫
    (stalk (f y)).map ((directImage f).map ((inverseImage f).map v)) ≫ _ = _
  have hn := a.unit.naturality v
  change v ≫ a.unit.app G = a.unit.app F ≫ (directImage f).map ((inverseImage f).map v) at hn
  rw [← Functor.map_comp_assoc, ← hn, Functor.map_comp, Category.assoc]

/-- The maps on stalks from the inverse-image units compose using the inverse-image
composition comparison. -/
private theorem stalkInverse_composition {W Y X : TopCat.{0}} (k : W ⟶ Y) (f : Y ⟶ X)
    (F : Sheaves X) (w : W) :
    inverseImageStalkMap (k ≫ f) F w ≫
        (stalk w).map ((inverseImageComposition k f).hom.app F) =
      inverseImageStalkMap f F (k w) ≫ inverseImageStalkMap k ((inverseImage f).obj F) w := by
  let a := inverseDirectAdjunction f
  let b := inverseDirectAdjunction k
  let r := inverseDirectAdjunction (k ≫ f)
  unfold inverseImageStalkMap
  rw [Category.assoc]
  erw [← stalkPushforward_naturality (k ≫ f) ((inverseImageComposition k f).hom.app F).hom w]
  change (stalk (f (k w))).map (r.unit.app F) ≫
    (stalk (f (k w))).map ((directImage (k ≫ f)).map
      ((r.leftAdjointUniq (a.comp b)).hom.app F)) ≫ _ = _
  rw [← Functor.map_comp_assoc, Adjunction.unit_leftAdjointUniq_hom_app,
    Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [TopCat.Presheaf.stalkPushforward.comp]
  simp only [Category.assoc]
  have h := stalkPushforward_naturality f (b.unit.app ((inverseImage f).obj F)).hom (k w)
  have hh := congrArg (fun t => t ≫ TopCat.Presheaf.stalkPushforward Coeff k
    ((inverseImage k).obj ((inverseImage f).obj F)).obj w) h
  simp only [Category.assoc] at hh
  erw [hh]
  rfl

private theorem stalk_ext {Y : TopCat.{0}} {F G : Sheaves Y} {v w : F ⟶ G}
    (h : ∀ y : Y, (stalk y).map v = (stalk y).map w) : v = w := by
  apply (TopCat.Sheaf.forget Coeff Y).map_injective
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.section_ext G
  intro y hy
  change TopCat.Presheaf.germ (X := Y) G.obj U.unop y hy (v.hom.app U s) = TopCat.Presheaf.germ (X := Y) G.obj U.unop y hy (w.hom.app U s)
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ v.hom,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ w.hom]
  exact congrArg (fun m : (stalk y).obj F ⟶ (stalk y).obj G =>
    m (TopCat.Presheaf.germ (X := Y) F.obj U.unop y hy s)) (h y)

private theorem stalk_transpose {Y X : TopCat.{0}} (j : Y ⟶ X)
    {F : Sheaves X} {G : Sheaves Y} (v : (inverseImage j).obj F ⟶ G) (z : Y) :
    (stalk (j z)).map ((inverseDirectAdjunction j).homEquiv _ _ v) ≫
        TopCat.Presheaf.stalkPushforward Coeff j G.obj z =
      inverseImageStalkMap j F z ≫ (stalk z).map v := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  unfold inverseImageStalkMap
  rw [Category.assoc]
  congr 1
  exact stalkPushforward_naturality j v.hom z

private def pointStalk {Y : TopCat.{0}} (f : Y ⟶ surface) (x : surface) (y : Y)
    (h : f y = x) :
    (stalk x).obj (pointSheaf x) ⟶ (stalk y).obj ((inverseImage f).obj (pointSheaf x)) :=
  eqToHom (congrArg (fun p : surface => (stalk p).obj (pointSheaf x)) h.symm) ≫
    inverseImageStalkMap f (pointSheaf x) y

private instance {Y : TopCat.{0}} (f : Y ⟶ surface) (x : surface) (y : Y)
    (h : f y = x) : IsIso (pointStalk f x y h) := by
  unfold pointStalk
  infer_instance

private theorem pointStalk_eq {Y : TopCat.{0}} {f g : Y ⟶ surface}
    (hfg : f = g) (x : surface) (y : Y) (hf : f y = x) (hg : g y = x) :
    pointStalk f x y hf ≫
        (stalk y).map (eqToHom (congrArg (fun k => (inverseImage k).obj (pointSheaf x)) hfg)) =
      pointStalk g x y hg := by
  subst g
  simp

private theorem pointStalk_comp {W Y : TopCat.{0}} (k : W ⟶ Y) (f : Y ⟶ surface)
    (x : surface) (w : W) (h : f (k w) = x) :
    pointStalk (k ≫ f) x w h ≫ (stalk w).map ((inverseImageComposition k f).hom.app _) =
      pointStalk f x (k w) h ≫ inverseImageStalkMap k ((inverseImage f).obj (pointSheaf x)) w := by
  simp only [pointStalk, Category.assoc, stalkInverse_composition]

private theorem ordinaryPointPullback_stalk {Y : TopCat.{0}} {f : Y ⟶ surface}
    {W : Set Y} {x : surface}
    (h : closedInclusion W ≫ f = toPoint W x ≫ closedInclusion ({x} : Set surface))
    (z : TopCat.of W) (hz : f z.val = x) :
    pointStalk f x z.val hz ≫ (stalk z.val).map (ordinaryPointPullback h) ≫
        TopCat.Presheaf.stalkPushforward Coeff (closedInclusion W)
          (rational (TopCat.of W)).obj z =
      TopCat.Presheaf.stalkPushforward Coeff (closedInclusion ({x} : Set surface))
        (rational (TopCat.of ({x} : Set surface))).obj ⟨x, rfl⟩ ≫
        inverseImageStalkMap (toPoint W x) (rational (TopCat.of ({x} : Set surface))) z ≫
        (stalk z).map (constantPullback (toPoint W x)).hom := by
  let j := closedInclusion W
  let i := closedInclusion ({x} : Set surface)
  let r := toPoint W x
  let F := pointSheaf x
  let Q := rational (TopCat.of ({x} : Set surface))
  let v : (inverseImage i).obj F ⟶ Q := (inverseDirectAdjunction i).counit.app Q
  let u := (constantPullback r).hom
  change pointStalk f x (j z) hz ≫ (stalk (j z)).map (ordinaryPointPullback h) ≫ _ = _
  let a := (inverseImageComposition j f).hom.app F
  let a' := (inverseImageComposition j f).inv.app F
  let b := eqToHom (congrArg (fun k => (inverseImage k).obj F) h)
  let c := (inverseImageComposition r i).hom.app F
  change pointStalk f x (j z) hz ≫
    (stalk (j z)).map ((inverseDirectAdjunction j).homEquiv _ _
      (a' ≫ b ≫ c ≫ (inverseImage r).map v ≫ u)) ≫ _ = _
  rw [stalk_transpose (j := j)]
  simp only [Functor.map_comp]
  rw [← Category.assoc, ← pointStalk_comp j f x z hz, Category.assoc, ← Functor.map_comp_assoc]
  have haa : a ≫ a' = 𝟙 _ := (inverseImageComposition j f).hom_inv_id_app F
  rw [haa, CategoryTheory.Functor.map_id (stalk z), Category.id_comp, ← Category.assoc,
    pointStalk_eq h x z hz rfl, ← Category.assoc, pointStalk_comp r i x z rfl]
  have hn := stalkInverse_naturality r v z
  simp only [Category.assoc]
  rw [← Category.assoc (inverseImageStalkMap r ((inverseImage i).obj F) z), hn]
  simp only [pointStalk, eqToHom_refl, Category.id_comp, Category.assoc]
  change inverseImageStalkMap i F (r z) ≫ (stalk (r z)).map v ≫ _ = _
  rw [← Category.assoc, inducedCounit_stalk]
  rfl

private def PreservesPointStalks {Y : TopCat.{0}} {f g : Y ⟶ surface} {x : surface}
    (v : (inverseImage f).obj (pointSheaf x) ⟶ (inverseImage g).obj (pointSheaf x)) : Prop :=
  ∀ (y : Y) (hf : f y = x) (hg : g y = x),
    pointStalk f x y hf ≫ (stalk y).map v = pointStalk g x y hg

private theorem pointArrow_unique {Y : TopCat.{0}} {f g : Y ⟶ surface} {x : surface}
    (hx : IsClosed ({x} : Set surface)) (hs : ∀ y : Y, f y = x → g y = x)
    {v w : (inverseImage f).obj (pointSheaf x) ⟶ (inverseImage g).obj (pointSheaf x)}
    (hv : PreservesPointStalks (x := x) v) (hw : PreservesPointStalks (x := x) w) :
    v = w := by
  apply stalk_ext
  intro y
  by_cases hy : f y = x
  · exact (cancel_epi (pointStalk f x y hy)).mp ((hv y hy (hs y hy)).trans (hw y hy (hs y hy)).symm)
  · have hz := (closedDirectImage_supported hx _ (f y) hy).of_iso
      ((inverseImageStalkIso f (pointSheaf x) y).symm)
    exact hz.eq_of_src _ _

private theorem pointArrow_comp {Y : TopCat.{0}} {f g j : Y ⟶ surface} {x : surface}
    (hs : ∀ y : Y, f y = x → g y = x)
    {v : (inverseImage f).obj (pointSheaf x) ⟶ (inverseImage g).obj (pointSheaf x)}
    {w : (inverseImage g).obj (pointSheaf x) ⟶ (inverseImage j).obj (pointSheaf x)}
    (hv : PreservesPointStalks (x := x) v) (hw : PreservesPointStalks (x := x) w) :
    PreservesPointStalks (x := x) (v ≫ w) := by
  intro y hf hj
  rw [Functor.map_comp, ← Category.assoc, hv y hf (hs y hf), hw y (hs y hf) hj]

private theorem pointArrow_id {Y : TopCat.{0}} (f : Y ⟶ surface) (x : surface) :
    PreservesPointStalks (x := x) (𝟙 ((inverseImage f).obj (pointSheaf x))) := by
  intro y hf hg
  simp

private def ordinaryPullbackArrow {W Y X : TopCat.{0}} (k : W ⟶ Y)
    {f g : Y ⟶ X} {F : Sheaves X}
    (v : (inverseImage f).obj F ⟶ (inverseImage g).obj F) :
    (inverseImage (k ≫ f)).obj F ⟶ (inverseImage (k ≫ g)).obj F :=
  (inverseImageComposition k f).hom.app F ≫ (inverseImage k).map v ≫
    (inverseImageComposition k g).inv.app F

private theorem pointArrow_pullback {W Y : TopCat.{0}} (k : W ⟶ Y)
    {f g : Y ⟶ surface} {x : surface}
    {v : (inverseImage f).obj (pointSheaf x) ⟶ (inverseImage g).obj (pointSheaf x)}
    (hv : PreservesPointStalks (x := x) v) :
    PreservesPointStalks (x := x) (ordinaryPullbackArrow k v) := by
  intro w hf hg
  unfold ordinaryPullbackArrow
  simp only [Functor.map_comp, ← Category.assoc]
  rw [pointStalk_comp k f x w hf]
  rw [Category.assoc (pointStalk f x (k w) hf), stalkInverse_naturality]
  rw [← Category.assoc, hv (k w) hf hg, ← pointStalk_comp k g x w hg]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  rw [CategoryTheory.Functor.map_id (stalk w), Category.comp_id]

private def pointDerivedIso {Y : TopCat.{0}} (f : Y ⟶ surface) {x : surface}
    (hx : IsClosed ({x} : Set surface)) :
    (derivedInverseImage f).obj (pointSkyscraper x hx) ≅
      (DerivedCategory.singleFunctor (Sheaves Y) 0).obj ((inverseImage f).obj (pointSheaf x)) :=
  (derivedInverseImage f).mapIso (pointSkyscraperSingle x hx) ≪≫
    ((inverseImage f).mapDerivedCategorySingleFunctor 0).app (pointSheaf x)

private def liftPointArrow {Y : TopCat.{0}} {f g : Y ⟶ surface} {x : surface}
    (hx : IsClosed ({x} : Set surface))
    (v : (inverseImage f).obj (pointSheaf x) ⟶ (inverseImage g).obj (pointSheaf x)) :
    (derivedInverseImage f).obj (pointSkyscraper x hx) ⟶
      (derivedInverseImage g).obj (pointSkyscraper x hx) :=
  (pointDerivedIso f hx).hom ≫ (DerivedCategory.singleFunctor (Sheaves Y) 0).map v ≫
    (pointDerivedIso g hx).inv

private theorem liftPointArrow_id {Y : TopCat.{0}} (f : Y ⟶ surface) {x : surface}
    (hx : IsClosed ({x} : Set surface)) :
    liftPointArrow (f := f) (g := f) hx (𝟙 _) = 𝟙 _ := by
  simp [liftPointArrow]

private theorem liftPointArrow_comp {Y : TopCat.{0}} {f g p : Y ⟶ surface} {x : surface}
    (hx : IsClosed ({x} : Set surface))
    (v : (inverseImage f).obj (pointSheaf x) ⟶ (inverseImage g).obj (pointSheaf x))
    (w : (inverseImage g).obj (pointSheaf x) ⟶ (inverseImage p).obj (pointSheaf x)) :
    liftPointArrow hx (v ≫ w) = liftPointArrow hx v ≫ liftPointArrow hx w := by
  simp [liftPointArrow]

private theorem pointDerivedIso_composition {W Y : TopCat.{0}} (k : W ⟶ Y) (f : Y ⟶ surface)
    {x : surface} (hx : IsClosed ({x} : Set surface)) :
    (derivedInverseImageComposition k f).hom.app (pointSkyscraper x hx) ≫
        (derivedInverseImage k).map (pointDerivedIso f hx).hom ≫
        ((inverseImage k).mapDerivedCategorySingleFunctor 0).hom.app
          ((inverseImage f).obj (pointSheaf x)) =
      (pointDerivedIso (k ≫ f) hx).hom ≫
        (DerivedCategory.singleFunctor (Sheaves W) 0).map
          ((inverseImageComposition k f).hom.app (pointSheaf x)) := by
  unfold pointDerivedIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hn := (derivedInverseImageComposition k f).hom.naturality (pointSkyscraperSingle x hx).hom
  change (derivedInverseImage (k ≫ f)).map _ ≫ _ =
    (derivedInverseImageComposition k f).hom.app _ ≫
      (derivedInverseImage k).map ((derivedInverseImage f).map _) at hn
  rw [← Category.assoc, ← hn, Category.assoc]
  exact congrArg (fun t => (derivedInverseImage (k ≫ f)).map (pointSkyscraperSingle x hx).hom ≫ t)
    (derivedComposition_single k f (pointSheaf x))

private theorem liftPointArrow_pullback {W Y : TopCat.{0}} (k : W ⟶ Y)
    {f g : Y ⟶ surface} {x : surface} (hx : IsClosed ({x} : Set surface))
    (v : (inverseImage f).obj (pointSheaf x) ⟶ (inverseImage g).obj (pointSheaf x)) :
    pullbackMorphism k rfl rfl (liftPointArrow hx v) =
      liftPointArrow hx (ordinaryPullbackArrow k v) := by
  let D := derivedInverseImage k
  let S := DerivedCategory.singleFunctor (Sheaves W) 0
  let F := pointSheaf x
  let e := ((inverseImage k).mapDerivedCategorySingleFunctor 0).hom
  let V := pointSkyscraper x hx
  let c := derivedInverseImageComposition k g
  have hn := e.naturality v
  change D.map ((DerivedCategory.singleFunctor (Sheaves Y) 0).map v) ≫
    e.app ((inverseImage g).obj F) =
      e.app ((inverseImage f).obj F) ≫ S.map ((inverseImage k).map v) at hn
  let t := c.hom.app V ≫ D.map (pointDerivedIso g hx).hom ≫ e.app ((inverseImage g).obj F)
  have ht : t = (pointDerivedIso (k ≫ g) hx).hom ≫
      S.map ((inverseImageComposition k g).hom.app F) := pointDerivedIso_composition k g hx
  apply (cancel_mono t).mp
  calc
    _ = (derivedInverseImageComposition k f).hom.app V ≫ D.map (pointDerivedIso f hx).hom ≫
          D.map ((DerivedCategory.singleFunctor (Sheaves Y) 0).map v) ≫
          e.app ((inverseImage g).obj F) := by
      simp only [t, c, V, D, pullbackMorphism, liftPointArrow, eqToHom_refl, Category.id_comp,
        Category.comp_id, Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
      have hh : D.map (pointDerivedIso g hx).inv ≫ D.map (pointDerivedIso g hx).hom ≫
          e.app ((inverseImage g).obj F) = e.app ((inverseImage g).obj F) :=
        (D.mapIso (pointDerivedIso g hx)).inv_hom_id_assoc _
      rw [hh]
    _ = (pointDerivedIso (k ≫ f) hx).hom ≫ S.map ((inverseImageComposition k f).hom.app F) ≫
          S.map ((inverseImage k).map v) := by
      rw [hn]
      have hf := pointDerivedIso_composition k f hx
      simpa only [Category.assoc] using
        congrArg (fun u => u ≫ S.map ((inverseImage k).map v)) hf
    _ = _ := by
      rw [ht]
      simp only [liftPointArrow, ordinaryPullbackArrow, Category.assoc, Iso.inv_hom_id_assoc,
        Functor.map_comp]
      have hh : S.map ((inverseImageComposition k g).inv.app F) ≫
          S.map ((inverseImageComposition k g).hom.app F) = 𝟙 _ :=
        (S.mapIso ((inverseImageComposition k g).app F)).inv_hom_id
      rw [hh]
      exact congrArg (fun m => (pointDerivedIso (k ≫ f) hx).hom ≫
        S.map ((inverseImageComposition k f).hom.app F) ≫ m)
        (Category.comp_id (S.map ((inverseImage k).map v))).symm

/-- The derived comparison comes from the morphism that is the identity after
identifying the stalks of the two ordinary pullbacks with the point stalk. -/
private def PreservesDerivedPointStalks {Y : TopCat.{0}} {f g : Y ⟶ surface} {x : surface}
    (hx : IsClosed ({x} : Set surface))
    (v : (derivedInverseImage f).obj (pointSkyscraper x hx) ⟶
      (derivedInverseImage g).obj (pointSkyscraper x hx)) : Prop :=
  ∃ w, PreservesPointStalks (x := x) w ∧ liftPointArrow hx w = v

private theorem derivedPointArrow_unique {Y : TopCat.{0}} {f g : Y ⟶ surface} {x : surface}
    (hx : IsClosed ({x} : Set surface)) (hs : ∀ y : Y, f y = x → g y = x)
    {v w : (derivedInverseImage f).obj (pointSkyscraper x hx) ⟶
      (derivedInverseImage g).obj (pointSkyscraper x hx)}
    (hv : PreservesDerivedPointStalks hx v) (hw : PreservesDerivedPointStalks hx w) :
    v = w := by
  obtain ⟨v, hv, rfl⟩ := hv
  obtain ⟨w, hw, rfl⟩ := hw
  rw [pointArrow_unique hx hs hv hw]

private theorem derivedPointArrow_id {Y : TopCat.{0}} (f : Y ⟶ surface) {x : surface}
    (hx : IsClosed ({x} : Set surface)) :
    PreservesDerivedPointStalks hx (𝟙 ((derivedInverseImage f).obj (pointSkyscraper x hx))) :=
  ⟨𝟙 _, pointArrow_id f x, liftPointArrow_id f hx⟩

private theorem derivedPointArrow_comp {Y : TopCat.{0}} {f g j : Y ⟶ surface} {x : surface}
    (hx : IsClosed ({x} : Set surface)) (hs : ∀ y : Y, f y = x → g y = x)
    {v : (derivedInverseImage f).obj (pointSkyscraper x hx) ⟶
        (derivedInverseImage g).obj (pointSkyscraper x hx)}
    {w : (derivedInverseImage g).obj (pointSkyscraper x hx) ⟶
        (derivedInverseImage j).obj (pointSkyscraper x hx)}
    (hv : PreservesDerivedPointStalks hx v) (hw : PreservesDerivedPointStalks hx w) :
    PreservesDerivedPointStalks hx (v ≫ w) := by
  obtain ⟨v, hv, rfl⟩ := hv
  obtain ⟨w, hw, rfl⟩ := hw
  exact ⟨v ≫ w, pointArrow_comp hs hv hw, liftPointArrow_comp hx v w⟩

private theorem derivedPointArrow_pullback {W Y : TopCat.{0}} (k : W ⟶ Y)
    {f g : Y ⟶ surface} {f' g' : W ⟶ surface} {x : surface}
    (hf : k ≫ f = f') (hg : k ≫ g = g') (hx : IsClosed ({x} : Set surface))
    {v : (derivedInverseImage f).obj (pointSkyscraper x hx) ⟶
      (derivedInverseImage g).obj (pointSkyscraper x hx)}
    (hv : PreservesDerivedPointStalks hx v) :
    PreservesDerivedPointStalks hx (pullbackMorphism k hf hg v) := by
  subst f' g'
  obtain ⟨v, hv, rfl⟩ := hv
  exact ⟨ordinaryPullbackArrow k v, pointArrow_pullback k hv, (liftPointArrow_pullback k hx v).symm⟩

private theorem action_eq_point {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {x : surface} (fixes : ∀ g : H.space, A.act (g, x) = x) (z : Parameters H surface) :
    A.act z = x ↔ z.2 = x := by
  rcases z with ⟨g, y⟩
  constructor
  · intro h
    have h' := congrArg (fun z => A.act (g⁻¹, z)) h
    change A.act (g⁻¹, A.act (g, y)) = A.act (g⁻¹, x) at h'
    rwa [← A.mul_act, inv_mul_cancel, A.one_act, fixes] at h'
  · intro h
    change y = x at h
    subst y
    exact fixes g

private theorem action_preimage_point {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {x : surface} (fixes : ∀ g : H.space, A.act (g, x) = x) :
    productPoint H x = A.act ⁻¹' ({x} : Set surface) := by
  ext z
  exact (action_eq_point fixes z).symm

private theorem pointArrow_from_comparison {Y : TopCat.{0}} {f g : Y ⟶ surface}
    {W : Set Y} {x : surface} (hx : IsClosed ({x} : Set surface))
    (hf : W = f ⁻¹' ({x} : Set surface)) (hg : W = g ⁻¹' ({x} : Set surface))
    (a : closedInclusion W ≫ f = toPoint W x ≫ closedInclusion ({x} : Set surface))
    (b : closedInclusion W ≫ g = toPoint W x ≫ closedInclusion ({x} : Set surface))
    {v : (derivedInverseImage f).obj (pointSkyscraper x hx) ⟶
      (derivedInverseImage g).obj (pointSkyscraper x hx)}
    (hv : v ≫ derivedPointPullback hx b = derivedPointPullback hx a) :
    PreservesDerivedPointStalks hx v := by
  have hb := (closedPointPullback hx hg b).1
  have hdb := (closedPointPullback hx hg b).2
  let w := ordinaryPointPullback a ≫ inv (ordinaryPointPullback b)
  have hw : w ≫ ordinaryPointPullback b = ordinaryPointPullback a := by simp [w]
  refine ⟨w, ?_, ?_⟩
  · intro y hfy hgy
    have hy : y ∈ W := hf.symm ▸ (show y ∈ f ⁻¹' ({x} : Set surface) from hfy)
    let z : TopCat.of W := ⟨y, hy⟩
    let s := TopCat.Presheaf.stalkPushforward Coeff (closedInclusion W)
      (rational (TopCat.of W)).obj z
    have : IsIso s := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      Coeff IsInducing.subtypeVal (rational (TopCat.of W)).obj z
    apply (cancel_mono ((stalk y).map (ordinaryPointPullback b) ≫ s)).mp
    have h := (ordinaryPointPullback_stalk a z hfy).trans (ordinaryPointPullback_stalk b z hgy).symm
    simp only [Category.assoc, ← Functor.map_comp_assoc, hw]
    exact h
  · apply (cancel_mono (derivedPointPullback hx b)).mp
    rw [hv]
    have hf' : derivedPointPullback hx a = (pointDerivedIso f hx).hom ≫
        (DerivedCategory.singleFunctor (Sheaves Y) 0).map (ordinaryPointPullback a) := by
      simp [derivedPointPullback, pointDerivedIso]
    have hg' : derivedPointPullback hx b = (pointDerivedIso g hx).hom ≫
        (DerivedCategory.singleFunctor (Sheaves Y) 0).map (ordinaryPointPullback b) := by
      simp [derivedPointPullback, pointDerivedIso]
    rw [hf', hg']
    simp [liftPointArrow, ← Functor.map_comp, hw]

theorem trivialPointCoefficients : Expected.TrivialPointCoefficients := by
  intro H A x hx fixes
  let p := projection H surface
  let a := actionPointSquare fixes
  let b := projectionPointSquare H x
  have ha := (closedPointPullback hx (action_preimage_point fixes) a).2
  have hb := (closedPointPullback hx rfl b).2
  let e := asIso (derivedPointPullback hx a) ≪≫ (asIso (derivedPointPullback hx b)).symm
  have he : e.hom ≫ derivedPointPullback hx b = derivedPointPullback hx a := by simp [e]
  have hst := pointArrow_from_comparison hx (action_preimage_point fixes) rfl a b he
  let m := multiplyParameters H surface
  let q := secondParameter H surface
  let j := closedInclusion (X := Parameters H surface) (productPoint H x)
  let s := identitySection H surface
  have hi : pullbackMorphism s (identity_act A) identity_projection e.hom = 𝟙 _ := by
    apply derivedPointArrow_unique hx (fun _ h => h)
    · exact derivedPointArrow_pullback s (identity_act A) identity_projection hx hst
    · exact derivedPointArrow_id _ hx
  have hm : pullbackMorphism m rfl rfl e.hom =
      pullbackMorphism (firstAfterSecond A) (multiply_act A) (first_projection A) e.hom ≫
        pullbackMorphism q rfl multiply_projection e.hom := by
    have hs : ∀ z : TwoParameters H surface, (m ≫ A.act) z = x → (m ≫ p) z = x :=
      fun z h => (action_eq_point fixes (m z)).mp h
    have hq : ∀ z : TwoParameters H surface, (m ≫ A.act) z = x → (q ≫ A.act) z = x :=
      fun z h => (action_eq_point fixes (q z)).mpr (hs z h)
    apply derivedPointArrow_unique hx hs
    · exact derivedPointArrow_pullback m rfl rfl hx hst
    · exact derivedPointArrow_comp hx hq
        (derivedPointArrow_pullback (firstAfterSecond A) (multiply_act A) (first_projection A) hx hst)
        (derivedPointArrow_pullback q rfl multiply_projection hx hst)
  have hj : pullbackMorphism j (a.trans b.symm) rfl e.hom = 𝟙 _ := by
    apply derivedPointArrow_unique hx (fun _ h => h)
    · exact derivedPointArrow_pullback j (a.trans b.symm) rfl hx hst
    · exact derivedPointArrow_id _ hx
  exact ⟨⟨e, hi, hm⟩, he, hj⟩

private theorem trivialPoint_stalks {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {x : surface} {hx : IsClosed ({x} : Set surface)}
    (fixes : ∀ g : H.space, A.act (g, x) = x)
    {α : A.Equivariance (pointSkyscraper x hx)} (hα : TrivialPointEquivariance fixes α) :
    PreservesDerivedPointStalks hx α.iso.hom :=
  pointArrow_from_comparison hx (action_preimage_point fixes) rfl
    (actionPointSquare fixes) (projectionPointSquare H x) hα.1

theorem pointCoefficientFunctoriality : Expected.PointCoefficientFunctoriality := by
  intro K H B A x hx fixesA fixesB φ hφ h α β hα hβ
  apply derivedPointArrow_unique hx (fun z hz => (action_eq_point fixesB z).mp hz)
  · exact derivedPointArrow_pullback (groupParameterMap φ hφ) h
      (groupParameterProjection φ hφ) hx (trivialPoint_stalks fixesA hα)
  · exact trivialPoint_stalks fixesB hβ

section ConnectedCoefficients

open LatticeModelSpecs
open private jetMatrixHomeomorph jetUnitOpen jetMatrixUnit unitOfJetMatrix unitOfJetMatrix_val
  constantMatrix jetConstant_eq from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepLocalCohomology

/-- In coefficient coordinates a complex affine line between two invertible
jets misses the noninvertible locus away from finitely many parameters. -/
private theorem jetUnitOpen_pathConnected : IsPathConnected jetUnitOpen := by
  rw [isPathConnected_iff]
  refine ⟨⟨1, (jetMatrixUnit 1).mp isUnit_one⟩, ?_⟩
  intro u hu v hv
  let E := Fin 2 → Fin 2 → Fin 2 → ℂ
  let a : E := jetMatrixHomeomorph u
  let b : E := jetMatrixHomeomorph v
  let line (z : ℂ) : E := a + z • (b - a)
  let P (z : ℂ) := jetMatrixHomeomorph.symm (line z)
  have hP : Continuous P :=
    jetMatrixHomeomorph.symm.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : P 0 = u := by simp [P, line, a]
  have h1 : P 1 = v := by simp [P, line, b, add_sub_cancel]
  let c (i j : Fin 2) : Polynomial ℂ :=
    Polynomial.C (a i j 0) + Polynomial.X * Polynomial.C ((b - a) i j 0)
  let d := c 0 0 * c 1 1 - c 0 1 * c 1 0
  have hentry (z : ℂ) (i j : Fin 2) : (constantMatrix (P z)) i j = (line z) i j 0 := by
    unfold constantMatrix
    rw [Matrix.map_apply, jetConstant_eq]
    exact congrFun (congrFun (congrFun (jetMatrixHomeomorph.apply_symm_apply (line z)) i) j) 0
  have hline (z : ℂ) (i j : Fin 2) : (c i j).eval z = (line z) i j 0 := by
    simp only [c, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rfl
  have hdet (z : ℂ) : d.eval z = (constantMatrix (P z)).det := by
    rw [Matrix.det_fin_two, hentry, hentry, hentry, hentry]
    simp only [d, Polynomial.eval_sub, Polynomial.eval_mul, hline]
  have hu' : (constantMatrix u).det ≠ 0 := hu
  have hv' : (constantMatrix v).det ≠ 0 := hv
  have hd : d ≠ 0 := by
    intro h
    apply hu'
    rw [← h0, ← hdet, h, Polynomial.eval_zero]
  let S : Set ℂ := {z | d.IsRoot z}ᶜ
  have hS : IsPathConnected S :=
    (Polynomial.finite_setOfPred_isRoot hd).countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)
  have hS0 : (0 : ℂ) ∈ S := by simpa [S, Polynomial.IsRoot, hdet, h0] using hu'
  have hS1 : (1 : ℂ) ∈ S := by simpa [S, Polynomial.IsRoot, hdet, h1] using hv'
  have hsu : u ∈ P '' S := ⟨0, hS0, h0⟩
  have hsv : v ∈ P '' S := ⟨1, hS1, h1⟩
  have hsub : P '' S ⊆ jetUnitOpen := by
    rintro _ ⟨z, hz, rfl⟩
    change (constantMatrix (P z)).det ≠ 0
    change ¬ d.IsRoot z at hz
    rwa [← hdet]
  exact ((hS.image hP).joinedIn u hsu v hsv).mono hsub

private theorem jetGroup_connected (hH : IsTopologicalGroup Jets) :
    ConnectedSpace (jetGroup hH).space := by
  have : ConnectedSpace jetUnitOpen :=
    isConnected_iff_connectedSpace.mp jetUnitOpen_pathConnected.isConnected
  let f : jetUnitOpen → (jetGroup hH).space := unitOfJetMatrix
  have hc : Continuous f := by
    apply continuous_induced_rng.mpr
    change Continuous (fun a : jetUnitOpen => (unitOfJetMatrix a).val)
    simpa only [unitOfJetMatrix_val] using
      (continuous_subtype_val : Continuous (Subtype.val : jetUnitOpen → _))
  have hs : Function.Surjective f := by
    intro g
    refine ⟨⟨g.val, (jetMatrixUnit g.val).mp g.isUnit⟩, ?_⟩
    apply Units.ext
    exact unitOfJetMatrix_val _
  exact hs.connectedSpace hc

private def productPointHomeomorph (H : AnalyticGroup.{0}) (x : surface) :
    productPoint H x ≃ₜ H.space where
  toFun z := z.val.1
  invFun g := ⟨(g, x), rfl⟩
  left_inv z := Subtype.ext (Prod.ext rfl z.property.symm)
  right_inv _ := rfl
  continuous_toFun := continuous_fst.comp continuous_subtype_val
  continuous_invFun := (continuous_id.prodMk continuous_const).subtype_mk _

open private constantGermIso constantAdj_unit
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent

private def coefficientGerm (Z : TopCat.{0}) (z : Z) :
    scalars ⟶ (stalk z).obj (rational Z) :=
  constantSections Z (op ⊤) ≫ Γgerm (X := Z) (rational Z).obj z

private instance (Z : TopCat.{0}) (z : Z) : IsIso (coefficientGerm Z z) := by
  let P := (Functor.const (Opens Z)ᵒᵖ).obj (scalars : Coeff.{0})
  let η := (sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}).unit.app P
  have := constantGermIso z (scalars : Coeff.{0})
  have := stalkFunctor_map_unit_toSheafify_isIso z Coeff.{0} P
  have h : coefficientGerm Z z = Γgerm (X := Z) P z ≫ (stalkFunctor Coeff z).map η :=
    (stalkFunctor_map_germ ⊤ z trivial η).symm
  rw [h]
  infer_instance

private def sectionValue (Z : TopCat.{0}) (s : (rational Z).obj.obj (op ⊤)) (z : Z) :
    (scalars : Coeff.{0}) :=
  inv (coefficientGerm Z z) (Γgerm (X := Z) (rational Z).obj z s)

private theorem sectionValue_eq (Z : TopCat.{0}) (s : (rational Z).obj.obj (op ⊤)) (z : Z) :
    coefficientGerm Z z (sectionValue Z s z) = Γgerm (X := Z) (rational Z).obj z s := by
  change (inv (coefficientGerm Z z) ≫ coefficientGerm Z z) _ = _
  simp

private theorem sectionValue_locallyConstant (Z : TopCat.{0})
    (s : (rational Z).obj.obj (op ⊤)) : IsLocallyConstant (sectionValue Z s) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro z
  let c := sectionValue Z s z
  let t := constantSections Z (op ⊤) c
  let F := (rational Z).obj
  have e : Γgerm (X := Z) F z t = Γgerm (X := Z) F z s := sectionValue_eq Z s z
  obtain ⟨U, hz, i, j, hij⟩ := TopCat.Presheaf.germ_eq (X := Z) F z
    (U := ⊤) (V := ⊤) trivial trivial t s e
  have hj : j = i := Subsingleton.elim j i
  subst j
  refine ⟨U, U.isOpen, hz, ?_⟩
  intro w hw
  apply (ConcreteCategory.bijective_of_isIso (coefficientGerm Z w)).injective
  rw [sectionValue_eq]
  change Γgerm (X := Z) F w s = Γgerm (X := Z) F w t
  rw [← Γgerm_res_apply (X := Z) F (i := i) w hw s,
    ← Γgerm_res_apply (X := Z) F (i := i) w hw t, hij]

private theorem constantEnd_stalk_injective {Z : TopCat.{0}} [PreconnectedSpace Z] (z : Z)
    {v w : rational Z ⟶ rational Z}
    (h : (stalk z).map v = (stalk z).map w) : v = w := by
  apply ((constantAdj Z).homEquiv (scalars : Coeff.{0}) (rational Z)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, constantAdj_unit]
  apply ConcreteCategory.hom_ext
  intro c
  let s := (constantSections Z (op ⊤) ≫ v.hom.app (op ⊤)) c
  let t := (constantSections Z (op ⊤) ≫ w.hom.app (op ⊤)) c
  change s = t
  have hg : Γgerm (X := Z) (rational Z).obj z s = Γgerm (X := Z) (rational Z).obj z t := by
    dsimp only [s, t, ConcreteCategory.comp_apply]
    change germ (X := Z) (rational Z).obj ⊤ z trivial
        (v.hom.app (op ⊤) (constantSections Z (op ⊤) c)) =
      germ (X := Z) (rational Z).obj ⊤ z trivial
        (w.hom.app (op ⊤) (constantSections Z (op ⊤) c))
    rw [← stalkFunctor_map_germ_apply _ _ _ v.hom, ← stalkFunctor_map_germ_apply _ _ _ w.hom]
    exact congrArg (fun k : (stalk z).obj (rational Z) ⟶ (stalk z).obj (rational Z) =>
      k (coefficientGerm Z z c)) h
  have hz : sectionValue Z s z = sectionValue Z t z :=
    congrArg (fun t => inv (coefficientGerm Z z) t) hg
  apply TopCat.Presheaf.section_ext (rational Z)
  intro y _
  change Γgerm (X := Z) (rational Z).obj y s = Γgerm (X := Z) (rational Z).obj y t
  rw [← sectionValue_eq Z s y, ← sectionValue_eq Z t y,
    (sectionValue_locallyConstant Z s).apply_eq_of_preconnectedSpace y z,
    (sectionValue_locallyConstant Z t).apply_eq_of_preconnectedSpace y z, hz]

end ConnectedCoefficients

private theorem liftPointArrow_injective {Y : TopCat.{0}} {f g : Y ⟶ surface} {x : surface}
    (hx : IsClosed ({x} : Set surface))
    {v w : (inverseImage f).obj (pointSheaf x) ⟶ (inverseImage g).obj (pointSheaf x)}
    (h : liftPointArrow hx v = liftPointArrow hx w) : v = w := by
  apply (DerivedCategory.singleFunctor (Sheaves Y) 0).map_injective
  apply (cancel_epi (pointDerivedIso f hx).hom).mp
  apply (cancel_mono (pointDerivedIso g hx).inv).mp
  simpa only [liftPointArrow, Category.assoc] using h

private theorem liftPointArrow_surjective {Y : TopCat.{0}} {f g : Y ⟶ surface} {x : surface}
    (hx : IsClosed ({x} : Set surface)) :
    Function.Surjective (liftPointArrow (f := f) (g := g) hx) := by
  intro v
  let S := DerivedCategory.singleFunctor (Sheaves Y) 0
  let vf := (pointDerivedIso f hx).inv ≫ v ≫ (pointDerivedIso g hx).hom
  obtain ⟨w, hw⟩ := S.map_surjective vf
  exact ⟨w, by simp [liftPointArrow, show (DerivedCategory.singleFunctor (Sheaves Y) 0).map w = vf
    from hw, vf]⟩

private theorem stalk_eq_of_ordinaryPullbacks_eq {W Y X : TopCat.{0}} (k : W ⟶ Y)
    {f g : Y ⟶ X} {F : Sheaves X}
    {v w : (inverseImage f).obj F ⟶ (inverseImage g).obj F}
    (h : ordinaryPullbackArrow k v = ordinaryPullbackArrow k w) (z : W) :
    (stalk (k z)).map v = (stalk (k z)).map w := by
  have h' : (inverseImage k).map v = (inverseImage k).map w := by
    apply (cancel_epi ((inverseImageComposition k f).hom.app F)).mp
    apply (cancel_mono ((inverseImageComposition k g).inv.app F)).mp
    simpa only [ordinaryPullbackArrow, Category.assoc] using h
  apply (cancel_mono (inverseImageStalkMap k ((inverseImage g).obj F) z)).mp
  rw [← stalkInverse_naturality, ← stalkInverse_naturality, h']

private theorem closedConstantEnd_stalk_injective {Y : TopCat.{0}} {W : Set Y}
    [PreconnectedSpace W] (z : TopCat.of W)
    {v w : (directImage (closedInclusion W)).obj (rational (TopCat.of W)) ⟶
        (directImage (closedInclusion W)).obj (rational (TopCat.of W))}
    (h : (stalk z.val).map v = (stalk z.val).map w) : v = w := by
  let j := closedInclusion W
  let Q := rational (TopCat.of W)
  let FF := closedDirectImageFullyFaithful W
  let v' := FF.preimage v
  let w' := FF.preimage w
  have hv : (directImage j).map v' = v := FF.map_preimage v
  have hw : (directImage j).map w' = w := FF.map_preimage w
  let c := TopCat.Presheaf.stalkPushforward Coeff j Q.obj z
  have : IsIso c := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    Coeff IsInducing.subtypeVal Q.obj z
  have hst : (stalk z).map v' = (stalk z).map w' := by
    apply (cancel_epi c).mp
    have hn (t : Q ⟶ Q) :
        (stalk (j z)).map ((directImage j).map t) ≫ c = c ≫ (stalk z).map t :=
      stalkPushforward_naturality j t.hom z
    rw [← hn v', ← hn w', hv, hw]
    exact congrArg (fun t => t ≫ c) h
  rw [← hv, ← hw, constantEnd_stalk_injective z hst]

private theorem pointArrow_eq_of_stalk_eq {Y : TopCat.{0}} {f g : Y ⟶ surface}
    {W : Set Y} [PreconnectedSpace W] {x : surface} (hx : IsClosed ({x} : Set surface))
    (hf : W = f ⁻¹' ({x} : Set surface)) (hg : W = g ⁻¹' ({x} : Set surface))
    (a : closedInclusion W ≫ f = toPoint W x ≫ closedInclusion ({x} : Set surface))
    (b : closedInclusion W ≫ g = toPoint W x ≫ closedInclusion ({x} : Set surface))
    (z : TopCat.of W)
    {v w : (inverseImage f).obj (pointSheaf x) ⟶ (inverseImage g).obj (pointSheaf x)}
    (h : (stalk z.val).map v = (stalk z.val).map w) : v = w := by
  have := (closedPointPullback hx hf a).1
  have := (closedPointPullback hx hg b).1
  apply (cancel_epi (inv (ordinaryPointPullback a))).mp
  apply (cancel_mono (ordinaryPointPullback b)).mp
  apply closedConstantEnd_stalk_injective z
  simp only [Functor.map_comp, h]

theorem twoJetPointUniqueness : Expected.TwoJetPointUniqueness := by
  intro hH A x hx _ fixes α _ e he
  let H := jetGroup hH
  have : ConnectedSpace H.space := jetGroup_connected hH
  have : ConnectedSpace (productPoint H x) :=
    (productPointHomeomorph H x).symm.surjective.connectedSpace
      (productPointHomeomorph H x).symm.continuous
  obtain ⟨v, hv⟩ := liftPointArrow_surjective hx e.hom
  obtain ⟨w, hw⟩ := liftPointArrow_surjective hx α.iso.hom
  let s := identitySection H surface
  have hp : pullbackMorphism s rfl rfl (liftPointArrow hx v) =
      pullbackMorphism s rfl rfl (liftPointArrow hx w) := by
    rw [hv, hw]
    let u := eqToHom (congrArg (fun f : surface ⟶ surface =>
      (derivedInverseImage f).obj (pointSkyscraper x hx)) (identity_act A).symm)
    let t := eqToHom (congrArg (fun f : surface ⟶ surface =>
      (derivedInverseImage f).obj (pointSkyscraper x hx)) (identity_projection (H := H)))
    apply (cancel_epi u).mp
    apply (cancel_mono t).mp
    simpa only [u, t, pullbackMorphism, eqToHom_refl, Category.id_comp, Category.comp_id,
      Category.assoc] using he.trans α.identity.symm
  rw [liftPointArrow_pullback, liftPointArrow_pullback] at hp
  have hp' := liftPointArrow_injective hx hp
  have hs := stalk_eq_of_ordinaryPullbacks_eq s hp' x
  have huv : v = w :=
    pointArrow_eq_of_stalk_eq (W := productPoint H x) hx (action_preimage_point fixes) rfl
      (actionPointSquare fixes) (projectionPointSquare H x) ⟨(1, x), rfl⟩ hs
  exact Iso.ext (hv.symm.trans ((congrArg (liftPointArrow hx) huv).trans hw))

private theorem pullback_conjugation {W Y X : TopCat.{0}} (k : W ⟶ Y)
    {f g : Y ⟶ X} {f' g' : W ⟶ X} (hf : k ≫ f = f') (hg : k ≫ g = g')
    {F G : Derived X} (c : F ≅ G)
    (v : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F) :
    pullbackMorphism k hf hg ((derivedInverseImage f).map c.inv ≫ v ≫
        (derivedInverseImage g).map c.hom) =
      (derivedInverseImage f').map c.inv ≫ pullbackMorphism k hf hg v ≫
        (derivedInverseImage g').map c.hom := by
  subst f' g'
  have h1 := (derivedInverseImageComposition k f).hom.naturality c.inv
  have h2 := (derivedInverseImageComposition k g).inv.naturality c.hom
  change (derivedInverseImage (k ≫ f)).map c.inv ≫ _ =
    _ ≫ (derivedInverseImage k).map ((derivedInverseImage f).map c.inv) at h1
  change (derivedInverseImage k).map ((derivedInverseImage g).map c.hom) ≫ _ =
    _ ≫ (derivedInverseImage (k ≫ g)).map c.hom at h2
  simp only [pullbackMorphism, eqToHom_refl, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc (f := (derivedInverseImageComposition k f).hom.app G), ← h1,
    Category.assoc, h2]

theorem normalizedConeComparison : Expected.NormalizedConeComparison := by
  intro hH A x hx hxscalar fixes α hα c e he
  apply twoJetPointUniqueness hH hxscalar fixes hα
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv,
    CategoryTheory.Functor.mapIso_hom]
  rw [pullback_conjugation, he]
  simp

end RepTheorySurvey.Geometric.ConvolutionPointCoefficients
