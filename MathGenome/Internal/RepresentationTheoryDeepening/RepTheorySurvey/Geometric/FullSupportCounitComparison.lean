import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FullSupportCounitComparison
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open CategoryTheory

universe w

namespace RepTheorySurvey.Geometric.FullSupportCounitComparison

open Analytic Analytic.IntersectionComplex
open Analytic.DerivedPullbackPasting.Expected (identityValue squareValue)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions)
open FullSupportCounitComparisonSpecs

open private adjointSquareMap_counit
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
open private comparison_transport_right_assoc square_hom transport transport_trans
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting

private theorem squareMateCounitHom {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {P : ObjectProperty C} {E : B ⥤ A} {V : D ⥤ P.FullSubcategory}
    {J : A ⥤ P.FullSubcategory} {K : B ⥤ D} {S : P.FullSubcategory ⥤ A} {R : D ⥤ B}
    (α : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R) (F : D) :
    (J.map (adjointSquareMap α a b F) ≫ a.counit.app (V.obj F)).hom =
      (α.hom.app (R.obj F)).hom ≫ (V.map (b.counit.app F)).hom :=
  congrArg (fun f : J.obj (E.obj (R.obj F)) ⟶ V.obj F => f.hom)
    (adjointSquareMap_counit α a b F)

private theorem directImageComparisonCounitHom {U V Y X : TopCat.{w}}
    {u : U ⟶ V} {i : Y ⟶ X} {t : V ⟶ X} {v : U ⟶ Y}
    (hs : u ≫ t = v ≫ i) (a : DerivedAdjunctions.{w}) (F : BoundedBelow Y) :
    ((boundedBelowInverseImage u).map (directImageComparison hs (a u) (a i) F) ≫
        (a u).counit.app ((boundedBelowInverseImage v).obj F)).hom =
      ((pullbackSquare hs).hom.app ((derivedDirectImage i).obj F)).hom ≫
        ((boundedBelowInverseImage v).map ((a i).counit.app F)).hom :=
  squareMateCounitHom (pullbackSquare hs) (a u) (a i) F

private theorem boundedBelowInverseImageMapHom {X Y : TopCat.{w}} (f : X ⟶ Y)
    {A B : BoundedBelow Y} (g : A ⟶ B) :
    ((boundedBelowInverseImage f).map g).hom = (derivedInverseImage f).map g.hom := rfl

private theorem squareCounitHom {U V Y X : TopCat.{w}}
    {u : U ⟶ V} {i : Y ⟶ X} {t : V ⟶ X} {v : U ⟶ Y}
    (hs : u ≫ t = v ≫ i) {E : BoundedBelow X} {F : BoundedBelow Y}
    (ε : (boundedBelowInverseImage i).obj E ⟶ F) :
    ((pullbackSquare hs).hom.app E).hom ≫ ((boundedBelowInverseImage v).map ε).hom =
      (squareValue hs).hom.app E.obj ≫ (derivedInverseImage v).map ε.hom :=
  congrArg₂ (fun p q => p ≫ q)
    (DerivedPullbackPasting.squareBoundedBelowCompatibility hs E)
    (boundedBelowInverseImageMapHom v ε)

private theorem directImageComparisonCounit {U V Y X : TopCat.{w}}
    {u : U ⟶ V} {i : Y ⟶ X} {t : V ⟶ X} {v : U ⟶ Y}
    (hs : u ≫ t = v ≫ i) (a : DerivedAdjunctions.{w}) (F : BoundedBelow Y) :
    ((boundedBelowInverseImage u).map (directImageComparison hs (a u) (a i) F) ≫
        (a u).counit.app ((boundedBelowInverseImage v).obj F)).hom =
      (squareValue hs).hom.app ((derivedDirectImage i).obj F).obj ≫
        (derivedInverseImage v).map ((a i).counit.app F).hom :=
  (directImageComparisonCounitHom hs a F).trans
    (squareCounitHom hs (E := (derivedDirectImage i).obj F) (F := F) ((a i).counit.app F))

private theorem counitAfterMap {C D : Type*} [Category* C] [Category* D]
    {P : ObjectProperty D} {L : C ⥤ P.FullSubcategory} {R : P.FullSubcategory ⥤ C}
    (a : L ⊣ R) {A : C} {B B' : P.FullSubcategory} (c : A ⟶ R.obj B) (d : B ⟶ B') :
    (L.map (c ≫ R.map d)).hom ≫ (a.counit.app B').hom =
      (L.map c ≫ a.counit.app B).hom ≫ d.hom := by
  have h : L.map (c ≫ R.map d) ≫ a.counit.app B' = (L.map c ≫ a.counit.app B) ≫ d := by
    rw [Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact a.counit.naturality d
  exact congrArg (fun f : L.obj A ⟶ B' => f.hom) h

private theorem identitySquareComponent {X Y V : TopCat.{w}}
    {i : Y ⟶ X} {j : Y ⟶ V} {t : V ⟶ X} (h : j ≫ t = i) (E : Derived X) :
    (squareValue (h.trans (Category.id_comp i).symm)).hom.app E ≫
        (identityValue Y).hom.app ((derivedInverseImage i).obj E) =
      (derivedInverseImageComposition j t).inv.app E ≫ transport h E := by
  let hs := h.trans (Category.id_comp i).symm
  let p := (derivedInverseImageComposition j t).inv.app E
  let q := (derivedInverseImageComposition (𝟙 Y) i).hom.app E
  let e := (identityValue Y).hom.app ((derivedInverseImage i).obj E)
  calc
    _ = (p ≫ transport hs E ≫ q) ≫ e := congrArg (· ≫ e) (square_hom hs E)
    _ = p ≫ transport hs E ≫ q ≫ e := by simp only [Category.assoc]
    _ = p ≫ transport hs E ≫ transport (Category.id_comp i) E :=
      congrArg (fun f => p ≫ transport hs E ≫ f) (DerivedPullbackPasting.compositionLeftUnit i E)
    _ = _ := congrArg (p ≫ ·) (transport_trans hs (Category.id_comp i) E)

private theorem fullSupportCounitFactor {X Y V : TopCat.{w}}
    {i : Y ⟶ X} {j : Y ⟶ V} {t : V ⟶ X}
    (h : j ≫ t = i) (a : DerivedAdjunctions.{w}) (F : BoundedBelow Y) :
    (derivedInverseImage j).map (fullSupportComparison h a F).hom ≫ ((a j).counit.app F).hom =
      ((boundedBelowInverseImage j).map
        (directImageComparison (h.trans (Category.id_comp i).symm) (a j) (a i) F) ≫
        (a j).counit.app ((boundedBelowInverseImage (𝟙 Y)).obj F)).hom ≫
          (identityValue Y).hom.app F.obj :=
  counitAfterMap (a j)
    (directImageComparison (h.trans (Category.id_comp i).symm) (a j) (a i) F)
    (ObjectProperty.homMk ((identityValue Y).hom.app F.obj))

private theorem pasteIdentityCounit {C : Type*} [Category* C] {I : C ⥤ C}
    (δ : I ⟶ 𝟭 C) {A B B' : C} (ε : B ⟶ B')
    {c : A ⟶ B'} {m : A ⟶ I.obj B'} {s : A ⟶ I.obj B} {p : A ⟶ B}
    (hc : c = m ≫ δ.app B') (hm : m = s ≫ I.map ε) (hs : s ≫ δ.app B = p) :
    c = p ≫ ε := by
  rw [hc, hm, Category.assoc, δ.naturality]
  change s ≫ δ.app B ≫ ε = _
  rw [← Category.assoc, hs]

theorem fullSupportCounit : Expected.FullSupportCounit.{w} := by
  intro X Y V i j t h a F
  let E := (derivedDirectImage i).obj F
  let hs : j ≫ t = 𝟙 Y ≫ i := h.trans (Category.id_comp i).symm
  let ε := ((a i).counit.app F).hom
  exact (pasteIdentityCounit (identityValue Y).hom ε
    (fullSupportCounitFactor h a F) (directImageComparisonCounit hs a F)
    (identitySquareComponent h E.obj)).trans (Category.assoc _ _ _)

private theorem cancelCompositionIsos {C D : Type*} [Category* C] [Category* D]
    (P : C ⥤ D) {A A' M : D} {B B' : C} (l : A ≅ A') (r : B ≅ B')
    (f : A' ⟶ P.obj B') (g : A ⟶ M) (k : M ⟶ P.obj B)
    (h : l.hom ≫ f = g ≫ k ≫ P.map r.hom) :
    f ≫ P.map r.inv = l.inv ≫ g ≫ k := by
  apply (cancel_epi l.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, h]
  simp [Category.assoc, ← Functor.map_comp]

private theorem counitViaFactor {U Y V X : TopCat.{w}} {j : Y ⟶ V} {v : U ⟶ Y}
    {i : Y ⟶ X} {t : V ⟶ X} (h : j ≫ t = i) (hs : (v ≫ j) ≫ t = v ≫ i)
    {E : Derived X} {F : Derived Y} (ε : (derivedInverseImage i).obj E ⟶ F) :
    (derivedInverseImageComposition v j).hom.app ((derivedInverseImage t).obj E) ≫
        (derivedInverseImage v).map ((derivedInverseImageComposition j t).inv.app E ≫
          transport h E ≫ ε) =
      (squareValue hs).hom.app E ≫ (derivedInverseImage v).map ε := by
  have hComp : (derivedInverseImageComposition v j).hom.app ((derivedInverseImage t).obj E) ≫
      (derivedInverseImage v).map ((derivedInverseImageComposition j t).inv.app E) =
      (derivedInverseImageComposition (v ≫ j) t).inv.app E ≫
        transport (Category.assoc v j t) E ≫ (derivedInverseImageComposition v (j ≫ t)).hom.app E :=
    cancelCompositionIsos (derivedInverseImage v)
      ((derivedInverseImageComposition (v ≫ j) t).app E)
      ((derivedInverseImageComposition j t).app E)
      ((derivedInverseImageComposition v j).hom.app ((derivedInverseImage t).obj E))
      (transport (Category.assoc v j t) E) ((derivedInverseImageComposition v (j ≫ t)).hom.app E)
      (DerivedPullbackPasting.compositionAssociativity v j t E)
  simp only [Functor.map_comp, Category.assoc, square_hom]
  rw [reassoc_of% hComp, comparison_transport_right_assoc, eqToHom_trans_assoc]

private theorem pullCounitViaFactor {U Y V X : TopCat.{w}}
    {j : Y ⟶ V} {v : U ⟶ Y} {u : U ⟶ V} {i : Y ⟶ X} {t : V ⟶ X}
    (h : j ≫ t = i) (hFactor : v ≫ j = u) (hs : u ≫ t = v ≫ i)
    {E : Derived X} {F : Derived Y} (ε : (derivedInverseImage i).obj E ⟶ F)
    {c : (derivedInverseImage j).obj ((derivedInverseImage t).obj E) ⟶ F}
    (hc : c = (derivedInverseImageComposition j t).inv.app E ≫ transport h E ≫ ε) :
    transport hFactor.symm ((derivedInverseImage t).obj E) ≫
      (derivedInverseImageComposition v j).hom.app ((derivedInverseImage t).obj E) ≫
        (derivedInverseImage v).map c =
      (squareValue hs).hom.app E ≫ (derivedInverseImage v).map ε := by
  subst c
  subst u
  exact (Category.id_comp _).trans (counitViaFactor h hs ε)

theorem intersectionCounit : Expected.IntersectionCounit.{w} := by
  intro X Y U V i j t v u h hFactor hSquare a F
  exact ⟨pullCounitViaFactor h hFactor hSquare ((a i).counit.app F).hom (fullSupportCounit h a F),
    (directImageComparisonCounit hSquare a F).symm⟩

end RepTheorySurvey.Geometric.FullSupportCounitComparison
