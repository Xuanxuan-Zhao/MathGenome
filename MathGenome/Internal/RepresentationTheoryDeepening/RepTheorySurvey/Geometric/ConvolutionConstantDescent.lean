import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionConstantDescent

import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Filtered.Final

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace RepTheorySurvey.Geometric.ConvolutionConstantDescent

open Analytic ConvolutionConstantDescentSpec

abbrev constantPullback {Y X : TopCat.{u}} (m : Y ⟶ X) :
    (inverseImage m).obj (rational X) ≅ rational Y :=
  ConvolutionConstantDescentSpec.constantPullback m

abbrev shiftedConstantPullback {Y X : TopCat.{u}} (m : Y ⟶ X) (d : ℕ) :
    (derivedInverseImage m).obj (IntersectionComplex.shiftedConstant X d).obj ≅
      (IntersectionComplex.shiftedConstant Y d).obj :=
  ConvolutionConstantDescentSpec.shiftedConstantPullback m d

abbrev tensorPresheaf {Z : TopCat.{0}} (F G : Sheaves Z) : Z.Presheaf Coeff.{0} :=
  ConvolutionConstantDescentSpec.tensorPresheaf F G

abbrev coefficientTensor : CoefficientTensorType :=
  ConvolutionConstantDescentSpec.coefficientTensor

section CoefficientTensor

open TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false

private theorem constantSections_restrict {Z : TopCat.{0}} {U V : (Opens Z)ᵒᵖ} (i : U ⟶ V) :
    constantSections Z U ≫ (rational Z).obj.map i = constantSections Z V := by
  have h := (((sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}).unit.app
    ((Functor.const (Opens Z)ᵒᵖ).obj scalars)).naturality i).symm
  change constantSections Z U ≫ (rational Z).obj.map i = (𝟙 _) ≫ constantSections Z V at h
  simpa only [Category.id_comp] using h

/-- The map from constant tensor coefficients into the tensor of the section presheaves. -/
private def tensorOfConstants {Z X Y : TopCat.{0}} (a : Z ⟶ X) (b : Z ⟶ Y) :
    (Functor.const (Opens Z)ᵒᵖ).obj (scalars ⊗ scalars) ⟶
      tensorPresheaf ((inverseImage a).obj (rational X)) ((inverseImage b).obj (rational Y)) where
  app U := (constantSections Z U ≫ (constantPullback a).inv.hom.app U) ⊗ₘ
    (constantSections Z U ≫ (constantPullback b).inv.hom.app U)
  naturality U V i := by
    have h (T : TopCat.{0}) (f : Z ⟶ T) :
        (constantSections Z U ≫ (constantPullback f).inv.hom.app U) ≫
          ((inverseImage f).obj (rational T)).obj.map i =
        constantSections Z V ≫ (constantPullback f).inv.hom.app V := by
      rw [Category.assoc, ← (constantPullback f).inv.hom.naturality i, ← Category.assoc]
      rw [constantSections_restrict i]
    change 𝟙 _ ≫ _ = _ ≫ (_ ⊗ₘ _)
    rw [Category.id_comp]
    symm
    refine Eq.trans (tensorHom_comp_tensorHom _ _ _ _) ?_
    erw [h X a, h Y b]

private theorem constantGermIso {Z : TopCat.{0}} (x : Z) (V : Coeff.{0}) :
    IsIso (Γgerm (X := Z) ((Functor.const (Opens Z)ᵒᵖ).obj V) x) := by
  let : IsConnected (OpenNhds x)ᵒᵖ := IsFiltered.isConnected _
  let c := (Functor.const (OpenNhds x)ᵒᵖ).obj V
  let e := (isColimitConstCocone (OpenNhds x)ᵒᵖ V).coconePointUniqueUpToIso
    (colimit.isColimit c)
  have h : e.hom = Γgerm (X := Z) ((Functor.const (Opens Z)ᵒᵖ).obj V) x := by
    have he := IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitConstCocone (OpenNhds x)ᵒᵖ V) (colimit.isColimit c)
      (op (⟨⊤, trivial⟩ : OpenNhds x))
    change 𝟙 V ≫ e.hom = Γgerm (X := Z) ((Functor.const (Opens Z)ᵒᵖ).obj V) x at he
    rw [Category.id_comp] at he
    exact he
  rw [← h]
  infer_instance

private theorem sectionGermIso {Z X : TopCat.{0}} (a : Z ⟶ X) (x : Z) :
    IsIso ((constantSections Z (op ⊤) ≫ (constantPullback a).inv.hom.app (op ⊤)) ≫
      Γgerm (X := Z) ((inverseImage a).obj (rational X)).obj x) := by
  let P := (Functor.const (Opens Z)ᵒᵖ).obj (scalars : Coeff.{0})
  let η := (sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}).unit.app P
  let f := (constantPullback a).inv.hom
  have : IsIso (Γgerm (X := Z) P x) := constantGermIso x _
  have : IsIso ((stalkFunctor Coeff.{0} x).map η) :=
    stalkFunctor_map_unit_toSheafify_isIso x _ P
  have : IsIso f := (TopCat.Sheaf.forget _ Z).map_isIso (constantPullback a).inv
  have h := stalkFunctor_map_germ ⊤ x trivial (η ≫ f)
  change Γgerm (X := Z) P x ≫ (stalkFunctor Coeff.{0} x).map (η ≫ f) =
    (η.app (op ⊤) ≫ f.app (op ⊤)) ≫
      Γgerm (X := Z) ((inverseImage a).obj (rational X)).obj x at h
  change IsIso ((η.app (op ⊤) ≫ f.app (op ⊤)) ≫ _)
  rw [← h, Functor.map_comp]
  infer_instance

/-- The neighborhood index is filtered, so the tensor of the two colimit cocones
again computes a colimit over the same index. -/
private def tensorStalkIso {Z : TopCat.{0}} (F G : Sheaves Z) (x : Z) :
    (tensorPresheaf F G).stalk x ≅ TopCat.Presheaf.stalk (X := Z) F.obj x ⊗ TopCat.Presheaf.stalk (X := Z) G.obj x := by
  let J := (OpenNhds x)ᵒᵖ
  let F' : J ⥤ Coeff.{0} := (OpenNhds.inclusion x).op ⋙ F.obj
  let G' : J ⥤ Coeff.{0} := (OpenNhds.inclusion x).op ⋙ G.obj
  letI : IsSifted J := IsFiltered.isSifted
  letI (M : Coeff.{0}) : PreservesColimits (tensorLeft M) := inferInstance
  letI (M : Coeff.{0}) : PreservesColimits (tensorRight M) := inferInstance
  let c : Cocone ((OpenNhds.inclusion x).op ⋙ tensorPresheaf F G) :=
    (colimit.cocone F').tensor (colimit.cocone G')
  have hc : IsColimit c := (colimit.isColimit F').tensor (colimit.isColimit G')
  exact (colimit.isColimit _).coconePointUniqueUpToIso hc

private theorem germ_tensorStalkIso {Z : TopCat.{0}} (F G : Sheaves Z) (x : Z) :
    Γgerm (X := Z) (tensorPresheaf F G) x ≫ (tensorStalkIso F G x).hom =
      Γgerm (X := Z) F.obj x ⊗ₘ Γgerm (X := Z) G.obj x := by
  unfold tensorStalkIso
  apply IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (op (⟨⊤, trivial⟩ : OpenNhds x))

private theorem tensorOfConstants_stalkIso {Z X Y : TopCat.{0}} (a : Z ⟶ X) (b : Z ⟶ Y)
    (x : Z) : IsIso ((stalkFunctor Coeff.{0} x).map (tensorOfConstants a b)) := by
  let f := tensorOfConstants a b
  let P := (Functor.const (Opens Z)ᵒᵖ).obj ((scalars : Coeff.{0}) ⊗ scalars)
  let F := (inverseImage a).obj (rational X)
  let G := (inverseImage b).obj (rational Y)
  let e := tensorStalkIso F G x
  have : IsIso (Γgerm (X := Z) P x) := constantGermIso x _
  have h := stalkFunctor_map_germ ⊤ x trivial f
  change Γgerm (X := Z) P x ≫ (stalkFunctor Coeff.{0} x).map f =
    f.app (op ⊤) ≫ Γgerm (X := Z) (tensorPresheaf F G) x at h
  have h' := calc
    (Γgerm (X := Z) P x ≫ (stalkFunctor Coeff.{0} x).map f) ≫ e.hom =
        f.app (op ⊤) ≫ (Γgerm (X := Z) (tensorPresheaf F G) x ≫ e.hom) := by
      rw [h, Category.assoc]
    _ = f.app (op ⊤) ≫ (Γgerm (X := Z) F.obj x ⊗ₘ Γgerm (X := Z) G.obj x) := by
      rw [germ_tensorStalkIso]
  have : IsIso ((Γgerm (X := Z) P x ≫ (stalkFunctor Coeff.{0} x).map f) ≫ e.hom) := by
    rw [h']
    change IsIso (((constantSections Z (op ⊤) ≫ (constantPullback a).inv.hom.app _) ⊗ₘ
      (constantSections Z (op ⊤) ≫ (constantPullback b).inv.hom.app _)) ≫
        (Γgerm (X := Z) F.obj x ⊗ₘ Γgerm (X := Z) G.obj x))
    rw [tensorHom_comp_tensorHom
      (constantSections Z (op ⊤) ≫ (constantPullback a).inv.hom.app _)
      (constantSections Z (op ⊤) ≫ (constantPullback b).inv.hom.app _)
      (Γgerm (X := Z) F.obj x) (Γgerm (X := Z) G.obj x)]
    have := sectionGermIso a x
    have := sectionGermIso b x
    infer_instance
  have := IsIso.of_isIso_comp_right
    (Γgerm (X := Z) P x ≫ (stalkFunctor Coeff.{0} x).map f) e.hom
  exact IsIso.of_isIso_comp_left (Γgerm (X := Z) P x) _

private theorem sheafifiedTensorOfConstants_isIso {Z X Y : TopCat.{0}} (a : Z ⟶ X) (b : Z ⟶ Y) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology Z) Coeff.{0}).map (tensorOfConstants a b)) := by
  let J := Opens.grothendieckTopology Z
  let L := presheafToSheaf J Coeff.{0}
  let f := tensorOfConstants a b
  let η := (sheafificationAdjunction J Coeff.{0}).unit
  apply (isIso_iff_stalkFunctor_map_iso _).2
  intro x
  let S := stalkFunctor Coeff.{0} x
  let P := (Functor.const (Opens Z)ᵒᵖ).obj ((scalars : Coeff.{0}) ⊗ scalars)
  let T := tensorPresheaf ((inverseImage a).obj (rational X)) ((inverseImage b).obj (rational Y))
  have h := η.naturality f
  change f ≫ η.app T = η.app P ≫ (L.map f).hom at h
  have : IsIso (S.map (η.app P)) := stalkFunctor_map_unit_toSheafify_isIso x _ P
  have : IsIso (S.map (η.app T)) := stalkFunctor_map_unit_toSheafify_isIso x _ T
  have : IsIso (S.map f) := tensorOfConstants_stalkIso a b x
  suffices IsIso (S.map (η.app P) ≫ S.map ((L.map f).hom)) from
    IsIso.of_isIso_comp_left (S.map (η.app P)) _
  rw [← Functor.map_comp, ← h, Functor.map_comp]
  infer_instance

private theorem scalarProduct_isIso : IsIso scalarProduct := by
  let e := (ULift.moduleEquiv (R := ℚ) (M := ℚ)).toModuleIso
  have h : scalarProduct = (e.hom ▷ scalars) ≫ (λ_ (scalars : Coeff.{0})).hom := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change x * y = x.down • y
    rfl
  rw [h]
  infer_instance

theorem tensorMultiplication : Expected.TensorMultiplication := by
  intro Z X Y a b
  let J := Opens.grothendieckTopology Z
  let L := presheafToSheaf J Coeff.{0}
  let f := tensorOfConstants a b
  let η := (sheafificationAdjunction J Coeff.{0}).unit
  let g := (Functor.const (Opens Z)ᵒᵖ).map scalarProduct
  have : IsIso (L.map f) := sheafifiedTensorOfConstants_isIso a b
  have : IsIso scalarProduct := scalarProduct_isIso
  let μ := (asIso (L.map f)).symm ≪≫ asIso (L.map g)
  refine ⟨μ, ?_⟩
  intro U
  change f.app U ≫ (η.app _).app U ≫ μ.hom.hom.app U =
    g.app U ≫ (η.app _).app U
  have hf := NatTrans.congr_app (η.naturality f) U
  have hg := NatTrans.congr_app (η.naturality g) U
  change f.app U ≫ (η.app _).app U = (η.app _).app U ≫ (L.map f).hom.app U at hf
  change g.app U ≫ (η.app _).app U = (η.app _).app U ≫ (L.map g).hom.app U at hg
  rw [← Category.assoc, hf, hg, Category.assoc]
  congr 1
  change ((L.map f) ≫ μ.hom).hom.app U = (L.map g).hom.app U
  simp [μ]

end CoefficientTensor

section ConstantPullback

open LocalSheaf

set_option backward.isDefEq.respectTransparency false

private def comparedUnit {Y X : TopCat.{0}} (f : Y ⟶ X) :
    rational X ⟶ (directImage f).obj (rational Y) :=
  (inverseDirectAdjunction f).homEquiv _ _ (constantPullback f).hom

private theorem constantAdj_unit (X : TopCat.{0}) :
    (constantAdj X).unit.app (scalars : Coeff.{0}) = constantSections X (op ⊤) := by
  unfold constantAdj constantSheafAdj
  rw [Adjunction.comp_unit_app]
  change (𝟙 _) ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- The adjunction comparison is the map that restricts the same constant
coefficient to the inverse image of each open. -/
private theorem comparedUnit_sections {Y X : TopCat.{0}} (f : Y ⟶ X) (U : (Opens X)ᵒᵖ) :
    constantSections X U ≫ (comparedUnit f).hom.app U =
      constantSections Y ((Opens.map f).op.obj U) := by
  let v := comparedUnit f
  let i : op (⊤ : Opens X) ⟶ U := (homOfLE le_top : U.unop ⟶ ⊤).op
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((constantAdj X).comp (inverseDirectAdjunction f))
    ((constantAdj Y).ofNatIsoRight (directGlobalSections f).symm) (scalars : Coeff.{0})
  rw [Adjunction.comp_homEquiv] at h
  change (constantAdj X).homEquiv _ _ v =
    ((constantAdj Y).ofNatIsoRight (directGlobalSections f).symm).unit.app _ at h
  rw [Adjunction.homEquiv_unit] at h
  change (constantAdj X).unit.app scalars ≫ v.hom.app (op ⊤) =
    (constantAdj Y).unit.app scalars ≫ (directGlobalSections f).inv.app (rational Y) at h
  rw [constantAdj_unit, constantAdj_unit] at h
  let j : op (⊤ : Opens Y) ⟶ (Opens.map f).op.obj (op ⊤) :=
    eqToHom (congrArg op (Opens.map_top f).symm)
  have hj : (directGlobalSections f).inv.app (rational Y) = (rational Y).obj.map j := by
    change _ = (rational Y).obj.map (eqToIso (congrArg op (Opens.map_top f))).inv
    rfl
  rw [hj, constantSections_restrict j] at h
  have hv := v.hom.naturality i
  change (rational X).obj.map i ≫ v.hom.app U =
    v.hom.app (op ⊤) ≫ (rational Y).obj.map ((Opens.map f).op.map i) at hv
  calc
    _ = (constantSections X (op ⊤) ≫ (rational X).obj.map i) ≫ v.hom.app U := by
      rw [constantSections_restrict i]
    _ = (constantSections X (op ⊤) ≫ v.hom.app (op ⊤)) ≫
        (rational Y).obj.map ((Opens.map f).op.map i) := by rw [Category.assoc, hv, ← Category.assoc]
    _ = _ := by rw [h, constantSections_restrict]

private theorem comparedUnit_comp {W Y X : TopCat.{0}} (f : W ⟶ Y) (g : Y ⟶ X) :
    comparedUnit (f ≫ g) = comparedUnit g ≫ (directImage g).map (comparedUnit f) := by
  apply ((sheafificationAdjunction (Opens.grothendieckTopology X) Coeff.{0}).homEquiv
    ((Functor.const (Opens X)ᵒᵖ).obj scalars) ((directImage (f ≫ g)).obj (rational W))).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext U
  change constantSections X U ≫ (comparedUnit (f ≫ g)).hom.app U =
    constantSections X U ≫ ((comparedUnit g).hom.app U ≫
      (comparedUnit f).hom.app ((Opens.map g).op.obj U))
  rw [← Category.assoc, comparedUnit_sections, comparedUnit_sections, comparedUnit_sections]
  rfl

private theorem comparedUnit_id (X : TopCat.{0}) : comparedUnit (𝟙 X) = 𝟙 (rational X) := by
  apply ((sheafificationAdjunction (Opens.grothendieckTopology X) Coeff.{0}).homEquiv
    ((Functor.const (Opens X)ᵒᵖ).obj scalars) (rational X)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext U
  change constantSections X U ≫ (comparedUnit (𝟙 X)).hom.app U =
    constantSections X U ≫ 𝟙 _
  rw [comparedUnit_sections, Category.comp_id]
  rfl

private theorem constantPullback_comp {W Y X : TopCat.{0}} (f : W ⟶ Y) (g : Y ⟶ X) :
    (inverseImageComposition f g).hom.app (rational X) ≫
        (inverseImage f).map (constantPullback g).hom ≫ (constantPullback f).hom =
      (constantPullback (f ≫ g)).hom := by
  let A := inverseDirectAdjunction (f ≫ g)
  let B := (inverseDirectAdjunction g).comp (inverseDirectAdjunction f)
  let c := (inverseImage f).map (constantPullback g).hom ≫ (constantPullback f).hom
  apply (A.homEquiv _ _).injective
  change A.homEquiv _ _ ((A.leftAdjointUniq B).hom.app (rational X) ≫ c) = comparedUnit (f ≫ g)
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hc := Adjunction.homEquiv_unit B (f := c)
  change B.unit.app _ ≫ (directImage f ⋙ directImage g).map c = _
  erw [← hc, comparedUnit_comp]
  dsimp only [B]
  rw [Adjunction.comp_homEquiv]
  change (inverseDirectAdjunction g).homEquiv _ _
      ((inverseDirectAdjunction f).homEquiv _ _ c) = _
  dsimp only [c]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rfl

private theorem constantPullback_id (X : TopCat.{0}) :
    (constantPullback (𝟙 X)).hom = (inverseImageIdentity X).hom.app (rational X) := by
  let A := inverseDirectAdjunction (𝟙 X)
  apply (A.homEquiv _ _).injective
  change comparedUnit (𝟙 X) =
    A.homEquiv _ _ ((A.leftAdjointUniq (Adjunction.id (C := Sheaves X))).hom.app (rational X))
  rw [comparedUnit_id, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

end ConstantPullback

section DerivedPullback

open Functor

set_option backward.isDefEq.respectTransparency false

private abbrev degreeZero (X : TopCat.{0}) :=
  (DerivedCategory.singleFunctor (Sheaves X) 0).obj (rational X)

private def degreeZeroComparison {Y X : TopCat.{0}} (f : Y ⟶ X) :
    (derivedInverseImage f).obj (degreeZero X) ⟶ degreeZero Y :=
  ((inverseImage f).mapDerivedCategorySingleFunctor 0).hom.app (rational X) ≫
    (DerivedCategory.singleFunctor (Sheaves Y) 0).map (constantPullback f).hom

private theorem derivedComposition_hom {W Y X : TopCat.{0}} (f : W ⟶ Y) (g : Y ⟶ X) :
    (derivedInverseImageComposition f g).hom =
    (inverseImageComposition f g).hom.mapDerivedCategory ≫
      (mapDerivedCategoryCompIso (inverseImage g) (inverseImage f)).inv := rfl

private theorem derivedIdentity_hom (X : TopCat.{0}) :
    (derivedInverseImageIdentity X).hom =
      (inverseImageIdentity X).hom.mapDerivedCategory ≫ (mapDerivedCategoryIdIso (Sheaves X)).hom :=
  rfl

local instance {Y X : TopCat.{0}} (f : Y ⟶ X) : (derivedInverseImage f).CommShift ℤ :=
  inferInstanceAs ((inverseImage f).mapDerivedCategory.CommShift ℤ)

local instance {W Y X : TopCat.{0}} (f : W ⟶ Y) (g : Y ⟶ X) :
    NatTrans.CommShift (derivedInverseImageComposition f g).hom ℤ := by
  change NatTrans.CommShift ((inverseImageComposition f g).hom.mapDerivedCategory ≫
    (mapDerivedCategoryCompIso _ _).inv) ℤ
  infer_instance

local instance (X : TopCat.{0}) : NatTrans.CommShift (derivedInverseImageIdentity X).hom ℤ := by
  change NatTrans.CommShift ((inverseImageIdentity X).hom.mapDerivedCategory ≫
    (mapDerivedCategoryIdIso _).hom) ℤ
  infer_instance

/-- On a single complex the localization comparison comes from the
ordinary inverse-image comparison of sheaves. -/
private theorem derivedComposition_single {W Y X : TopCat.{0}} (f : W ⟶ Y) (g : Y ⟶ X)
    (V : Sheaves X) :
    let F := inverseImage g
    let G := inverseImage f
    let S := DerivedCategory.singleFunctor (Sheaves W) 0
    (derivedInverseImageComposition f g).hom.app
        ((DerivedCategory.singleFunctor (Sheaves X) 0).obj V) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app V) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj V) =
    (((inverseImage (f ≫ g)).mapDerivedCategorySingleFunctor 0).hom.app V) ≫
      S.map ((inverseImageComposition f g).hom.app V) := by
  dsimp only
  rw [derivedComposition_hom, NatTrans.comp_app, Category.assoc]
  rw [← mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app,
    Iso.inv_hom_id_app_assoc]
  rw [NatTrans.mapDerivedCategory_app_singleFunctor_obj]
  simp

private theorem degreeZeroComparison_comp {W Y X : TopCat.{0}} (f : W ⟶ Y) (g : Y ⟶ X) :
    (derivedInverseImageComposition f g).hom.app (degreeZero X) ≫
        (derivedInverseImage f).map (degreeZeroComparison g) ≫ degreeZeroComparison f =
      degreeZeroComparison (f ≫ g) := by
  let F := inverseImage g
  let G := inverseImage f
  let S := DerivedCategory.singleFunctor (Sheaves W) 0
  let v := (constantPullback g).hom
  let w := (constantPullback f).hom
  have hn := (G.mapDerivedCategorySingleFunctor 0).hom.naturality v
  change G.mapDerivedCategory.map ((DerivedCategory.singleFunctor (Sheaves Y) 0).map v) ≫
    (G.mapDerivedCategorySingleFunctor 0).hom.app (rational Y) =
    (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj (rational X)) ≫ S.map (G.map v) at hn
  unfold degreeZeroComparison
  change _ ≫ G.mapDerivedCategory.map (_ ≫ (DerivedCategory.singleFunctor (Sheaves Y) 0).map v) ≫
    (G.mapDerivedCategorySingleFunctor 0).hom.app _ ≫ S.map w = _
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (G.mapDerivedCategory.map ((DerivedCategory.singleFunctor (Sheaves Y) 0).map v)),
    hn, Category.assoc, ← Functor.map_comp]
  rw [← Category.assoc (G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app _)),
    ← Category.assoc (f := (derivedInverseImageComposition f g).hom.app _),
    derivedComposition_single f g]
  rw [Category.assoc, ← Functor.map_comp, constantPullback_comp f g]

private theorem degreeZeroComparison_id (X : TopCat.{0}) :
    degreeZeroComparison (𝟙 X) = (derivedInverseImageIdentity X).hom.app (degreeZero X) := by
  rw [derivedIdentity_hom, NatTrans.comp_app, NatTrans.mapDerivedCategory_app_singleFunctor_obj,
    mapDerivedCategoryIdIso_hom_app_singleFunctor_obj]
  unfold degreeZeroComparison
  rw [constantPullback_id]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  let v := (DerivedCategory.singleFunctor (Sheaves X) 0).map
    ((inverseImageIdentity X).hom.app (rational X))
  exact congrArg (fun t => ((inverseImage (𝟙 X)).mapDerivedCategorySingleFunctor 0).hom.app
    (rational X) ≫ t) (Category.comp_id v).symm

private theorem shiftedComparison_hom {Y X : TopCat.{0}} (f : Y ⟶ X) (d : ℕ) :
    (shiftedConstantPullback f d).hom =
      ((derivedInverseImage f).commShiftIso (d : ℤ)).hom.app (degreeZero X) ≫
      (shiftFunctor (Derived Y) (d : ℤ)).map (degreeZeroComparison f) := by
  rfl

theorem shiftedPullbackComposition : Expected.ShiftedPullbackComposition := by
  intro W Y X f g d
  let G := (inverseImage f).mapDerivedCategory
  let F := (inverseImage g).mapDerivedCategory
  let K := (derivedInverseImageComposition f g).hom
  let n : ℤ := d
  let SX := shiftFunctor (Derived X) n
  let SY := shiftFunctor (Derived Y) n
  let SW := shiftFunctor (Derived W) n
  let v := degreeZeroComparison g
  let w := degreeZeroComparison f
  rw [shiftedComparison_hom, shiftedComparison_hom, shiftedComparison_hom]
  change K.app (SX.obj (degreeZero X)) ≫
    G.map ((F.commShiftIso n).hom.app (degreeZero X) ≫ SY.map v) ≫
    (G.commShiftIso n).hom.app (degreeZero Y) ≫ SW.map w =
    _ ≫ SW.map (degreeZeroComparison (f ≫ g))
  have hn := (G.commShiftIso n).hom.naturality v
  change G.map (SY.map v) ≫ (G.commShiftIso n).hom.app (degreeZero Y) =
    (G.commShiftIso n).hom.app (F.obj (degreeZero X)) ≫ SW.map (G.map v) at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (G.map (SY.map v)), hn, Category.assoc, ← Functor.map_comp]
  have hcomp := Functor.commShiftIso_comp_hom_app F G n (degreeZero X)
  change ((F ⋙ G).commShiftIso n).hom.app (degreeZero X) =
    G.map ((F.commShiftIso n).hom.app (degreeZero X)) ≫
      (G.commShiftIso n).hom.app (F.obj (degreeZero X)) at hcomp
  rw [← Category.assoc (G.map ((F.commShiftIso n).hom.app (degreeZero X))), ← hcomp]
  have hk := NatTrans.shift_app_comm K n (degreeZero X)
  change ((derivedInverseImage (f ≫ g)).commShiftIso n).hom.app (degreeZero X) ≫
    SW.map (K.app (degreeZero X)) =
    K.app (SX.obj (degreeZero X)) ≫ ((F ⋙ G).commShiftIso n).hom.app (degreeZero X) at hk
  rw [← Category.assoc (K.app _), ← hk, Category.assoc, ← Functor.map_comp]
  exact congrArg (fun t => ((derivedInverseImage (f ≫ g)).commShiftIso n).hom.app
    (degreeZero X) ≫ SW.map t) (degreeZeroComparison_comp f g)

theorem shiftedPullbackIdentity : Expected.ShiftedPullbackIdentity := by
  intro X d
  apply Iso.ext
  change (shiftedConstantPullback (𝟙 X) d).hom =
    (derivedInverseImageIdentity X).hom.app _
  rw [shiftedComparison_hom, degreeZeroComparison_id]
  have h := NatTrans.shift_app_comm (derivedInverseImageIdentity X).hom (d : ℤ) (degreeZero X)
  simp only [Functor.commShiftIso_id_hom_app] at h
  exact h.trans (Category.comp_id _)

end DerivedPullback

section Equivariance

set_option backward.isDefEq.respectTransparency false

private theorem pullback_constantTransition {W Y X : TopCat.{0}}
    (k : W ⟶ Y) {f g : Y ⟶ X} {f' g' : W ⟶ X}
    (hf : k ≫ f = f') (hg : k ≫ g = g') (d : ℕ) :
    pullbackMorphism k hf hg
        ((shiftedConstantPullback f d) ≪≫ (shiftedConstantPullback g d).symm).hom =
      ((shiftedConstantPullback f' d) ≪≫ (shiftedConstantPullback g' d).symm).hom := by
  subst f' g'
  let R := (IntersectionComplex.shiftedConstant X d).obj
  let F := derivedInverseImage k
  let c (p : Y ⟶ X) :=
    (derivedInverseImageComposition k p).app R ≪≫ F.mapIso (shiftedConstantPullback p d)
  have hc (p : Y ⟶ X) :
      c p ≪≫ shiftedConstantPullback k d = shiftedConstantPullback (k ≫ p) d := by
    apply Iso.ext
    simpa only [c, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc, R, F] using
      shiftedPullbackComposition k p d
  have h : c f ≪≫ (c g).symm =
      shiftedConstantPullback (k ≫ f) d ≪≫ (shiftedConstantPullback (k ≫ g) d).symm := by
    rw [← hc f, ← hc g]
    apply Iso.ext
    simp
  have hh := congrArg Iso.hom h
  simpa only [pullbackMorphism, eqToHom_refl, Category.id_comp, Category.comp_id,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc, c, R, F] using hh

theorem normalizedEquivariance : Expected.NormalizedEquivariance := by
  intro H Z A d
  open AnalyticAction in
  refine ⟨{
    iso := shiftedConstantPullback A.act d ≪≫ (shiftedConstantPullback (projection H Z) d).symm
    identity := ?_
    multiplication := ?_ }, rfl⟩
  · rw [pullback_constantTransition]
    exact Iso.hom_inv_id _
  · rw [pullback_constantTransition, pullback_constantTransition, pullback_constantTransition]
    simp [Category.assoc]

end Equivariance

theorem shiftedDescent : Expected.ShiftedDescent := by
  intro Z X Y S a b q
  obtain ⟨μ, hμ⟩ := tensorMultiplication a b
  let μ₂ : shiftedTensor a b ≅ (IntersectionComplex.shiftedConstant Z 2).obj :=
    (shiftFunctor (Derived Z) (2 : ℤ)).mapIso
      ((DerivedCategory.singleFunctor (Sheaves Z) 0).mapIso μ)
  let e := shiftedConstantPullback q 2 ≪≫ μ₂.symm
  refine ⟨μ, e, hμ, ?_, ?_⟩
  · apply Iso.ext
    change (e ≪≫ μ₂).hom = _
    simp [e]
  · intro W k
    change _ ≫ (derivedInverseImage k).map (e.hom ≫ μ₂.hom) ≫ _ = _
    have h : e.hom ≫ μ₂.hom = (shiftedConstantPullback q 2).hom := by simp [e]
    rw [h]
    exact shiftedPullbackComposition k q 2

end RepTheorySurvey.Geometric.ConvolutionConstantDescent
