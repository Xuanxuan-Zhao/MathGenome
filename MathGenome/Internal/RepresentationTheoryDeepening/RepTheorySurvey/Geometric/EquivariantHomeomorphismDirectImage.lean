import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImage
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Adjunction.CompositionIso

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImage

open Analytic Analytic.IntersectionComplex EquivariantIntersectionComplexesSpecs
open EquivariantHomeomorphismDirectImageSpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)

open private pullbackEquivalence
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private def productIso (H : AnalyticGroup.{0}) {X Y : TopCat.{0}} (v : X ≅ Y) :
    AnalyticAction.Parameters H X ≅ AnalyticAction.Parameters H Y where
  hom := parameterInclusion H v.hom
  inv := parameterInclusion H v.inv
  hom_inv_id := TopCat.ext fun p => Prod.ext rfl (congrArg (fun f : X ⟶ X => f p.2) v.hom_inv_id)
  inv_hom_id := TopCat.ext fun p => Prod.ext rfl (congrArg (fun f : Y ⟶ Y => f p.2) v.inv_hom_id)

private theorem adjointSquareMap_isIso
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C} {L : A ⥤ C} {K : B ⥤ D} {S : C ⥤ A} {R : D ⥤ B}
    (s : E ⋙ L ≅ K ⋙ V) (a : L ⊣ S) (b : K ⊣ R) (F : D)
    [IsIso a.unit] [IsIso b.counit] : IsIso (adjointSquareMap s a b F) := by
  rw [adjointSquareMap, a.homEquiv_unit]
  infer_instance

private theorem precomp_adjointSquareMap
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C} {L : A ⥤ C} {K : B ⥤ D} {S : C ⥤ A} {R : D ⥤ B}
    (s : E ⋙ L ≅ K ⋙ V) (a : L ⊣ S) (b : K ⊣ R) {F : D} {G : B} (c : K.obj G ⟶ F) :
    (a.homEquiv _ _).symm (E.map (b.homEquiv _ _ c) ≫ adjointSquareMap s a b F) =
      s.hom.app G ≫ V.map c := by
  rw [a.homEquiv_naturality_left_symm]
  unfold adjointSquareMap
  rw [Equiv.symm_apply_apply]
  have hs := s.hom.naturality (b.homEquiv G F c)
  change L.map (E.map _) ≫ s.hom.app (R.obj F) = s.hom.app G ≫ V.map (K.map _) at hs
  rw [← Category.assoc, hs, Category.assoc, ← V.map_comp, ← b.homEquiv_counit,
    Equiv.symm_apply_apply]

private theorem adjointSquareIntertwines
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {E₁ E₂ : B ⥤ A} {V₁ V₂ : D ⥤ C} {L : A ⥤ C} {K : B ⥤ D}
    {S : C ⥤ A} {R : D ⥤ B}
    (s₁ : E₁ ⋙ L ≅ K ⋙ V₁) (s₂ : E₂ ⋙ L ≅ K ⋙ V₂) (a : L ⊣ S) (b : K ⊣ R)
    {F : D} {G : B} (c : K.obj G ⟶ F) (i : R.obj F ≅ G)
    (hi : i.inv = b.homEquiv G F c)
    (α : V₁.obj F ⟶ V₂.obj F) (β : E₁.obj G ⟶ E₂.obj G)
    (h : s₁.hom.app G ≫ V₁.map c ≫ α = L.map β ≫ s₂.hom.app G ≫ V₂.map c) :
    E₁.map i.hom ≫ β ≫ E₂.map i.inv ≫ adjointSquareMap s₂ a b F =
      adjointSquareMap s₁ a b F ≫ S.map α := by
  rw [← cancel_epi (E₁.map i.inv)]
  simp only [← E₁.map_comp_assoc, Iso.inv_hom_id, E₁.map_id, Category.id_comp]
  apply (a.homEquiv _ _).symm.injective
  rw [← Category.assoc (E₁.map i.inv), a.homEquiv_naturality_right_symm,
    hi, precomp_adjointSquareMap, a.homEquiv_naturality_left_symm, precomp_adjointSquareMap]
  simpa only [Category.assoc] using h.symm

section PullbackCoherence

open CategoryTheory.Functor
open ConvolutionConstantDescentSpec (derivedInverseImageIdentity)

private theorem inverseImage_assoc {W X Y Z : TopCat.{0}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Sheaves Z) :
    (inverseImageComposition f (g ≫ h)).hom.app F ≫
      (inverseImage f).map ((inverseImageComposition g h).hom.app F) =
    (inverseImageComposition (f ≫ g) h).hom.app F ≫
      (inverseImageComposition f g).hom.app ((inverseImage h).obj F) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (inverseDirectAdjunction h) (inverseDirectAdjunction g) (inverseDirectAdjunction f)
    (inverseDirectAdjunction (g ≫ h)) (inverseDirectAdjunction (f ≫ g))
    (inverseDirectAdjunction (f ≫ g ≫ h))
    (Iso.refl (directImage (g ≫ h))) (Iso.refl (directImage (f ≫ g)))
    (Iso.refl (directImage (f ≫ g ≫ h))) (Iso.refl (directImage (f ≫ g ≫ h))) (by
      ext : 1
      change (𝟙 _ ≫ 𝟙 _ : _ ⟶ _) = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
      simp only [Category.id_comp])
  have hh' := congrArg (fun e => e.inv.app F) hh
  change
    (inverseImageComposition (f ≫ g) h).hom.app F ≫
      (inverseImageComposition f g).hom.app ((inverseImage h).obj F) =
    ((inverseImageComposition f (g ≫ h)).hom.app F ≫
      (inverseImage f).map ((inverseImageComposition g h).hom.app F)) ≫ 𝟙 _ at hh'
  rw [Category.comp_id] at hh'
  exact hh'.symm

private theorem derivedCompositionAtLocalization {W X Y : TopCat.{0}}
    (f : W ⟶ X) (g : X ⟶ Y) (K : CochainComplex (Sheaves Y) ℤ) :
    (derivedInverseImageComposition f g).hom.app (DerivedCategory.Q.obj K) =
      (inverseImage (f ≫ g)).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map (((inverseImageComposition f g).hom.mapHomologicalComplex _).app K) ≫
      (inverseImage f).mapDerivedCategoryFactors.inv.app
        (((inverseImage g).mapHomologicalComplex _).obj K) ≫
      (derivedInverseImage f).map ((inverseImage g).mapDerivedCategoryFactors.inv.app K) := by
  let A := inverseImage f
  let B := inverseImage g
  change ((inverseImageComposition f g).hom.mapDerivedCategory ≫
    (mapDerivedCategoryCompIso B A).inv).app (DerivedCategory.Q.obj K) = _
  rw [← cancel_mono ((mapDerivedCategoryCompIso B A).hom.app (DerivedCategory.Q.obj K))]
  have hId : (NatIso.mapHomologicalComplex (Iso.refl (B ⋙ A)) (.up ℤ)).hom.app K = 𝟙 _ := by
    ext n
    rfl
  have eq₁ := mapDerivedCategoryCompIso_hom_app_Q_obj B A K
  rw [mapHomologicalComplexCompIso, hId] at eq₁
  erw [(DerivedCategory.Q (C := Sheaves W)).map_id _, Category.id_comp] at eq₁
  simp only [NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    NatTrans.mapDerivedCategory_app_Q_obj]
  rw [eq₁]
  change _ = _ ≫ _ ≫ A.mapDerivedCategoryFactors.inv.app _ ≫
    A.mapDerivedCategory.map (B.mapDerivedCategoryFactors.inv.app K) ≫
    A.mapDerivedCategory.map (B.mapDerivedCategoryFactors.hom.app K) ≫ _
  erw [← A.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app, A.mapDerivedCategory.map_id,
    Category.id_comp]
  exact congrArg (fun z => _ ≫ _ ≫ z)
    ((A.mapDerivedCategoryFactors.app ((B.mapHomologicalComplex (.up ℤ)).obj K)).inv_hom_id_assoc
      ((B ⋙ A).mapDerivedCategoryFactors.inv.app K)).symm

private theorem chain_inverseImage_assoc {W X Y Z : TopCat.{0}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (K : CochainComplex (Sheaves Z) ℤ) :
    ((inverseImageComposition f (g ≫ h)).hom.mapHomologicalComplex _).app K ≫
      ((inverseImage f).mapHomologicalComplex _).map
        (((inverseImageComposition g h).hom.mapHomologicalComplex _).app K) =
    ((inverseImageComposition (f ≫ g) h).hom.mapHomologicalComplex _).app K ≫
      ((inverseImageComposition f g).hom.mapHomologicalComplex _).app
        (((inverseImage h).mapHomologicalComplex _).obj K) := by
  ext n
  exact inverseImage_assoc f g h (K.X n)

private theorem derivedInverseImage_assoc {W X Y Z : TopCat.{0}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Derived Z) :
    (derivedInverseImageComposition f (g ≫ h)).hom.app F ≫
      (derivedInverseImage f).map ((derivedInverseImageComposition g h).hom.app F) =
    (derivedInverseImageComposition (f ≫ g) h).hom.app F ≫
      (derivedInverseImageComposition f g).hom.app ((derivedInverseImage h).obj F) := by
  let l := (derivedInverseImageComposition f (g ≫ h)).hom ≫
    whiskerRight (derivedInverseImageComposition g h).hom (derivedInverseImage f)
  let r := (derivedInverseImageComposition (f ≫ g) h).hom ≫
    whiskerLeft (derivedInverseImage h) (derivedInverseImageComposition f g).hom
  suffices l = r from NatTrans.congr_app this F
  refine Localization.natTrans_ext (DerivedCategory.Q (C := Sheaves Z))
    (HomologicalComplex.quasiIso (Sheaves Z) (.up ℤ)) (fun K => ?_)
  change (derivedInverseImageComposition f (g ≫ h)).hom.app (DerivedCategory.Q.obj K) ≫
      (derivedInverseImage f).map ((derivedInverseImageComposition g h).hom.app (DerivedCategory.Q.obj K)) =
    (derivedInverseImageComposition (f ≫ g) h).hom.app (DerivedCategory.Q.obj K) ≫
      (derivedInverseImageComposition f g).hom.app ((derivedInverseImage h).obj (DerivedCategory.Q.obj K))
  let K' := ((inverseImage h).mapHomologicalComplex (.up ℤ)).obj K
  have hNat := (derivedInverseImageComposition f g).hom.naturality
    ((inverseImage h).mapDerivedCategoryFactors.inv.app K)
  change (derivedInverseImage (f ≫ g)).map ((inverseImage h).mapDerivedCategoryFactors.inv.app K) ≫
    (derivedInverseImageComposition f g).hom.app ((derivedInverseImage h).obj (DerivedCategory.Q.obj K)) =
    (derivedInverseImageComposition f g).hom.app (DerivedCategory.Q.obj K') ≫
    (derivedInverseImage f).map ((derivedInverseImage g).map ((inverseImage h).mapDerivedCategoryFactors.inv.app K))
    at hNat
  rw [derivedCompositionAtLocalization f (g ≫ h), derivedCompositionAtLocalization g h,
    derivedCompositionAtLocalization (f ≫ g) h]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, hNat, derivedCompositionAtLocalization f g]
  erw [← (derivedInverseImage f).map_comp_assoc, Iso.inv_hom_id_app,
    (derivedInverseImage f).map_id, Category.id_comp]
  change _ = _ ≫ _ ≫ (inverseImage (f ≫ g)).mapDerivedCategoryFactors.inv.app K' ≫ _
  rw [Iso.inv_hom_id_app_assoc]
  let m := ((inverseImageComposition g h).hom.mapHomologicalComplex (.up ℤ)).app K
  let A := inverseImage f
  have hMove :
      A.mapDerivedCategoryFactors.inv.app _ ≫ A.mapDerivedCategory.map (DerivedCategory.Q.map m) =
        DerivedCategory.Q.map ((A.mapHomologicalComplex (.up ℤ)).map m) ≫
          A.mapDerivedCategoryFactors.inv.app _ := by
    apply (A.mapDerivedCategoryFactors.app _).inv_comp_eq.mpr
    rw [← Category.assoc]
    exact (A.mapDerivedCategoryFactors.app _).eq_comp_inv.mpr
      (A.mapDerivedCategoryFactors_hom_naturality m)
  change _ ≫ _ ≫ A.mapDerivedCategoryFactors.inv.app _ ≫
    A.mapDerivedCategory.map (DerivedCategory.Q.map m) ≫ _ = _
  rw [reassoc_of% hMove]
  erw [← (DerivedCategory.Q (C := Sheaves W)).map_comp_assoc,
    ← (DerivedCategory.Q (C := Sheaves W)).map_comp_assoc, chain_inverseImage_assoc]
  rfl

end PullbackCoherence

section EquivarianceTransport

open ConvolutionConstantDescentSpec (derivedInverseImageIdentity)

private abbrev InverseImageHom {X Y : TopCat.{0}}
    (F : Derived Y) (p q : X ⟶ Y) :=
  (derivedInverseImage p).obj F ⟶ (derivedInverseImage q).obj F

private def pullIso {U X Y : TopCat.{0}} {t : U ⟶ X} {p : X ⟶ Y} {p' : U ⟶ Y}
    (hp : t ≫ p = p') (F : Derived Y) :
    (derivedInverseImage p').obj F ≅ (derivedInverseImage t).obj ((derivedInverseImage p).obj F) :=
  eqToIso (congrArg (fun f => (derivedInverseImage f).obj F) hp.symm) ≪≫
    (derivedInverseImageComposition t p).app F

private theorem pullbackMorphism_eq {U X Y : TopCat.{0}} (t : U ⟶ X) {p q : X ⟶ Y}
    {p' q' : U ⟶ Y} (hp : t ≫ p = p') (hq : t ≫ q = q')
    {F : Derived Y} (m : InverseImageHom F p q) :
    pullbackMorphism t hp hq m = (pullIso hp F).hom ≫
      (derivedInverseImage t).map m ≫ (pullIso hq F).inv := by
  subst p' q'
  simp [pullbackMorphism, pullIso]

private theorem pullbackMorphism_id {U X Y : TopCat.{0}} (t : U ⟶ X) {p : X ⟶ Y}
    {p' : U ⟶ Y} (hp : t ≫ p = p') (F : Derived Y) :
    pullbackMorphism t hp hp (𝟙 ((derivedInverseImage p).obj F)) = 𝟙 _ := by
  rw [pullbackMorphism_eq]
  simp

private theorem pullbackMorphism_comp {U X Y : TopCat.{0}} (t : U ⟶ X)
    {p q r : X ⟶ Y} {p' q' r' : U ⟶ Y}
    (hp : t ≫ p = p') (hq : t ≫ q = q') (hr : t ≫ r = r')
    {F : Derived Y} (m : InverseImageHom F p q) (n : InverseImageHom F q r) :
    pullbackMorphism t hp hr (m ≫ n) =
      pullbackMorphism t hp hq m ≫ pullbackMorphism t hq hr n := by
  simp only [pullbackMorphism_eq, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

private theorem pullbackMorphism_injective {U X Y : TopCat.{0}} (t : U ⟶ X)
    [(derivedInverseImage t).Faithful] {p q : X ⟶ Y} {p' q' : U ⟶ Y}
    (hp : t ≫ p = p') (hq : t ≫ q = q') (F : Derived Y) :
    Function.Injective (fun m : InverseImageHom F p q => pullbackMorphism t hp hq m) := by
  intro m n h
  simp only [pullbackMorphism_eq, cancel_epi, cancel_mono] at h
  exact (derivedInverseImage t).map_injective h

private theorem pullbackMorphism_twice {T U X Y : TopCat.{0}} (s : T ⟶ U) (t : U ⟶ X)
    {p q : X ⟶ Y} {p' q' : U ⟶ Y} {p'' q'' : T ⟶ Y}
    (hp : t ≫ p = p') (hq : t ≫ q = q') (hp' : s ≫ p' = p'') (hq' : s ≫ q' = q'')
    {F : Derived Y} (m : InverseImageHom F p q) :
    pullbackMorphism s hp' hq' (pullbackMorphism t hp hq m) =
      pullbackMorphism (s ≫ t) (by rw [Category.assoc, hp, hp'])
        (by rw [Category.assoc, hq, hq']) m := by
  subst p' q' p'' q''
  let d := derivedInverseImageComposition s t
  let A := derivedInverseImage s
  let B := derivedInverseImage t
  let C := derivedInverseImage (s ≫ t)
  let a := (derivedInverseImageComposition (s ≫ t) p).app F
  let b := (derivedInverseImageComposition (s ≫ t) q).app F
  let p₂ := (derivedInverseImageComposition s (t ≫ p)).app F
  let q₂ := (derivedInverseImageComposition s (t ≫ q)).app F
  let p₁ := (derivedInverseImageComposition t p).app F
  let q₁ := (derivedInverseImageComposition t q).app F
  have hp : p₂.hom ≫ A.map p₁.hom = a.hom ≫ d.hom.app _ :=
    derivedInverseImage_assoc s t p F
  have hq : A.map q₁.inv ≫ q₂.inv = d.inv.app _ ≫ b.inv := by
    have hh : q₂ ≪≫ A.mapIso q₁ = b ≪≫ d.app _ :=
      Iso.ext (derivedInverseImage_assoc s t q F)
    exact congrArg Iso.inv hh
  have hm : d.hom.app _ ≫ A.map (B.map m) = C.map m ≫ d.hom.app _ :=
    (d.hom.naturality m).symm
  simp only [pullbackMorphism, eqToHom_refl, Category.id_comp, Category.comp_id]
  change p₂.hom ≫ A.map (p₁.hom ≫ B.map m ≫ q₁.inv) ≫ q₂.inv =
    a.hom ≫ C.map m ≫ b.inv
  simp only [Functor.map_comp, Category.assoc, reassoc_of% hp, reassoc_of% hm,
    hq, Iso.hom_inv_id_app_assoc]

private def postcompHom {U X Y : TopCat.{0}} (e : X ⟶ Y) (p q : U ⟶ X)
    (F : Derived Y) :
    InverseImageHom ((derivedInverseImage e).obj F) p q ≃ InverseImageHom F (p ≫ e) (q ≫ e) where
  toFun m := (derivedInverseImageComposition p e).hom.app F ≫ m ≫
    (derivedInverseImageComposition q e).inv.app F
  invFun m := (derivedInverseImageComposition p e).inv.app F ≫ m ≫
    (derivedInverseImageComposition q e).hom.app F
  left_inv m := by simp
  right_inv m := by simp

private theorem postcompHom_pullback {U V X Y : TopCat.{0}} (e : X ⟶ Y)
    (t : U ⟶ V) {p q : V ⟶ X} {p' q' : U ⟶ X} (hp : t ≫ p = p') (hq : t ≫ q = q')
    {F : Derived Y} (m : InverseImageHom ((derivedInverseImage e).obj F) p q) :
    postcompHom e p' q' F (pullbackMorphism t hp hq m) =
      pullbackMorphism t (by rw [← Category.assoc, hp] : t ≫ (p ≫ e) = p' ≫ e)
        (by rw [← Category.assoc, hq] : t ≫ (q ≫ e) = q' ≫ e)
        (postcompHom e p q F m) := by
  subst p' q'
  simp only [postcompHom, Equiv.coe_fn_mk, pullbackMorphism, eqToHom_refl,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp]
  rw [← reassoc_of% (derivedInverseImage_assoc t p e F)]
  have h : (derivedInverseImageComposition t (q ≫ e)).app F ≪≫
      (derivedInverseImage t).mapIso ((derivedInverseImageComposition q e).app F) =
    (derivedInverseImageComposition (t ≫ q) e).app F ≪≫
      (derivedInverseImageComposition t q).app ((derivedInverseImage e).obj F) :=
    Iso.ext (derivedInverseImage_assoc t q e F)
  have hi := congrArg Iso.inv h
  exact congrArg (fun v => (derivedInverseImageComposition t (p ≫ e)).hom.app F ≫
    (derivedInverseImage t).map ((derivedInverseImageComposition p e).hom.app F) ≫
    (derivedInverseImage t).map m ≫ v) hi.symm

private def restrictHom {U V X Y : TopCat.{0}} (e : X ⟶ Y) (t : U ⟶ V)
    {p q : V ⟶ Y} {p' q' : U ⟶ X}
    (hp : t ≫ p = p' ≫ e) (hq : t ≫ q = q' ≫ e) {F : Derived Y}
    (m : InverseImageHom F p q) : InverseImageHom ((derivedInverseImage e).obj F) p' q' :=
  (postcompHom e p' q' F).symm (pullbackMorphism t hp hq m)

private theorem restrictHom_id {U V X Y : TopCat.{0}} (e : X ⟶ Y) (t : U ⟶ V)
    {p : V ⟶ Y} {p' : U ⟶ X} (hp : t ≫ p = p' ≫ e) (F : Derived Y) :
    restrictHom e t hp hp (𝟙 ((derivedInverseImage p).obj F)) = 𝟙 _ := by
  simp [restrictHom, postcompHom, pullbackMorphism_id]

private theorem restrictHom_comp {U V X Y : TopCat.{0}} (e : X ⟶ Y) (t : U ⟶ V)
    {p q r : V ⟶ Y} {p' q' r' : U ⟶ X}
    (hp : t ≫ p = p' ≫ e) (hq : t ≫ q = q' ≫ e) (hr : t ≫ r = r' ≫ e)
    {F : Derived Y} (m : InverseImageHom F p q) (n : InverseImageHom F q r) :
    restrictHom e t hp hr (m ≫ n) =
      restrictHom e t hp hq m ≫ restrictHom e t hq hr n := by
  rw [restrictHom, pullbackMorphism_comp t hp hq hr]
  simp [restrictHom, postcompHom, Category.assoc]

private theorem restrictHom_injective {U V X Y : TopCat.{0}} (e : X ⟶ Y) (t : U ⟶ V)
    [(derivedInverseImage t).Faithful] {p q : V ⟶ Y} {p' q' : U ⟶ X}
    (hp : t ≫ p = p' ≫ e) (hq : t ≫ q = q' ≫ e) (F : Derived Y) :
    Function.Injective (fun m : InverseImageHom F p q => restrictHom e t hp hq m) :=
  (postcompHom e p' q' F).symm.injective.comp (pullbackMorphism_injective t hp hq F)

/-- In a commuting cube, restriction commutes with pulling back the parameter maps. -/
private theorem pullback_restrict {U V U' V' X Y : TopCat.{0}}
    (e : X ⟶ Y) (t : U ⟶ V) (t' : U' ⟶ V') (l : U' ⟶ U) (r : V' ⟶ V)
    (ht : l ≫ t = t' ≫ r) {p q : V ⟶ Y} {p' q' : U ⟶ X}
    {p₂ q₂ : V' ⟶ Y} {p₂' q₂' : U' ⟶ X}
    (hp : t ≫ p = p' ≫ e) (hq : t ≫ q = q' ≫ e)
    (hlp : l ≫ p' = p₂') (hlq : l ≫ q' = q₂')
    (hrp : r ≫ p = p₂) (hrq : r ≫ q = q₂)
    (hp₂ : t' ≫ p₂ = p₂' ≫ e) (hq₂ : t' ≫ q₂ = q₂' ≫ e)
    {F : Derived Y} (m : InverseImageHom F p q) :
    pullbackMorphism l hlp hlq (restrictHom e t hp hq m) =
      restrictHom e t' hp₂ hq₂ (pullbackMorphism r hrp hrq m) := by
  apply (postcompHom e p₂' q₂' F).injective
  rw [postcompHom_pullback]
  simp only [restrictHom, Equiv.apply_symm_apply, pullbackMorphism_twice]
  congr 1

private theorem pullbackMorphism_natural {U V X : TopCat.{0}} (t : U ⟶ V)
    {p q : V ⟶ X} {p' q' : U ⟶ X} (hp : t ≫ p = p') (hq : t ≫ q = q')
    {F G : Derived X} (c : G ≅ F) (m : InverseImageHom F p q) :
    pullbackMorphism t hp hq ((derivedInverseImage p).map c.hom ≫ m ≫
      (derivedInverseImage q).map c.inv) =
    (derivedInverseImage p').map c.hom ≫ pullbackMorphism t hp hq m ≫
      (derivedInverseImage q').map c.inv := by
  subst p' q'
  simp only [pullbackMorphism, eqToHom_refl, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc]
  have h₁ := (derivedInverseImageComposition t p).hom.naturality c.hom
  have h₂ := (derivedInverseImageComposition t q).inv.naturality c.inv
  rw [reassoc_of% h₁]
  exact congrArg (fun z => _ ≫ _ ≫ _ ≫ z) h₂

private def derivedPullbackEquivalence {X Y : TopCat.{0}} (v : X ≅ Y) :
    Derived Y ≌ Derived X :=
  CategoryTheory.Equivalence.mk (derivedInverseImage v.hom) (derivedInverseImage v.inv)
    ((derivedInverseImageIdentity Y).symm ≪≫
      eqToIso (congrArg derivedInverseImage v.inv_hom_id.symm) ≪≫
      derivedInverseImageComposition v.inv v.hom)
    ((derivedInverseImageComposition v.hom v.inv).symm ≪≫
      eqToIso (congrArg derivedInverseImage v.hom_inv_id) ≪≫
      derivedInverseImageIdentity X)

private def changeDatumCoefficients {H : AnalyticGroup.{0}} {X : TopCat.{0}}
    {A : AnalyticAction H X} {F G : Derived X} (c : G ≅ F)
    (α : A.Equivariance F) : A.Equivariance G where
  iso := (derivedInverseImage A.act).mapIso c ≪≫ α.iso ≪≫
    (derivedInverseImage (AnalyticAction.projection H X)).mapIso c.symm
  identity := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      pullbackMorphism_natural, α.identity, Category.id_comp, ← Functor.map_comp,
      Iso.hom_inv_id]
    exact (derivedInverseImage (𝟙 X)).map_id G
  multiplication := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Category.assoc, pullbackMorphism_natural]
    rw [α.multiplication]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
    erw [(derivedInverseImage (AnalyticAction.secondParameter H X ≫ A.act)).map_id, Category.id_comp]

private def changeCoefficients {J : JetSystem.{0}} {X : TopCat.{0}}
    {A : JetAction J X} {F G : Derived X} (c : G ≅ F)
    (α : A.Equivariance F) : A.Equivariance G where
  datum k hk := changeDatumCoefficients c (α.datum k hk)
  compatibility := by
    intro k l hk h
    simp only [changeDatumCoefficients, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, pullbackMorphism_natural, α.compatibility]
    rfl

private theorem parameterSquare {U V U' V' X Y : TopCat.{0}}
    {e : X ⟶ Y} {t : U ⟶ V} {t' : U' ⟶ V'} {l : U' ⟶ U} {r : V' ⟶ V}
    (ht : l ≫ t = t' ≫ r) {p : V ⟶ Y} {p' : U ⟶ X} {p₂ : V' ⟶ Y} {p₂' : U' ⟶ X}
    (hp : t ≫ p = p' ≫ e) (hl : l ≫ p' = p₂') (hr : r ≫ p = p₂) :
    t' ≫ p₂ = p₂' ≫ e := by
  rw [← hr, ← Category.assoc, ← ht, Category.assoc, hp, ← Category.assoc, hl]

private theorem reflectLevelLaws {H : AnalyticGroup.{0}} {X Y : TopCat.{0}} (e : X ≅ Y)
    (A : AnalyticAction H X) (B : AnalyticAction H Y)
    (s : parameterInclusion H e.hom ≫ B.act = A.act ≫ e.hom)
    {G : Derived Y} (α : A.Equivariance ((derivedInverseImage e.hom).obj G))
    (β : (derivedInverseImage B.act).obj G ≅
      (derivedInverseImage (AnalyticAction.projection H Y)).obj G)
    (hβ : restrictHom e.hom (parameterInclusion H e.hom) s (projectionSquare H e.hom)
      β.hom = α.iso.hom) :
    ∃ b : B.Equivariance G, b.iso = β := by
  let t := parameterInclusion H e.hom
  let p := projectionSquare H e.hom
  refine ⟨⟨β, ?_, ?_⟩, rfl⟩
  · have : (derivedInverseImage e.hom).IsEquivalence :=
      (derivedPullbackEquivalence e).isEquivalence_functor
    have ht : AnalyticAction.identitySection H X ≫ t =
        e.hom ≫ AnalyticAction.identitySection H Y := TopCat.ext (fun _ => rfl)
    have hi : e.hom ≫ 𝟙 Y = 𝟙 X ≫ e.hom := by simp
    apply restrictHom_injective e.hom e.hom hi hi G
    dsimp only
    rw [← pullback_restrict e.hom t e.hom _ _ ht s p
      (AnalyticAction.identity_act A) AnalyticAction.identity_projection
      (AnalyticAction.identity_act B) AnalyticAction.identity_projection hi hi,
      restrictHom_id, hβ]
    exact α.identity
  · let E := productIso H (productIso H e)
    let t₂ := E.hom
    have : (derivedInverseImage t₂).IsEquivalence :=
      (derivedPullbackEquivalence E).isEquivalence_functor
    have hm : AnalyticAction.multiplyParameters H X ≫ t =
        t₂ ≫ AnalyticAction.multiplyParameters H Y := TopCat.ext (fun _ => rfl)
    have hf : AnalyticAction.firstAfterSecond A ≫ t =
        t₂ ≫ AnalyticAction.firstAfterSecond B := by
      apply TopCat.ext
      intro x
      exact Prod.ext rfl (congrArg (fun f => f x.2) s).symm
    have hs : AnalyticAction.secondParameter H X ≫ t =
        t₂ ≫ AnalyticAction.secondParameter H Y := TopCat.ext (fun _ => rfl)
    have sa := parameterSquare hm s rfl rfl
    have sp := parameterSquare hm p rfl rfl
    have sm := parameterSquare hs s rfl rfl
    apply restrictHom_injective e.hom t₂ sa sp G
    dsimp only
    rw [restrictHom_comp e.hom t₂ sa sm sp]
    rw [← pullback_restrict e.hom t t₂ _ _ hm s p rfl rfl rfl rfl sa sp,
      ← pullback_restrict e.hom t t₂ _ _ hf s p (AnalyticAction.multiply_act A)
        (AnalyticAction.first_projection A) (AnalyticAction.multiply_act B)
        (AnalyticAction.first_projection B) sa sm,
      ← pullback_restrict e.hom t t₂ _ _ hs s p rfl AnalyticAction.multiply_projection
        rfl AnalyticAction.multiply_projection sm sp]
    rw [hβ]
    exact α.multiplication

private def restrictionIso {U V X Y : TopCat.{0}} (e : X ⟶ Y)
    {t : U ⟶ V} {p : V ⟶ Y} {q : U ⟶ X} (h : t ≫ p = q ≫ e) (G : Derived Y) :
    (derivedInverseImage q).obj ((derivedInverseImage e).obj G) ≅
      (derivedInverseImage t).obj ((derivedInverseImage p).obj G) :=
  ((derivedInverseImageComposition q e).app G).symm ≪≫ pullIso h G

private theorem restrictHom_iso {U V X Y : TopCat.{0}} (e : X ⟶ Y) (t : U ⟶ V)
    {p q : V ⟶ Y} {p' q' : U ⟶ X}
    (hp : t ≫ p = p' ≫ e) (hq : t ≫ q = q' ≫ e) {G : Derived Y}
    (m : InverseImageHom G p q) :
    restrictHom e t hp hq m = (restrictionIso e hp G).hom ≫
      (derivedInverseImage t).map m ≫ (restrictionIso e hq G).inv := by
  rw [restrictHom, pullbackMorphism_eq]
  change (derivedInverseImageComposition p' e).inv.app G ≫ ((pullIso hp G).hom ≫
      (derivedInverseImage t).map m ≫ (pullIso hq G).inv) ≫
      (derivedInverseImageComposition q' e).hom.app G = _
  simp only [restrictionIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Iso.app_hom, Iso.app_inv]

private theorem liftLevelDatum {H : AnalyticGroup.{0}} {X Y : TopCat.{0}} (e : X ≅ Y)
    (A : AnalyticAction H X) (B : AnalyticAction H Y)
    (s : parameterInclusion H e.hom ≫ B.act = A.act ≫ e.hom)
    {G : Derived Y} (α : A.Equivariance ((derivedInverseImage e.hom).obj G)) :
    ∃ β : B.Equivariance G,
      restrictHom e.hom (parameterInclusion H e.hom) s (projectionSquare H e.hom)
        β.iso.hom = α.iso.hom := by
  let t := parameterInclusion H e.hom
  let p := projectionSquare H e.hom
  let aIso := restrictionIso e.hom s G
  let pIso := restrictionIso e.hom p G
  let ff : (derivedInverseImage t).FullyFaithful :=
    (derivedPullbackEquivalence (productIso H e)).fullyFaithfulFunctor
  let bIso := aIso.symm ≪≫ α.iso ≪≫ pIso
  let β := ff.preimageIso bIso
  have hm : (derivedInverseImage t).map β.hom = bIso.hom := ff.map_preimage _
  have hβ : restrictHom e.hom t s p β.hom = α.iso.hom := by
    rw [restrictHom_iso, hm]
    change aIso.hom ≫ (aIso.inv ≫ α.iso.hom ≫ pIso.hom) ≫ pIso.inv = _
    simp
  obtain ⟨b, hb⟩ := reflectLevelLaws e A B s α β hβ
  refine ⟨b, ?_⟩
  rw [hb]
  exact hβ

private theorem liftEquivariance {J : JetSystem.{0}} {X Y : TopCat.{0}} (e : X ≅ Y)
    (A : JetAction J X) (B : JetAction J Y) (h : JetMapsCommute A B e.hom)
    (hAB : A.cutoff ≤ B.cutoff)
    {G : Derived Y} (α : A.Equivariance ((derivedInverseImage e.hom).obj G)) :
    ∃ β : B.Equivariance G, ∀ k hx hy, restrictedArrow h β k hx hy = (α.datum k hx).iso.hom := by
  let s := fun (k : ℕ) (hk : B.cutoff ≤ k) => h k (hAB.trans hk) hk
  have hex (k : ℕ) (hk : B.cutoff ≤ k) := liftLevelDatum e
    (A.action k (hAB.trans hk)) (B.action k hk) (s k hk) (α.datum k (hAB.trans hk))
  choose β hβ using hex
  refine ⟨⟨β, ?_⟩, ?_⟩
  · intro k l hk hkl
    let H := J.group k
    let K := J.group l
    let tk := parameterInclusion H e.hom
    let tl := parameterInclusion K e.hom
    let p := projectionSquare H e.hom
    let tx := J.parameterMap hkl (𝟙 X)
    let ty := J.parameterMap hkl (𝟙 Y)
    have : (derivedInverseImage tl).IsEquivalence :=
      (derivedPullbackEquivalence (productIso K e)).isEquivalence_functor
    have ht : tx ≫ tk = tl ≫ ty := TopCat.ext (fun _ => rfl)
    have hpX : tx ≫ AnalyticAction.projection H X = AnalyticAction.projection K X :=
      TopCat.ext (fun _ => rfl)
    have hpY : ty ≫ AnalyticAction.projection H Y = AnalyticAction.projection K Y :=
      TopCat.ext (fun _ => rfl)
    have hl := hk.trans hkl
    change pullbackMorphism ty (B.factors hk hkl) hpY (β k hk).iso.hom = (β l hl).iso.hom
    apply restrictHom_injective e.hom tl (s l hl) (projectionSquare K e.hom) G
    dsimp only
    rw [← pullback_restrict e.hom tk tl tx ty ht (s k hk) p
      (A.factors (hAB.trans hk) hkl) hpX (B.factors hk hkl) hpY (s l hl)
      (projectionSquare K e.hom),
      hβ k hk, hβ l hl]
    exact α.compatibility (hAB.trans hk) hkl
  · intro k hx hy
    exact hβ k hy

private theorem transportEquivariance {J : JetSystem.{0}} {X Y : TopCat.{0}} (e : X ≅ Y)
    (A : JetAction J X) (B : JetAction J Y) (h : JetMapsCommute A B e.hom)
    (hAB : A.cutoff ≤ B.cutoff) {F : BoundedBelow X} {G : BoundedBelow Y}
    (c : (boundedBelowInverseImage e.hom).obj G ≅ F) (α : A.Equivariance F.obj) :
    ∃ β : B.Equivariance G.obj, PullbackIntertwines h α β c := by
  let c' : (derivedInverseImage e.hom).obj G.obj ≅ F.obj := DerivedCategory.Plus.ι.mapIso c
  let α' := changeCoefficients c' α
  obtain ⟨β, hβ⟩ := liftEquivariance e A B h hAB α'
  refine ⟨β, ?_⟩
  intro k hx hy
  dsimp only
  rw [hβ k hx hy]
  change _ ≫ _ = (_ ≫ _ ≫ (derivedInverseImage (AnalyticAction.projection (J.group k) X)).map c'.inv) ≫
    (derivedInverseImage (AnalyticAction.projection (J.group k) X)).map c'.hom
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  erw [(derivedInverseImage (AnalyticAction.projection (J.group k) X)).map_id, Category.comp_id]
  rfl

end EquivarianceTransport

private theorem boundedBelowEq_app {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : f = g) (G : BoundedBelow Y) :
    ((eqToHom (congrArg boundedBelowInverseImage h)).app G).hom =
      eqToHom (congrArg (fun u => (derivedInverseImage u).obj G.obj) h) := by
  subst g
  rfl

private theorem boundedBelowComposition_hom {U V X : TopCat.{0}} (k : U ⟶ V) (j : V ⟶ X)
    (G : BoundedBelow X) :
    ((boundedBelowPullbackComposition k j).hom.app G).hom =
      (derivedInverseImageComposition k j).hom.app G.obj := rfl

private theorem boundedBelowComposition_inv {U V X : TopCat.{0}} (k : U ⟶ V) (j : V ⟶ X)
    (G : BoundedBelow X) :
    ((boundedBelowPullbackComposition k j).inv.app G).hom =
      (derivedInverseImageComposition k j).inv.app G.obj := rfl

section

variable {U X V Y : TopCat.{0}} {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V}
  (h : v ≫ k = j ≫ e) (G : BoundedBelow Y)

private theorem pullbackSquare_hom :
    (pullbackSquare (j := v) (k := e) h).hom =
      (boundedBelowPullbackComposition v k).inv ≫
        eqToHom (congrArg boundedBelowInverseImage h) ≫
        (boundedBelowPullbackComposition j e).hom := by
  rfl

private theorem pullbackSquare_hom_app :
    (pullbackSquare (j := v) (k := e) h).hom.app G =
      (boundedBelowPullbackComposition v k).inv.app G ≫
        (eqToHom (congrArg boundedBelowInverseImage h)).app G ≫
        (boundedBelowPullbackComposition j e).hom.app G := by
  rw [pullbackSquare_hom h, NatTrans.comp_app, NatTrans.comp_app]

private theorem pullbackSquare_underlying :
    ((pullbackSquare (j := v) (k := e) h).hom.app G).hom =
      ((boundedBelowPullbackComposition v k).inv.app G).hom ≫
        ((eqToHom (congrArg boundedBelowInverseImage h)).app G).hom ≫
        ((boundedBelowPullbackComposition j e).hom.app G).hom := by
  rw [pullbackSquare_hom_app h G, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom]

private theorem pullbackSquare_composition :
    ((boundedBelowPullbackComposition v k).inv.app G).hom ≫
        ((eqToHom (congrArg boundedBelowInverseImage h)).app G).hom ≫
        ((boundedBelowPullbackComposition j e).hom.app G).hom =
      (derivedInverseImageComposition v k).inv.app G.obj ≫
          eqToHom (congrArg (fun u => (derivedInverseImage u).obj G.obj) h) ≫
          (derivedInverseImageComposition j e).hom.app G.obj := by
  simp only [boundedBelowComposition_inv, boundedBelowEq_app h G, boundedBelowComposition_hom]

private theorem restrictionIso_inv :
    (restrictionIso e h G.obj).inv =
      (derivedInverseImageComposition v k).inv.app G.obj ≫
          eqToHom (congrArg (fun u => (derivedInverseImage u).obj G.obj) h) ≫
          (derivedInverseImageComposition j e).hom.app G.obj := by
  simp only [restrictionIso, pullIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Iso.app_hom, Iso.app_inv,
    Category.assoc]

private theorem pullbackSquare_hom_hom :
    ((pullbackSquare h).hom.app G).hom = (restrictionIso e h G.obj).inv :=
  (pullbackSquare_underlying h G).trans ((pullbackSquare_composition h G).trans (restrictionIso_inv h G).symm)

end

private theorem transportMate {J : JetSystem.{0}} {X Y : TopCat.{0}} (v : X ≅ Y)
    (a : DerivedAdjunctions) (A : JetAction J X) (B : JetAction J Y)
    (h : JetMapsCommute A B v.hom)
    {F : BoundedBelow X} {G : BoundedBelow Y} (α : A.Equivariance F.obj)
    (β : B.Equivariance G.obj) (c : (boundedBelowInverseImage v.hom).obj G ≅ F)
    (hc : PullbackIntertwines h α β c) :
    ∃ i : (derivedDirectImage v.hom).obj F ≅ G,
      i.inv = (a v.hom).homEquiv G F c.hom ∧ DirectImageIntertwines a A B h F α G β i := by
  let b := a v.hom
  have : (boundedBelowInverseImage v.hom).IsEquivalence := (pullbackEquivalence v).isEquivalence_functor
  have : IsIso b.unit := inferInstance
  have : IsIso b.counit := inferInstance
  have : IsIso (b.homEquiv G F c.hom) := by
    rw [b.homEquiv_unit]
    infer_instance
  let i := (asIso (b.homEquiv G F c.hom)).symm
  refine ⟨i, rfl, ?_⟩
  intro k hx hy
  let H := J.group k
  let t := productIso H v
  let L := a t.hom
  let p := projectionSquare H v.hom
  let s := h k hx hy
  have : (boundedBelowInverseImage t.hom).IsEquivalence := (pullbackEquivalence t).isEquivalence_functor
  have : IsIso L.unit := inferInstance
  refine ⟨adjointSquareMap_isIso (pullbackSquare s) L b F,
    adjointSquareMap_isIso (pullbackSquare p) L b F, ?_⟩
  let α' : (boundedBelowInverseImage (A.action k hx).act).obj F ⟶
      (boundedBelowInverseImage (AnalyticAction.projection H X)).obj F :=
    ObjectProperty.homMk (α.datum k hx).iso.hom
  let β' : (boundedBelowInverseImage (B.action k hy).act).obj G ⟶
      (boundedBelowInverseImage (AnalyticAction.projection H Y)).obj G :=
    ObjectProperty.homMk (β.datum k hy).iso.hom
  have hh : (pullbackSquare s).hom.app G ≫
        (boundedBelowInverseImage (A.action k hx).act).map c.hom ≫ α' =
      (boundedBelowInverseImage t.hom).map β' ≫ (pullbackSquare p).hom.app G ≫
        (boundedBelowInverseImage (AnalyticAction.projection H X)).map c.hom := by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackSquare_hom_hom]
    let sa := restrictionIso v.hom s G.obj
    let sp := restrictionIso v.hom p G.obj
    change sa.inv ≫ (derivedInverseImage (A.action k hx).act).map c.hom.hom ≫
        (α.datum k hx).iso.hom =
      (derivedInverseImage (parameterInclusion H v.hom)).map (β.datum k hy).iso.hom ≫
        sp.inv ≫ (derivedInverseImage (AnalyticAction.projection H X)).map c.hom.hom
    have hc' := hc k hx hy
    change (derivedInverseImage (A.action k hx).act).map c.hom.hom ≫ (α.datum k hx).iso.hom =
      restrictHom v.hom (parameterInclusion H v.hom) s p (β.datum k hy).iso.hom ≫
        (derivedInverseImage (AnalyticAction.projection H X)).map c.hom.hom at hc'
    rw [restrictHom_iso] at hc'
    change _ = (sa.hom ≫ _ ≫ sp.inv) ≫ _ at hc'
    have hw := congrArg (fun m => sa.inv ≫ m) hc'
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hw
  exact congrArg InducedCategory.Hom.hom
    (adjointSquareIntertwines (pullbackSquare s) (pullbackSquare p) L b c.hom i rfl α' β' hh)

/-- Derived direct-image transport for an equivariant homeomorphism at every common jet level. -/
theorem equivariantHomeomorphismDirectImage_conditional
    (_ : EquivariantIntersectionComplexesSpecs.Expected.EquivariantIntersectionComplexes) :
    EquivariantHomeomorphismDirectImageSpecs.EquivariantHomeomorphismDirectImage := by
  intro J X Y v a A B h
  refine ⟨fun F G α β c hc => transportMate v a A B h α β c hc, ?_⟩
  intro hAB F α
  let G := (derivedDirectImage v.hom).obj F
  have : (boundedBelowInverseImage v.hom).IsEquivalence :=
    (pullbackEquivalence v).isEquivalence_functor
  let c : (boundedBelowInverseImage v.hom).obj G ≅ F := asIso ((a v.hom).counit.app F)
  obtain ⟨β, hc⟩ := transportEquivariance v A B h hAB c α
  obtain ⟨i, _, hi⟩ := transportMate v a A B h α β c hc
  exact ⟨G, β, i, hi⟩

end RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImage

theorem _root_.«RepTheorySurvey».«Geometric».«EquivariantHomeomorphismDirectImage».«equivariantHomeomorphismDirectImage» : _root_.«RepTheorySurvey».«Geometric».«EquivariantHomeomorphismDirectImageSpecs».«EquivariantHomeomorphismDirectImage» :=
  @_root_.«RepTheorySurvey».«Geometric».«EquivariantHomeomorphismDirectImage».«equivariantHomeomorphismDirectImage_conditional» (@_root_.«RepTheorySurvey».«Geometric».«EquivariantIntersectionComplexes».«equivariantIntersectionComplexes»)
