import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting

noncomputable section

open CategoryTheory CategoryTheory.Category

set_option backward.isDefEq.respectTransparency false

universe u

namespace RepTheorySurvey.Geometric.DerivedPullbackPasting

open Analytic Analytic.DerivedPullbackPasting.Expected
open Analytic.IntersectionComplex (boundedBelowPullbackComposition pullbackSquare)

private abbrev identityIso (X : TopCat.{u}) : derivedInverseImage (𝟙 X) ≅ 𝟭 (Derived X) :=
  identityValue X

abbrev derivedInverseImageIdentity : Analytic.DerivedPullbackPasting.Expected.IdentityType.{u} :=
  Analytic.DerivedPullbackPasting.Expected.identityValue.{u}

abbrev derivedPullbackSquare : Analytic.DerivedPullbackPasting.Expected.SquareType.{u} :=
  Analytic.DerivedPullbackPasting.Expected.squareValue.{u}

private abbrev inverseIdentity (X : TopCat.{u}) : inverseImage (𝟙 X) ≅ 𝟭 (Sheaves X) :=
  (inverseDirectAdjunction (𝟙 X)).leftAdjointUniq Adjunction.id

private theorem inverseComposition_unit {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaves Z) :
    (inverseDirectAdjunction (f ≫ g)).unit.app F ≫
        (directImage (f ≫ g)).map ((inverseImageComposition f g).hom.app F) =
      (inverseDirectAdjunction g).unit.app F ≫
        (directImage g).map ((inverseDirectAdjunction f).unit.app ((inverseImage g).obj F)) :=
  (Adjunction.unit_leftAdjointUniq_hom_app _ _ F).trans
    (Adjunction.comp_unit_app (inverseDirectAdjunction g) (inverseDirectAdjunction f) F)

private theorem inverseIdentity_unit (X : TopCat.{u}) (F : Sheaves X) :
    (inverseDirectAdjunction (𝟙 X)).unit.app F ≫ (inverseIdentity X).hom.app F = 𝟙 F :=
  Adjunction.unit_leftAdjointUniq_hom_app
    (inverseDirectAdjunction (𝟙 X)) Adjunction.id F

private theorem inverseComposition_leftUnit {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Sheaves Y) :
    (inverseImageComposition (𝟙 X) f).hom.app F ≫
      (inverseIdentity X).hom.app ((inverseImage f).obj F) =
      𝟙 ((inverseImage f).obj F) := by
  apply ((inverseDirectAdjunction f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := inverseComposition_unit (𝟙 X) f F
  change (inverseDirectAdjunction f).unit.app F ≫
      (directImage f).map ((inverseImageComposition (𝟙 X) f).hom.app F) = _ at hu
  rw [← assoc, hu]
  erw [assoc, ← (directImage f).map_comp, inverseIdentity_unit]

private theorem inverseComposition_rightUnit {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Sheaves Y) :
    (inverseImageComposition f (𝟙 Y)).hom.app F ≫
      (inverseImage f).map ((inverseIdentity Y).hom.app F) =
      𝟙 ((inverseImage f).obj F) := by
  apply ((inverseDirectAdjunction f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := inverseComposition_unit f (𝟙 Y) F
  change (inverseDirectAdjunction f).unit.app F ≫
      (directImage f).map ((inverseImageComposition f (𝟙 Y)).hom.app F) =
      (inverseDirectAdjunction (𝟙 Y)).unit.app F ≫
        (inverseDirectAdjunction f).unit.app _ at hu
  rw [← assoc, hu]
  have hn := ((inverseDirectAdjunction f).unit.naturality ((inverseIdentity Y).hom.app F)).symm
  change (inverseDirectAdjunction f).unit.app ((inverseImage (𝟙 Y)).obj F) ≫
    (directImage f).map ((inverseImage f).map ((inverseIdentity Y).hom.app F)) =
      (inverseIdentity Y).hom.app F ≫ (inverseDirectAdjunction f).unit.app F at hn
  erw [assoc, hn, ← assoc, inverseIdentity_unit, id_comp]

private theorem inverseComposition_assoc {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Sheaves Z) :
    (inverseImageComposition (f ≫ g) h).hom.app F ≫
      (inverseImageComposition f g).hom.app ((inverseImage h).obj F) =
    (inverseImageComposition f (g ≫ h)).hom.app F ≫
      (inverseImage f).map ((inverseImageComposition g h).hom.app F) := by
  apply ((inverseDirectAdjunction ((f ≫ g) ≫ h)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← assoc]
  rw [inverseComposition_unit]
  have hu := inverseComposition_unit f (g ≫ h) F
  change (inverseDirectAdjunction ((f ≫ g) ≫ h)).unit.app F ≫
      (directImage ((f ≫ g) ≫ h)).map ((inverseImageComposition f (g ≫ h)).hom.app F) = _ at hu
  rw [hu]
  change (_ ≫ (directImage h).map ((inverseDirectAdjunction (f ≫ g)).unit.app _)) ≫
        (directImage h).map ((directImage (f ≫ g)).map
          ((inverseImageComposition f g).hom.app _)) =
    (_ ≫ (directImage (g ≫ h)).map ((inverseDirectAdjunction f).unit.app _)) ≫
      (directImage (g ≫ h)).map ((directImage f).map
        ((inverseImage f).map ((inverseImageComposition g h).hom.app _)))
  simp only [assoc, ← Functor.map_comp, inverseComposition_unit]
  have hn := ((inverseDirectAdjunction f).unit.naturality
    ((inverseImageComposition g h).hom.app F)).symm
  change (inverseDirectAdjunction f).unit.app _ ≫
    (directImage f).map ((inverseImage f).map ((inverseImageComposition g h).hom.app F)) =
      (inverseImageComposition g h).hom.app F ≫ (inverseDirectAdjunction f).unit.app _ at hn
  rw [hn, (directImage (g ≫ h)).map_comp, ← assoc, inverseComposition_unit]
  erw [(directImage h).map_comp, assoc]
  rfl

private theorem identityLocalizedCommShift (X : TopCat.{u}) :
    letI : (derivedInverseImage (𝟙 X)).CommShift ℤ :=
      inferInstanceAs ((inverseImage (𝟙 X)).mapDerivedCategory.CommShift ℤ)
    NatTrans.CommShift (identityIso X).hom ℤ := by
  change NatTrans.CommShift
    ((inverseIdentity X).hom.mapDerivedCategory ≫ (Functor.mapDerivedCategoryIdIso (Sheaves X)).hom) ℤ
  infer_instance

theorem identityCommShift : IdentityCommShift.{u} := identityLocalizedCommShift

private theorem compositionLocalizedCommShift {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI : (derivedInverseImage (f ≫ g)).CommShift ℤ :=
      inferInstanceAs ((inverseImage (f ≫ g)).mapDerivedCategory.CommShift ℤ)
    letI : (derivedInverseImage g).CommShift ℤ :=
      inferInstanceAs ((inverseImage g).mapDerivedCategory.CommShift ℤ)
    letI : (derivedInverseImage f).CommShift ℤ :=
      inferInstanceAs ((inverseImage f).mapDerivedCategory.CommShift ℤ)
    NatTrans.CommShift (derivedInverseImageComposition f g).hom ℤ := by
  change NatTrans.CommShift
    ((inverseImageComposition f g).hom.mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIso (inverseImage g) (inverseImage f)).inv) ℤ
  infer_instance

theorem compositionCommShift : CompositionCommShift.{u} := compositionLocalizedCommShift

theorem pullbackIdentityMorphism : PullbackIdentityMorphism.{u} := by
  intro W Y X k f f' hf F
  subst f'
  simp [pullbackMorphism]

theorem pullbackComposition : PullbackComposition.{u} := by
  intro W Y X k f g h f' g' h' hf hg hh F α β
  subst f'
  subst g'
  subst h'
  simp [pullbackMorphism, Functor.map_comp, assoc]

theorem pullbackNaturality : PullbackNaturality.{u} := by
  intro W Y X k f g f' g' hf hg F G a α β h
  subst f'
  subst g'
  simp only [pullbackMorphism, eqToHom_refl, id_comp, comp_id, assoc]
  rw [(derivedInverseImageComposition k f).hom.naturality_assoc]
  change (derivedInverseImageComposition k f).hom.app F ≫
    (derivedInverseImage k).map ((derivedInverseImage f).map a) ≫
      (derivedInverseImage k).map β ≫ _ = _
  rw [← Functor.map_comp_assoc, h, Functor.map_comp, assoc]
  erw [(derivedInverseImageComposition k g).inv.naturality]

private abbrev cochainInverse {X Y : TopCat.{u}} (f : X ⟶ Y) :=
  (inverseImage f).mapHomologicalComplex (.up ℤ)

private abbrev cochainComparison {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex (Sheaves Z) ℤ) : (cochainInverse (f ≫ g)).obj K ⟶
      (cochainInverse f).obj ((cochainInverse g).obj K) :=
  ((inverseImageComposition f g).hom.mapHomologicalComplex (.up ℤ)).app K

private abbrev cochainIdentity (X : TopCat.{u}) (K : CochainComplex (Sheaves X) ℤ) :
    (cochainInverse (𝟙 X)).obj K ⟶ K :=
  ((inverseIdentity X).hom.mapHomologicalComplex (.up ℤ)).app K

private abbrev inverseFactor {X Y : TopCat.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaves Y) ℤ) :
    (derivedInverseImage f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((cochainInverse f).obj K) :=
  (inverseImage f).mapDerivedCategoryFactors.app K

@[reassoc]
private theorem composition_factor {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex (Sheaves Z) ℤ) :
    (derivedInverseImageComposition f g).hom.app (DerivedCategory.Q.obj K) ≫
        (derivedInverseImage f).map (inverseFactor g K).hom ≫
        (inverseFactor f ((cochainInverse g).obj K)).hom =
      (inverseFactor (f ≫ g) K).hom ≫ DerivedCategory.Q.map (cochainComparison f g K) := by
  let together := inverseImage g ⋙ inverseImage f
  let comparison := Functor.mapDerivedCategoryCompIso (inverseImage g) (inverseImage f)
  have compFactor : comparison.hom.app (DerivedCategory.Q.obj K) ≫
        together.mapDerivedCategoryFactors.hom.app K =
      (derivedInverseImage f).map (inverseFactor g K).hom ≫
        (inverseFactor f ((cochainInverse g).obj K)).hom := by
    change (Functor.mapDerivedCategoryCompIso _ _).hom.app _ ≫ _ = _
    rw [Functor.mapDerivedCategoryCompIso_hom_app_Q_obj]
    have cochainComp :
        (Functor.mapHomologicalComplexCompIso (Iso.refl together) (.up ℤ)).hom.app K =
          𝟙 ((together.mapHomologicalComplex (.up ℤ)).obj K) := by
      ext
      rfl
    dsimp only [together] at cochainComp ⊢
    rw [cochainComp]
    erw [DerivedCategory.Q.map_id, id_comp]
    simp only [assoc]
    erw [Iso.inv_hom_id_app, comp_id]
    rfl
  change ((inverseImageComposition f g).hom.mapDerivedCategory.app (DerivedCategory.Q.obj K) ≫
    comparison.inv.app (DerivedCategory.Q.obj K)) ≫ _ = _
  rw [assoc, ← compFactor, Iso.inv_hom_id_app_assoc, NatTrans.mapDerivedCategory_app_Q_obj]
  dsimp only [together]
  erw [assoc, assoc, Iso.inv_hom_id_app, comp_id]
  rfl

@[reassoc]
private theorem identity_factor (X : TopCat.{u}) (K : CochainComplex (Sheaves X) ℤ) :
    (identityIso X).hom.app (DerivedCategory.Q.obj K) =
      (inverseFactor (𝟙 X) K).hom ≫ DerivedCategory.Q.map (cochainIdentity X K) := by
  change ((inverseIdentity X).hom.mapDerivedCategory.app (DerivedCategory.Q.obj K)) ≫
    (Functor.mapDerivedCategoryIdIso _).hom.app _ = _
  rw [NatTrans.mapDerivedCategory_app_Q_obj, Functor.mapDerivedCategoryIdIso_hom_app]
  have cochainId : (Functor.mapHomologicalComplexIdIso (Sheaves X) (.up ℤ)).hom.app K = 𝟙 K := by
    ext
    rfl
  rw [cochainId, DerivedCategory.Q.map_id]
  erw [comp_id, assoc, assoc, Iso.inv_hom_id_app, comp_id]
  rfl

private theorem compare_on_cochains {X Y : TopCat.{u}}
    {P R : Derived Y ⥤ Derived X} {α β : P ⟶ R}
    (h : ∀ K : CochainComplex (Sheaves Y) ℤ,
      α.app (DerivedCategory.Q.obj K) = β.app (DerivedCategory.Q.obj K)) : α = β :=
  Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso (Sheaves Y) (.up ℤ)) h

private theorem leftUnit_on_cochains {X Y : TopCat.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaves Y) ℤ) :
    (derivedInverseImageComposition (𝟙 X) f).hom.app (DerivedCategory.Q.obj K) ≫
      (identityIso X).hom.app ((derivedInverseImage f).obj (DerivedCategory.Q.obj K)) =
    𝟙 ((derivedInverseImage f).obj (DerivedCategory.Q.obj K)) := by
  rw [← cancel_mono (inverseFactor f K).hom, assoc]
  conv_rhs => erw [id_comp]
  have hn := ((identityIso X).hom.naturality (inverseFactor f K).hom).symm
  change (identityIso X).hom.app _ ≫ (inverseFactor f K).hom =
    (derivedInverseImage (𝟙 X)).map (inverseFactor f K).hom ≫ (identityIso X).hom.app _ at hn
  erw [hn, identity_factor X ((cochainInverse f).obj K), composition_factor_assoc (𝟙 X) f K,
    ← (DerivedCategory.Q (C := Sheaves X)).map_comp]
  have hc : cochainComparison (𝟙 X) f K ≫ cochainIdentity X ((cochainInverse f).obj K) =
      𝟙 ((cochainInverse f).obj K) := by
    ext i
    exact inverseComposition_leftUnit f (K.X i)
  erw [hc, DerivedCategory.Q.map_id]
  exact comp_id _

private theorem rightUnit_on_cochains {X Y : TopCat.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaves Y) ℤ) :
    (derivedInverseImageComposition f (𝟙 Y)).hom.app (DerivedCategory.Q.obj K) ≫
      (derivedInverseImage f).map ((identityIso Y).hom.app (DerivedCategory.Q.obj K)) =
    𝟙 ((derivedInverseImage f).obj (DerivedCategory.Q.obj K)) := by
  rw [← cancel_mono (inverseFactor f K).hom, assoc]
  conv_rhs => erw [id_comp]
  rw [identity_factor, CategoryTheory.Functor.map_comp, assoc]
  have hn := (inverseImage f).mapDerivedCategoryFactors_hom_naturality (cochainIdentity Y K)
  change (derivedInverseImage f).map (DerivedCategory.Q.map (cochainIdentity Y K)) ≫
      (inverseFactor f K).hom =
    (inverseFactor f _).hom ≫ DerivedCategory.Q.map ((cochainInverse f).map (cochainIdentity Y K)) at hn
  erw [hn, composition_factor_assoc, ← DerivedCategory.Q.map_comp]
  have hc : cochainComparison f (𝟙 Y) K ≫ (cochainInverse f).map (cochainIdentity Y K) =
      𝟙 ((cochainInverse f).obj K) := by
    ext i
    exact inverseComposition_rightUnit f (K.X i)
  erw [hc, DerivedCategory.Q.map_id]
  exact comp_id _

theorem compositionLeftUnit : CompositionLeftUnit.{u} := by
  intro X Y f F
  change _ = eqToHom (rfl : (derivedInverseImage f).obj F = _)
  rw [eqToHom_refl]
  exact congr_app (compare_on_cochains
    (α := (derivedInverseImageComposition (𝟙 X) f).hom ≫
      CategoryTheory.Functor.whiskerLeft (derivedInverseImage f) (identityIso X).hom)
    (β := 𝟙 _) (leftUnit_on_cochains f)) F

theorem compositionRightUnit : CompositionRightUnit.{u} := by
  intro X Y f F
  change _ = eqToHom (rfl : (derivedInverseImage f).obj F = _)
  rw [eqToHom_refl]
  exact congr_app (compare_on_cochains
    (α := (derivedInverseImageComposition f (𝟙 Y)).hom ≫
      CategoryTheory.Functor.whiskerRight (identityIso Y).hom (derivedInverseImage f))
    (β := 𝟙 _) (rightUnit_on_cochains f)) F

set_option maxHeartbeats 500000 in
private theorem associativity_on_cochains {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (K : CochainComplex (Sheaves Z) ℤ) :
    (derivedInverseImageComposition (f ≫ g) h).hom.app (DerivedCategory.Q.obj K) ≫
      (derivedInverseImageComposition f g).hom.app ((derivedInverseImage h).obj (DerivedCategory.Q.obj K)) =
    (derivedInverseImageComposition f (g ≫ h)).hom.app (DerivedCategory.Q.obj K) ≫
      (derivedInverseImage f).map ((derivedInverseImageComposition g h).hom.app (DerivedCategory.Q.obj K)) := by
  let L := (cochainInverse h).obj K
  let M := (cochainInverse g).obj L
  let factor := (derivedInverseImage f).map ((derivedInverseImage g).map (inverseFactor h K).hom) ≫
    (derivedInverseImage f).map (inverseFactor g L).hom ≫ (inverseFactor f M).hom
  rw [← cancel_mono factor]
  dsimp only [factor]
  simp only [assoc]
  have hn := ((derivedInverseImageComposition f g).hom.naturality_assoc (inverseFactor h K).hom
    ((derivedInverseImage f).map (inverseFactor g L).hom ≫ (inverseFactor f M).hom)).symm
  change (derivedInverseImageComposition f g).hom.app _ ≫
      (derivedInverseImage f).map ((derivedInverseImage g).map (inverseFactor h K).hom) ≫ _ =
    (derivedInverseImage (f ≫ g)).map (inverseFactor h K).hom ≫
      (derivedInverseImageComposition f g).hom.app _ ≫ _ at hn
  erw [hn, composition_factor f g L, composition_factor_assoc (f ≫ g) h K]
  rw [← (derivedInverseImage f).map_comp_assoc, ← (derivedInverseImage f).map_comp_assoc]
  simp only [assoc]
  erw [composition_factor g h K, (derivedInverseImage f).map_comp]
  have hn' := (inverseImage f).mapDerivedCategoryFactors_hom_naturality (cochainComparison g h K)
  change (derivedInverseImage f).map (DerivedCategory.Q.map (cochainComparison g h K)) ≫
      (inverseFactor f M).hom =
    (inverseFactor f _).hom ≫ DerivedCategory.Q.map ((cochainInverse f).map (cochainComparison g h K)) at hn'
  conv_rhs =>
    arg 2
    rw [assoc, hn']
  erw [composition_factor_assoc f (g ≫ h) K]
  have hc : cochainComparison (f ≫ g) h K ≫ cochainComparison f g L =
      cochainComparison f (g ≫ h) K ≫ (cochainInverse f).map (cochainComparison g h K) := by
    ext i
    exact inverseComposition_assoc f g h (K.X i)
  have he := congrArg (fun a => (inverseFactor ((f ≫ g) ≫ h) K).hom ≫ DerivedCategory.Q.map a) hc
  simp only [(DerivedCategory.Q (C := Sheaves W)).map_comp] at he
  exact he

theorem compositionAssociativity : CompositionAssociativity.{u} := by
  intro W X Y Z f g h F
  change _ = eqToHom (rfl : (derivedInverseImage (f ≫ g ≫ h)).obj F = _) ≫ _
  rw [eqToHom_refl, id_comp]
  exact congr_app (compare_on_cochains
    (α := (derivedInverseImageComposition (f ≫ g) h).hom ≫
      CategoryTheory.Functor.whiskerLeft (derivedInverseImage h) (derivedInverseImageComposition f g).hom)
    (β := (derivedInverseImageComposition f (g ≫ h)).hom ≫
      CategoryTheory.Functor.whiskerRight (derivedInverseImageComposition g h).hom (derivedInverseImage f))
    (associativity_on_cochains f g h)) F

@[reassoc]
private theorem composition_assoc {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Derived Z) :
    (derivedInverseImageComposition (f ≫ g) h).hom.app F ≫
      (derivedInverseImageComposition f g).hom.app ((derivedInverseImage h).obj F) =
    (derivedInverseImageComposition f (g ≫ h)).hom.app F ≫
      (derivedInverseImage f).map ((derivedInverseImageComposition g h).hom.app F) := by
  simpa only [show Category.assoc f g h = rfl from Subsingleton.elim _ _, congrArg, eqToHom_refl,
    id_comp] using compositionAssociativity f g h F

theorem pullbackIdentityMap : PullbackIdentityMap.{u} := by
  intro Y X f g F α
  have hf : (derivedInverseImageComposition (𝟙 Y) f).hom.app F ≫
      (identityIso Y).hom.app ((derivedInverseImage f).obj F) = 𝟙 _ := by
    exact compositionLeftUnit f F
  have hg : (derivedInverseImageComposition (𝟙 Y) g).hom.app F ≫
      (identityIso Y).hom.app ((derivedInverseImage g).obj F) = 𝟙 _ := by
    exact compositionLeftUnit g F
  have hginv : (derivedInverseImageComposition (𝟙 Y) g).inv.app F =
      (identityIso Y).hom.app ((derivedInverseImage g).obj F) := by
    rw [← cancel_epi ((derivedInverseImageComposition (𝟙 Y) g).hom.app F),
      Iso.hom_inv_id_app, hg]
  have hn := (identityIso Y).hom.naturality α
  change (derivedInverseImage (𝟙 Y)).map α ≫ (identityIso Y).hom.app _ =
    (identityIso Y).hom.app _ ≫ α at hn
  simp only [pullbackMorphism, eqToHom_refl, id_comp, comp_id,
    hginv, hn, ← assoc, hf]

theorem pullbackSuccessive : PullbackSuccessive.{u} := by
  intro V W Y X l k f g f' g' f'' g'' hf hg hf' hg' F α
  subst f'
  subst g'
  subst f''
  subst g''
  simp only [pullbackMorphism, eqToHom_refl,
    id_comp, comp_id, CategoryTheory.Functor.map_comp, assoc]
  let gcomp := (derivedInverseImageComposition (l ≫ k) g).hom.app F
  apply (cancel_mono gcomp).mp
  simp only [gcomp, assoc, Iso.inv_hom_id_app]
  have ha := composition_assoc l k g F
  have hag : (derivedInverseImage l).map ((derivedInverseImageComposition k g).inv.app F) ≫
      (derivedInverseImageComposition l (k ≫ g)).inv.app F ≫ gcomp =
      (derivedInverseImageComposition l k).inv.app ((derivedInverseImage g).obj F) := by
    apply (cancel_epi ((derivedInverseImageComposition l (k ≫ g)).hom.app F ≫
      (derivedInverseImage l).map ((derivedInverseImageComposition k g).hom.app F))).mp
    simp only [assoc, ← (derivedInverseImage l).map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, id_comp, gcomp]
    conv_rhs =>
      rw [← assoc, ← ha, assoc, Iso.hom_inv_id_app]
      erw [comp_id]
    exact Iso.hom_inv_id_app_assoc _ _ _
  rw [hag, ← composition_assoc_assoc]
  have hn := (derivedInverseImageComposition l k).hom.naturality_assoc α
    ((derivedInverseImageComposition l k).inv.app ((derivedInverseImage g).obj F))
  change (derivedInverseImage (l ≫ k)).map α ≫
      (derivedInverseImageComposition l k).hom.app _ ≫ _ =
    (derivedInverseImageComposition l k).hom.app _ ≫
      (derivedInverseImage l).map ((derivedInverseImage k).map α) ≫ _ at hn
  rw [← hn, Iso.hom_inv_id_app]
  rfl

local instance derivedPullbackCommShift {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (derivedInverseImage f).CommShift ℤ :=
  inferInstanceAs ((inverseImage f).mapDerivedCategory.CommShift ℤ)

theorem pullbackShift : PullbackShift.{u} := by
  intro W Y X k f g f' g' hf hg F n α
  subst f'
  subst g'
  let : NatTrans.CommShift (derivedInverseImageComposition k f).hom ℤ :=
    compositionLocalizedCommShift k f
  let : NatTrans.CommShift (derivedInverseImageComposition k g).hom ℤ :=
    compositionLocalizedCommShift k g
  let : NatTrans.CommShift (derivedInverseImageComposition k g).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  simp only [pullbackMorphism, eqToHom_refl, id_comp, comp_id]
  rw [NatTrans.app_shift (derivedInverseImageComposition k f).hom n F,
    NatTrans.app_shift (derivedInverseImageComposition k g).inv n F]
  simp only [CategoryTheory.Functor.commShiftIso_comp_hom_app,
    CategoryTheory.Functor.commShiftIso_comp_inv_app, CategoryTheory.Functor.map_comp, assoc]
  simp only [← (derivedInverseImage k).map_comp_assoc, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc]
  have hα : (shiftFunctor (Derived Y) n).map α ≫
      𝟙 ((derivedInverseImage g ⋙ shiftFunctor (Derived Y) n).obj F) =
      (shiftFunctor (Derived Y) n).map α := comp_id _
  rw [hα]
  erw [CategoryTheory.Functor.commShiftIso_hom_naturality_assoc,
    Iso.inv_hom_id_app_assoc]

private abbrev transport {X Y : TopCat.{u}} {f g : X ⟶ Y} (h : f = g) (F : Derived Y) :
    (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F :=
  eqToHom (congrArg (fun t => (derivedInverseImage t).obj F) h)

private theorem transport_trans {X Y : TopCat.{u}} {f g h : X ⟶ Y}
    (h₁ : f = g) (h₂ : g = h) (F : Derived Y) :
    transport h₁ F ≫ transport h₂ F = transport (h₁.trans h₂) F := by
  cases h₁
  cases h₂
  simp [transport]

@[reassoc]
private theorem comparison_transport_right {U X Y : TopCat.{u}} (j : U ⟶ X)
    {e e' : X ⟶ Y} (h : e = e') (F : Derived Y) :
    (derivedInverseImageComposition j e).hom.app F ≫ (derivedInverseImage j).map (transport h F) =
      transport (congrArg (j ≫ ·) h) F ≫ (derivedInverseImageComposition j e').hom.app F := by
  cases h
  simp [transport]

@[reassoc]
private theorem comparison_transport_left {U X Y : TopCat.{u}} {j j' : U ⟶ X}
    (e : X ⟶ Y) (h : j = j') (F : Derived Y) :
    (derivedInverseImageComposition j e).hom.app F ≫ transport h ((derivedInverseImage e).obj F) =
      transport (congrArg (· ≫ e) h) F ≫ (derivedInverseImageComposition j' e).hom.app F := by
  cases h
  simp [transport]

@[reassoc]
private theorem reassociate_left {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Derived Z) :
    (derivedInverseImageComposition (f ≫ g) h).hom.app F ≫
      (derivedInverseImageComposition f g).hom.app ((derivedInverseImage h).obj F) ≫
      (derivedInverseImage f).map ((derivedInverseImageComposition g h).inv.app F) =
      (derivedInverseImageComposition f (g ≫ h)).hom.app F := by
  rw [composition_assoc_assoc f g h F, ← (derivedInverseImage f).map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  exact comp_id _

@[reassoc]
private theorem reassociate_right {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Derived Z) :
    (derivedInverseImageComposition f (g ≫ h)).hom.app F ≫
      (derivedInverseImage f).map ((derivedInverseImageComposition g h).hom.app F) ≫
      (derivedInverseImageComposition f g).inv.app ((derivedInverseImage h).obj F) =
      (derivedInverseImageComposition (f ≫ g) h).hom.app F := by
  rw [← composition_assoc_assoc f g h F, Iso.hom_inv_id_app]
  exact comp_id _

private theorem square_comparison_app {C D : Type*} [Category* C] [Category* D]
    {A B L R : C ⥤ D} (e : A ≅ L) (p : A = B) (d : B ≅ R) (x : C) :
    (e.symm ≪≫ eqToIso p ≪≫ d).hom.app x =
      e.inv.app x ≫ eqToHom (CategoryTheory.Functor.congr_obj p x) ≫ d.hom.app x := by
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app]

set_option maxHeartbeats 600000 in
private theorem square_hom {U X V Y : TopCat.{u}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V}
    (h : j ≫ e = v ≫ k) (F : Derived Y) :
    (squareValue h).hom.app F = (derivedInverseImageComposition j e).inv.app F ≫
      transport h F ≫ (derivedInverseImageComposition v k).hom.app F :=
  square_comparison_app (derivedInverseImageComposition j e)
    (congrArg (fun t => derivedInverseImage t) h) (derivedInverseImageComposition v k) F

theorem squareHorizontalPasting : SquareHorizontalPasting.{u} := by
  intro U X A V Y B j j' k k' v e e' h h' F
  simp only [square_hom, CategoryTheory.Functor.map_comp, assoc]
  apply (cancel_epi ((derivedInverseImageComposition (j ≫ j') e').hom.app F)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassociate_left_assoc, comparison_transport_right_assoc, reassociate_right_assoc,
    comparison_transport_left_assoc, reassociate_left]
  conv_rhs => rw [← assoc, transport_trans]

theorem squareVerticalPasting : SquareVerticalPasting.{u} := by
  intro U X V Y A B j k m v e v' e' h h' F
  simp only [square_hom, CategoryTheory.Functor.map_comp, assoc]
  apply (cancel_epi ((derivedInverseImageComposition j (e ≫ e')).hom.app F)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassociate_right_assoc, comparison_transport_left_assoc, reassociate_left_assoc,
    comparison_transport_right_assoc, reassociate_right]
  conv_rhs => rw [← assoc, transport_trans]

private theorem whiskerRight_three {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (I : D ⥤ E) {F G H K : C ⥤ D} {a : G ≅ F} {b : G ≅ H} {c : H ≅ K}
    {a' : G ⋙ I ≅ F ⋙ I} {b' : G ⋙ I ≅ H ⋙ I} {c' : H ⋙ I ≅ K ⋙ I}
    (ha : Functor.isoWhiskerRight a I = a') (hb : Functor.isoWhiskerRight b I = b')
    (hc : Functor.isoWhiskerRight c I = c') :
    Functor.isoWhiskerRight (a.symm ≪≫ b ≪≫ c) I = a'.symm ≪≫ b' ≪≫ c' := by
  simp only [Functor.isoWhiskerRight_trans, ← Functor.isoWhiskerRight_symm, ha, hb, hc]

private theorem include_comparison {U X Y : TopCat.{u}} (j : U ⟶ X) (e : X ⟶ Y) :
    Functor.isoWhiskerRight (boundedBelowPullbackComposition j e)
        (DerivedCategory.Plus.ι (C := Sheaves U)) =
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι (C := Sheaves Y))
        (derivedInverseImageComposition j e) := rfl


private theorem include_transport {U Y : TopCat.{u}} {f g : U ⟶ Y} (h : f = g) :
    Functor.isoWhiskerRight (eqToIso (congrArg (fun t => boundedBelowInverseImage t) h))
        (DerivedCategory.Plus.ι (C := Sheaves U)) =
      Functor.isoWhiskerLeft (DerivedCategory.Plus.ι (C := Sheaves Y))
        (eqToIso (congrArg (fun t => derivedInverseImage t) h)) := by
  cases h
  rfl


private theorem square_expansion {U X V Y : TopCat.{u}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V} (h : j ≫ e = v ≫ k) :
    pullbackSquare h = (boundedBelowPullbackComposition j e).symm ≪≫
      eqToIso (congrArg (fun f => boundedBelowInverseImage f) h) ≪≫
      boundedBelowPullbackComposition v k := rfl

private theorem derived_square_expansion {U X V Y : TopCat.{u}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V} (h : j ≫ e = v ≫ k) :
    squareValue h = (derivedInverseImageComposition j e).symm ≪≫
      eqToIso (congrArg (fun f => derivedInverseImage f) h) ≪≫
      derivedInverseImageComposition v k := rfl

private theorem whiskerLeft_three {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (I : C ⥤ D) {F G H K : D ⥤ E} (a : G ≅ F) (b : G ≅ H) (c : H ≅ K) :
    (I.isoWhiskerLeft a).symm ≪≫ I.isoWhiskerLeft b ≪≫ I.isoWhiskerLeft c =
      I.isoWhiskerLeft (a.symm ≪≫ b ≪≫ c) := rfl

set_option maxHeartbeats 650000 in
private theorem include_square {U X V Y : TopCat.{u}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V} (h : j ≫ e = v ≫ k) :
    Functor.isoWhiskerRight (pullbackSquare h) (DerivedCategory.Plus.ι (C := Sheaves U)) =
    Functor.isoWhiskerLeft (DerivedCategory.Plus.ι (C := Sheaves Y)) (squareValue h) := by
  let last := congrArg (Functor.isoWhiskerLeft (DerivedCategory.Plus.ι (C := Sheaves Y)))
    (derived_square_expansion h)
  let middle := whiskerRight_three (DerivedCategory.Plus.ι (C := Sheaves U))
    (include_comparison j e) (include_transport h) (include_comparison v k)
  let first := congrArg (fun t => Functor.isoWhiskerRight t (DerivedCategory.Plus.ι (C := Sheaves U)))
    (square_expansion h)
  let compose := whiskerLeft_three (DerivedCategory.Plus.ι (C := Sheaves Y))
    (derivedInverseImageComposition j e) (eqToIso (congrArg (fun f => derivedInverseImage f) h))
    (derivedInverseImageComposition v k)
  exact first.trans (middle.trans (compose.trans last.symm))


private theorem include_component {C D : Type*} [Category* C] [Category* D]
    {P : ObjectProperty D} {F G : C ⥤ P.FullSubcategory} {a : F ≅ G}
    {b : F ⋙ P.ι ≅ G ⋙ P.ι} (h : Functor.isoWhiskerRight a P.ι = b) (X : C) :
    (a.hom.app X).hom = b.hom.app X :=
  congrArg (fun t => t.hom.app X) h

private theorem whiskerLeft_component {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (I : C ⥤ D) {F G : D ⥤ E} (e : F ≅ G) (X : C) :
    (I.isoWhiskerLeft e).hom.app X = e.hom.app (I.obj X) := rfl

set_option maxHeartbeats 450000 in
theorem squareBoundedBelowCompatibility : SquareBoundedBelowCompatibility.{u} := by
  intro U X V Y j k e v h F
  let component := include_component (include_square h) F
  let restriction := whiskerLeft_component (DerivedCategory.Plus.ι (C := Sheaves Y)) (squareValue h) F
  exact component.trans restriction

section BoundedSpecialization

variable (bounded_assoc :
  ∀ {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : BoundedBelow Z),
    (boundedBelowPullbackComposition (f ≫ g) h).hom.app F ≫
      (boundedBelowPullbackComposition f g).hom.app ((boundedBelowInverseImage h).obj F) =
    (boundedBelowPullbackComposition f (g ≫ h)).hom.app F ≫
      (boundedBelowInverseImage f).map ((boundedBelowPullbackComposition g h).hom.app F))

private abbrev boundedTransport {X Y : TopCat.{u}} {f g : X ⟶ Y} (h : f = g) (F : BoundedBelow Y) :
    (boundedBelowInverseImage f).obj F ⟶ (boundedBelowInverseImage g).obj F :=
  eqToHom (congrArg (fun t => (boundedBelowInverseImage t).obj F) h)

private theorem bounded_transport_trans {X Y : TopCat.{u}} {f g h : X ⟶ Y}
    (h₁ : f = g) (h₂ : g = h) (F : BoundedBelow Y) :
    boundedTransport h₁ F ≫ boundedTransport h₂ F = boundedTransport (h₁.trans h₂) F := by
  cases h₁
  cases h₂
  simp [boundedTransport]

@[reassoc]
private theorem bounded_comparison_transport_right {U X Y : TopCat.{u}} (j : U ⟶ X)
    {e e' : X ⟶ Y} (h : e = e') (F : BoundedBelow Y) :
    (boundedBelowPullbackComposition j e).hom.app F ≫ (boundedBelowInverseImage j).map (boundedTransport h F) =
      boundedTransport (congrArg (j ≫ ·) h) F ≫ (boundedBelowPullbackComposition j e').hom.app F := by
  cases h
  simp [boundedTransport]

@[reassoc]
private theorem bounded_comparison_transport_left {U X Y : TopCat.{u}} {j j' : U ⟶ X}
    (e : X ⟶ Y) (h : j = j') (F : BoundedBelow Y) :
    (boundedBelowPullbackComposition j e).hom.app F ≫ boundedTransport h ((boundedBelowInverseImage e).obj F) =
      boundedTransport (congrArg (· ≫ e) h) F ≫ (boundedBelowPullbackComposition j' e).hom.app F := by
  cases h
  simp [boundedTransport]

include bounded_assoc in
@[reassoc]
private theorem bounded_reassociate_left {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : BoundedBelow Z) :
    (boundedBelowPullbackComposition (f ≫ g) h).hom.app F ≫
      (boundedBelowPullbackComposition f g).hom.app ((boundedBelowInverseImage h).obj F) ≫
      (boundedBelowInverseImage f).map ((boundedBelowPullbackComposition g h).inv.app F) =
      (boundedBelowPullbackComposition f (g ≫ h)).hom.app F := by
  rw [reassoc_of% (show _ = _ from bounded_assoc f g h F), ← (boundedBelowInverseImage f).map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  exact comp_id _

include bounded_assoc in
@[reassoc]
private theorem bounded_reassociate_right {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : BoundedBelow Z) :
    (boundedBelowPullbackComposition f (g ≫ h)).hom.app F ≫
      (boundedBelowInverseImage f).map ((boundedBelowPullbackComposition g h).hom.app F) ≫
      (boundedBelowPullbackComposition f g).inv.app ((boundedBelowInverseImage h).obj F) =
      (boundedBelowPullbackComposition (f ≫ g) h).hom.app F := by
  rw [← reassoc_of% (show _ = _ from bounded_assoc f g h F), Iso.hom_inv_id_app]
  exact comp_id _

set_option maxHeartbeats 500000 in
private theorem bounded_square_hom {U X V Y : TopCat.{u}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V}
    (h : j ≫ e = v ≫ k) (F : BoundedBelow Y) :
    (pullbackSquare h).hom.app F = (boundedBelowPullbackComposition j e).inv.app F ≫
      boundedTransport h F ≫ (boundedBelowPullbackComposition v k).hom.app F := by
  let opening := congrArg (fun x => x.hom.app F) (square_expansion h)
  let form := square_comparison_app (boundedBelowPullbackComposition j e)
    (congrArg (fun t => boundedBelowInverseImage t) h) (boundedBelowPullbackComposition v k) F
  exact opening.trans form

include bounded_assoc in
private theorem pasteBoundedHorizontal : BoundedBelowSquareHorizontalPasting.{u} := by
  intro U X A V Y B j j' k k' v e e' h h' F
  simp only [bounded_square_hom, CategoryTheory.Functor.map_comp, assoc]
  apply (cancel_epi ((boundedBelowPullbackComposition (j ≫ j') e').hom.app F)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [bounded_reassociate_left_assoc bounded_assoc, bounded_comparison_transport_right_assoc,
    bounded_reassociate_right_assoc bounded_assoc,
    bounded_comparison_transport_left_assoc, bounded_reassociate_left bounded_assoc]
  conv_rhs => rw [← assoc, bounded_transport_trans]

include bounded_assoc in
private theorem pasteBoundedVertical : BoundedBelowSquareVerticalPasting.{u} := by
  intro U X V Y A B j k m v e v' e' h h' F
  simp only [bounded_square_hom, CategoryTheory.Functor.map_comp, assoc]
  apply (cancel_epi ((boundedBelowPullbackComposition j (e ≫ e')).hom.app F)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [bounded_reassociate_right_assoc bounded_assoc, bounded_comparison_transport_left_assoc,
    bounded_reassociate_left_assoc bounded_assoc,
    bounded_comparison_transport_right_assoc, bounded_reassociate_right bounded_assoc]
  conv_rhs => rw [← assoc, bounded_transport_trans]

end BoundedSpecialization

private theorem bounded_composition_assoc {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : BoundedBelow Z) :
    (boundedBelowPullbackComposition (f ≫ g) h).hom.app F ≫
        (boundedBelowPullbackComposition f g).hom.app ((boundedBelowInverseImage h).obj F) =
      (boundedBelowPullbackComposition f (g ≫ h)).hom.app F ≫
        (boundedBelowInverseImage f).map ((boundedBelowPullbackComposition g h).hom.app F) := by
  apply ObjectProperty.hom_ext
  exact composition_assoc f g h F.obj

theorem boundedBelowSquareHorizontalPasting : BoundedBelowSquareHorizontalPasting.{u} :=
  pasteBoundedHorizontal @bounded_composition_assoc

theorem boundedBelowSquareVerticalPasting : BoundedBelowSquareVerticalPasting.{u} :=
  pasteBoundedVertical @bounded_composition_assoc

end RepTheorySurvey.Geometric.DerivedPullbackPasting
