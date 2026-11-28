import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace RepTheorySurvey.Geometric.ClosedEquivarianceExtension

open Analytic Analytic.IntersectionComplex LocalSheaf ClosedEquivarianceExtensionSpecs

open private closedInverseAdjunction pullbackStalkIso pullbackEquivalence
  embeddingIsoOfRange embeddingIsoOfRange_comp
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 250000

private theorem inverseImageComposition_assoc {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Sheaves Z) :
    (inverseImageComposition f (g ≫ h)).hom.app F ≫
        (inverseImage f).map ((inverseImageComposition g h).hom.app F) =
      (inverseImageComposition (f ≫ g) h).hom.app F ≫
        (inverseImageComposition f g).hom.app ((inverseImage h).obj F) := by
  let a := @inverseDirectAdjunction.{u}
  let c₁ := (inverseImageComposition f (g ≫ h)).hom.app F
  let c₂ := (inverseImageComposition g h).hom.app F
  let d₁ := (inverseImageComposition (f ≫ g) h).hom.app F
  let d₂ := (inverseImageComposition f g).hom.app ((inverseImage h).obj F)
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app (a (f ≫ g ≫ h))
    ((a (g ≫ h)).comp (a f)) F
  have h₂ := Adjunction.unit_leftAdjointUniq_hom_app (a (g ≫ h))
    ((a h).comp (a g)) F
  have h₃ := Adjunction.unit_leftAdjointUniq_hom_app (a ((f ≫ g) ≫ h))
    ((a h).comp (a (f ≫ g))) F
  have h₄ := Adjunction.unit_leftAdjointUniq_hom_app (a (f ≫ g))
    ((a g).comp (a f)) ((inverseImage h).obj F)
  change (a (f ≫ g ≫ h)).unit.app F ≫ (directImage (f ≫ g ≫ h)).map c₁ = _ at h₁
  change (a (g ≫ h)).unit.app F ≫ (directImage (g ≫ h)).map c₂ = _ at h₂
  change (a (f ≫ g ≫ h)).unit.app F ≫ (directImage (f ≫ g ≫ h)).map d₁ = _ at h₃
  change (a (f ≫ g)).unit.app _ ≫ (directImage (f ≫ g)).map d₂ = _ at h₄
  change c₁ ≫ (inverseImage f).map c₂ = d₁ ≫ d₂
  apply ((a (f ≫ g ≫ h)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, h₁, h₃,
    Adjunction.comp_unit_app]
  change
    (((a (g ≫ h)).unit.app F ≫
        (directImage (g ≫ h)).map ((a f).unit.app ((inverseImage (g ≫ h)).obj F))) ≫
      (directImage (g ≫ h)).map ((directImage f).map ((inverseImage f).map c₂))) =
    (((a h).unit.app F ≫ (directImage h).map ((a (f ≫ g)).unit.app ((inverseImage h).obj F))) ≫
      (directImage h).map ((directImage (f ≫ g)).map d₂))
  have hn : (a f).unit.app ((inverseImage (g ≫ h)).obj F) ≫
        (directImage f).map ((inverseImage f).map c₂) =
      c₂ ≫ (a f).unit.app ((inverseImage h ⋙ inverseImage g).obj F) :=
    ((a f).unit.naturality c₂).symm
  have h₂' := h₂.trans (Adjunction.comp_unit_app (a h) (a g) F)
  have h₄' := h₄.trans (Adjunction.comp_unit_app (a g) (a f) ((inverseImage h).obj F))
  erw [Category.assoc, ← Functor.map_comp, hn, Functor.map_comp, ← Category.assoc, h₂']
  have hright := congrArg (fun v => (a h).unit.app F ≫ (directImage h).map v) h₄'
  simp only [Functor.map_comp] at hright
  erw [Category.assoc, Category.assoc]
  exact hright.symm

private theorem adjointSquareMap_change {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
    {S : C ⥤ A} {R : D ⥤ B}
    (α : E ⋙ J ≅ K ⋙ V) (a a' : J ⊣ S) (b b' : K ⊣ R) (F : D) :
    adjointSquareMap α a' b' F =
      E.map ((b.rightAdjointUniq b').inv.app F) ≫ adjointSquareMap α a b F ≫
        (a.rightAdjointUniq a').hom.app (V.obj F) := by
  let p := (b.rightAdjointUniq b').inv.app F
  have hp : K.map p ≫ b.counit.app F = b'.counit.app F := by
    dsimp [p]
    rw [Adjunction.rightAdjointUniq_inv_app, Adjunction.rightAdjointUniq_hom_app_counit]
  apply (a'.homEquiv _ _).symm.injective
  rw [adjointSquareMap, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc, Adjunction.rightAdjointUniq_hom_app_counit]
  have ha : J.map (adjointSquareMap α a b F) ≫ a.counit.app (V.obj F) =
      α.hom.app (R.obj F) ≫ V.map (b.counit.app F) := by
    exact (a.homEquiv_counit _ _ _).symm.trans ((a.homEquiv _ _).symm_apply_apply _)
  have hn : J.map (E.map p) ≫ α.hom.app (R.obj F) =
      α.hom.app (R.obj F) ≫ V.map (K.map p) := α.hom.naturality p
  rw [ha, ← Category.assoc, hn, Category.assoc]
  rw [← Functor.map_comp, hp]


private abbrev cochainPullback {X Y : TopCat.{u}} (f : X ⟶ Y) :=
  (inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)

private abbrev pullbackFactor {X Y : TopCat.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaves Y) ℤ) :=
  (inverseImage f).mapDerivedCategoryFactors.app K

@[reassoc]
private theorem derivedComposition_factor {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex (Sheaves Z) ℤ) :
    (derivedInverseImageComposition f g).hom.app (DerivedCategory.Q.obj K) ≫
        (derivedInverseImage f).map (pullbackFactor g K).hom ≫
        (pullbackFactor f ((cochainPullback g).obj K)).hom =
      (pullbackFactor (f ≫ g) K).hom ≫
        DerivedCategory.Q.map (((inverseImageComposition f g).hom.mapHomologicalComplex _).app K) := by
  let L := inverseImage g
  let M := inverseImage f
  let e := Functor.mapDerivedCategoryCompIso L M
  have he : e.hom.app (DerivedCategory.Q.obj K) ≫ (L ⋙ M).mapDerivedCategoryFactors.hom.app K =
      (derivedInverseImage f).map (pullbackFactor g K).hom ≫
        (pullbackFactor f ((cochainPullback g).obj K)).hom := by
    dsimp only [e]
    rw [Functor.mapDerivedCategoryCompIso_hom_app_Q_obj]
    have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ M))
        (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := by
      ext n
      rfl
    change _ = 𝟙 (((L ⋙ M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) at hi
    erw [hi, CategoryTheory.Functor.map_id]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.id_comp, Category.comp_id]
    rfl
  rw [← he]
  unfold derivedInverseImageComposition
  dsimp only [e, L, M]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  change ((inverseImageComposition f g).hom.mapDerivedCategory.app (DerivedCategory.Q.obj K)) ≫
      (L ⋙ M).mapDerivedCategoryFactors.hom.app K = _
  rw [NatTrans.mapDerivedCategory_app_Q_obj]
  dsimp only [L, M]
  simp

private abbrev compComparison {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Derived Z) :=
  (derivedInverseImageComposition f g).hom.app F

private abbrev cochainComparison {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex (Sheaves Z) ℤ) :=
  ((inverseImageComposition f g).hom.mapHomologicalComplex (ComplexShape.up ℤ)).app K

set_option maxHeartbeats 1200000 in
private theorem derivedComposition_assoc {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Derived Z) :
    compComparison f (g ≫ h) F ≫ (derivedInverseImage f).map (compComparison g h F) =
      compComparison (f ≫ g) h F ≫ compComparison f g ((derivedInverseImage h).obj F) := by
  let L : derivedInverseImage (f ≫ g ≫ h) ⟶
      derivedInverseImage h ⋙ derivedInverseImage g ⋙ derivedInverseImage f :=
    (derivedInverseImageComposition f (g ≫ h)).hom ≫
      Functor.whiskerRight (derivedInverseImageComposition g h).hom (derivedInverseImage f)
  let R : derivedInverseImage (f ≫ g ≫ h) ⟶
      derivedInverseImage h ⋙ derivedInverseImage g ⋙ derivedInverseImage f :=
    (derivedInverseImageComposition (f ≫ g) h).hom ≫
      Functor.whiskerLeft (derivedInverseImage h) (derivedInverseImageComposition f g).hom
  suffices he : L = R from congrArg (fun v => v.app F) he
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaves Z) (ComplexShape.up ℤ))
  intro K
  let Q := DerivedCategory.Q.obj K
  let Kh := (cochainPullback h).obj K
  let Kgh := (cochainPullback g).obj Kh
  let c := (derivedInverseImage f).map ((derivedInverseImage g).map (pullbackFactor h K).hom) ≫
    (derivedInverseImage f).map (pullbackFactor g Kh).hom ≫ (pullbackFactor f Kgh).hom
  haveI : IsIso c := by dsimp only [c]; infer_instance
  apply (cancel_mono c).mp
  change (compComparison f (g ≫ h) Q ≫ (derivedInverseImage f).map (compComparison g h Q)) ≫ c =
    (compComparison (f ≫ g) h Q ≫ compComparison f g ((derivedInverseImage h).obj Q)) ≫ c
  have hnat := (derivedInverseImageComposition f g).hom.naturality (pullbackFactor h K).hom
  change (derivedInverseImage (f ≫ g)).map (pullbackFactor h K).hom ≫
      compComparison f g (DerivedCategory.Q.obj Kh) =
    compComparison f g ((derivedInverseImage h).obj Q) ≫
      (derivedInverseImage f).map ((derivedInverseImage g).map (pullbackFactor h K).hom) at hnat
  have hfactor : (derivedInverseImage f).map (DerivedCategory.Q.map (cochainComparison g h K)) ≫
      (pullbackFactor f Kgh).hom =
    (pullbackFactor f ((cochainPullback (g ≫ h)).obj K)).hom ≫
      DerivedCategory.Q.map ((cochainPullback f).map (cochainComparison g h K)) :=
    (inverseImage f).mapDerivedCategoryFactors_hom_naturality (cochainComparison g h K)
  have hcochain :
      cochainComparison f (g ≫ h) K ≫ (cochainPullback f).map (cochainComparison g h K) =
        cochainComparison (f ≫ g) h K ≫ cochainComparison f g Kh := by
    ext n
    exact inverseImageComposition_assoc f g h (K.X n)
  simp only [c, Category.assoc]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  erw [derivedComposition_factor g h K, (derivedInverseImage f).map_comp]
  simp only [Category.assoc]
  erw [hfactor, derivedComposition_factor_assoc f (g ≫ h) K,
    ← reassoc_of% hnat, derivedComposition_factor f g Kh,
    derivedComposition_factor_assoc (f ≫ g) h K]
  erw [← Functor.map_comp, ← Functor.map_comp, hcochain]
  rfl


private def compositionAt {W Y X : TopCat.{u}} (k : W ⟶ Y) (f : Y ⟶ X)
    {f' : W ⟶ X} (h : k ≫ f = f') (F : Derived X) :
    (derivedInverseImage f').obj F ≅ (derivedInverseImage k).obj ((derivedInverseImage f).obj F) :=
  eqToIso (congrArg (fun t => (derivedInverseImage t).obj F) h.symm) ≪≫
    (derivedInverseImageComposition k f).app F

private theorem pullbackMorphism_eq {W Y X : TopCat.{u}} {f g : Y ⟶ X} {F : Derived X}
    (k : W ⟶ Y) {f' g' : W ⟶ X} (hf : k ≫ f = f') (hg : k ≫ g = g')
    (v : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F) :
    pullbackMorphism k hf hg v =
      (compositionAt k f hf F).hom ≫ (derivedInverseImage k).map v ≫
        (compositionAt k g hg F).inv := by
  subst f' g'
  simp [pullbackMorphism, compositionAt]

private theorem pullbackMorphism_id {W Y X : TopCat.{u}} {f : Y ⟶ X} {F : Derived X}
    (k : W ⟶ Y) {f' : W ⟶ X} (hf : k ≫ f = f') :
    pullbackMorphism k hf hf (𝟙 ((derivedInverseImage f).obj F)) = 𝟙 _ := by
  rw [pullbackMorphism_eq]
  simp

private theorem pullbackMorphism_comp {W Y X : TopCat.{u}} {f g t : Y ⟶ X} {F : Derived X}
    (k : W ⟶ Y) {f' g' t' : W ⟶ X} (hf : k ≫ f = f') (hg : k ≫ g = g')
    (ht : k ≫ t = t')
    (v : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F)
    (w : (derivedInverseImage g).obj F ⟶ (derivedInverseImage t).obj F) :
    pullbackMorphism k hf ht (v ≫ w) =
      pullbackMorphism k hf hg v ≫ pullbackMorphism k hg ht w := by
  simp only [pullbackMorphism_eq, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

@[reassoc]
private theorem compositionAt_paste {V W Y X : TopCat.{u}} (l : V ⟶ W) (k : W ⟶ Y) (f : Y ⟶ X)
    {f' : W ⟶ X} {f'' : V ⟶ X}
    (hk : k ≫ f = f') (hl : l ≫ f' = f'') (hkl : (l ≫ k) ≫ f = f'') (F : Derived X) :
    (compositionAt l f' hl F).hom ≫ (derivedInverseImage l).map (compositionAt k f hk F).hom =
      (compositionAt (l ≫ k) f hkl F).hom ≫ compComparison l k ((derivedInverseImage f).obj F) := by
  subst f' f''
  simpa [compositionAt] using derivedComposition_assoc l k f F

private theorem pullbackMorphism_paste {V W Y X : TopCat.{u}} {f g : Y ⟶ X} {F : Derived X}
    (l : V ⟶ W) (k : W ⟶ Y) {f' g' : W ⟶ X} {f'' g'' : V ⟶ X}
    (hkf : k ≫ f = f') (hkg : k ≫ g = g') (hlf : l ≫ f' = f'') (hlg : l ≫ g' = g'')
    (hf : (l ≫ k) ≫ f = f'') (hg : (l ≫ k) ≫ g = g'')
    (v : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F) :
    pullbackMorphism l hlf hlg (pullbackMorphism k hkf hkg v) =
      pullbackMorphism (l ≫ k) hf hg v := by
  apply (cancel_mono ((compositionAt l g' hlg F).hom ≫
    (derivedInverseImage l).map (compositionAt k g hkg F).hom)).mp
  have hn := (derivedInverseImageComposition l k).hom.naturality v
  change (derivedInverseImage (l ≫ k)).map v ≫ compComparison l k ((derivedInverseImage g).obj F) =
    compComparison l k ((derivedInverseImage f).obj F) ≫
      (derivedInverseImage l).map ((derivedInverseImage k).map v) at hn
  simp only [pullbackMorphism_eq, Category.assoc, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
  rw [(derivedInverseImage l).map_comp]
  rw [compositionAt_paste_assoc l k f hkf hlf hf,
    compositionAt_paste l k g hkg hlg hg, Iso.inv_hom_id_assoc, hn]


private def restrictionComparison {V U X : TopCat.{u}} (i : U ⟶ X) (v : V ⟶ U)
    {G : Derived X} {F : Derived U} (ε : (derivedInverseImage i).obj G ⟶ F) :
    (derivedInverseImage (v ≫ i)).obj G ⟶ (derivedInverseImage v).obj F :=
  compComparison v i G ≫ (derivedInverseImage v).map ε

private theorem restrictionComparison_isIso {V U X : TopCat.{u}} (i : U ⟶ X) (v : V ⟶ U)
    {G : Derived X} {F : Derived U} (ε : (derivedInverseImage i).obj G ⟶ F) [IsIso ε] :
    IsIso (restrictionComparison i v ε) := by
  unfold restrictionComparison compComparison
  infer_instance

@[reassoc]
private theorem restrictionComparison_paste {W V U X : TopCat.{u}}
    (i : U ⟶ X) (v : V ⟶ U) (k : W ⟶ V) {w : W ⟶ U} (hw : k ≫ v = w)
    (hw' : k ≫ (v ≫ i) = w ≫ i) {G : Derived X} {F : Derived U}
    (ε : (derivedInverseImage i).obj G ⟶ F) :
    (compositionAt k (v ≫ i) hw' G).hom ≫ (derivedInverseImage k).map (restrictionComparison i v ε) =
      restrictionComparison i w ε ≫ (compositionAt k v hw F).hom := by
  subst w
  simp only [compositionAt, restrictionComparison, eqToIso_refl, Iso.refl_trans]
  change compComparison k (v ≫ i) G ≫
      (derivedInverseImage k).map (compComparison v i G ≫ (derivedInverseImage v).map ε) =
    (compComparison (k ≫ v) i G ≫ (derivedInverseImage (k ≫ v)).map ε) ≫ compComparison k v F
  have hn := (derivedInverseImageComposition k v).hom.naturality ε
  change (derivedInverseImage (k ≫ v)).map ε ≫ compComparison k v F =
    compComparison k v ((derivedInverseImage i).obj G) ≫
      (derivedInverseImage k).map ((derivedInverseImage v).map ε) at hn
  rw [(derivedInverseImage k).map_comp]
  let t := (derivedInverseImage k).map ((derivedInverseImage v).map ε)
  calc
    _ = (compComparison k (v ≫ i) G ≫ (derivedInverseImage k).map (compComparison v i G)) ≫ t :=
      (Category.assoc _ _ _).symm
    _ = (compComparison (k ≫ v) i G ≫ compComparison k v ((derivedInverseImage i).obj G)) ≫ t :=
      congrArg (· ≫ t) (derivedComposition_assoc k v i G)
    _ = compComparison (k ≫ v) i G ≫ ((derivedInverseImage (k ≫ v)).map ε ≫ compComparison k v F) :=
      (Category.assoc _ _ _).trans (congrArg (compComparison (k ≫ v) i G ≫ ·) hn.symm)
    _ = _ := (Category.assoc _ _ _).symm

private theorem restrictionComparison_pullback {W V U X : TopCat.{u}}
    (i : U ⟶ X) (k : W ⟶ V) {v t : V ⟶ U} {v' t' : W ⟶ U}
    (hv : k ≫ v = v') (ht : k ≫ t = t')
    (hv' : k ≫ (v ≫ i) = v' ≫ i) (ht' : k ≫ (t ≫ i) = t' ≫ i)
    {G : Derived X} {F : Derived U} (ε : (derivedInverseImage i).obj G ⟶ F)
    {α : (derivedInverseImage (v ≫ i)).obj G ⟶ (derivedInverseImage (t ≫ i)).obj G}
    {β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage t).obj F}
    (h : α ≫ restrictionComparison i t ε = restrictionComparison i v ε ≫ β) :
    pullbackMorphism k hv' ht' α ≫ restrictionComparison i t' ε =
      restrictionComparison i v' ε ≫ pullbackMorphism k hv ht β := by
  apply (cancel_mono (compositionAt k t ht F).hom).mp
  simp only [pullbackMorphism_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← restrictionComparison_paste i t k ht ht' ε, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, h, Functor.map_comp, ← restrictionComparison_paste_assoc i v k hv hv' ε]

private theorem pullbackMorphism_congr {W Y X : TopCat.{u}} {f g : Y ⟶ X} {F : Derived X}
    {k l : W ⟶ Y} (h : k = l) {f' g' : W ⟶ X}
    (hkf : k ≫ f = f') (hkg : k ≫ g = g') (hlf : l ≫ f = f') (hlg : l ≫ g = g')
    (v : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F) :
    pullbackMorphism k hkf hkg v = pullbackMorphism l hlf hlg v := by
  subst l
  rfl

private def RestrictsTo {U X V W : TopCat.{u}} (i : U ⟶ X) (j : V ⟶ W)
    {e p : W ⟶ X} {v q : V ⟶ U} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {G : Derived X} {F : Derived U} (ε : (derivedInverseImage i).obj G ⟶ F)
    (α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G)
    (β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F) : Prop :=
  pullbackMorphism j he hp α ≫ restrictionComparison i q ε =
    restrictionComparison i v ε ≫ β

private theorem restrictsTo_id {U X V W : TopCat.{u}} (i : U ⟶ X) (j : V ⟶ W)
    {e : W ⟶ X} {v : V ⟶ U} (he : j ≫ e = v ≫ i)
    {G : Derived X} {F : Derived U} (ε : (derivedInverseImage i).obj G ⟶ F) :
    RestrictsTo i j he he ε (𝟙 _) (𝟙 _) := by
  simp [RestrictsTo, pullbackMorphism_id]

private theorem RestrictsTo.comp {U X V W : TopCat.{u}} {i : U ⟶ X} {j : V ⟶ W}
    {e p t : W ⟶ X} {v q s : V ⟶ U}
    {he : j ≫ e = v ≫ i} {hp : j ≫ p = q ≫ i} {ht : j ≫ t = s ≫ i}
    {G : Derived X} {F : Derived U} {ε : (derivedInverseImage i).obj G ⟶ F}
    {α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G}
    {α' : (derivedInverseImage p).obj G ⟶ (derivedInverseImage t).obj G}
    {β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F}
    {β' : (derivedInverseImage q).obj F ⟶ (derivedInverseImage s).obj F}
    (h : RestrictsTo i j he hp ε α β) (h' : RestrictsTo i j hp ht ε α' β') :
    RestrictsTo i j he ht ε (α ≫ α') (β ≫ β') := by
  unfold RestrictsTo at h h' ⊢
  rw [pullbackMorphism_comp j he hp ht, Category.assoc, h', ← Category.assoc, h, Category.assoc]

private theorem RestrictsTo.pullback {U X V W V' W' : TopCat.{u}}
    {i : U ⟶ X} {j : V ⟶ W} {j' : V' ⟶ W'} (k : W' ⟶ W) (l : V' ⟶ V)
    (hl : j' ≫ k = l ≫ j)
    {e p : W ⟶ X} {v q : V ⟶ U} {e' p' : W' ⟶ X} {v' q' : V' ⟶ U}
    {he : j ≫ e = v ≫ i} {hp : j ≫ p = q ≫ i}
    (hke : k ≫ e = e') (hkp : k ≫ p = p') (hlv : l ≫ v = v') (hlq : l ≫ q = q')
    (he' : j' ≫ e' = v' ≫ i) (hp' : j' ≫ p' = q' ≫ i)
    {G : Derived X} {F : Derived U} {ε : (derivedInverseImage i).obj G ⟶ F}
    {α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G}
    {β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F}
    (h : RestrictsTo i j he hp ε α β) :
    RestrictsTo i j' he' hp' ε (pullbackMorphism k hke hkp α) (pullbackMorphism l hlv hlq β) := by
  have hcv : l ≫ (v ≫ i) = v' ≫ i := congrArg (· ≫ i) hlv
  have hcq : l ≫ (q ≫ i) = q' ≫ i := congrArg (· ≫ i) hlq
  have h₁ : (j' ≫ k) ≫ e = v' ≫ i := (congrArg (j' ≫ ·) hke).trans he'
  have h₂ : (j' ≫ k) ≫ p = q' ≫ i := (congrArg (j' ≫ ·) hkp).trans hp'
  have h₃ : (l ≫ j) ≫ e = v' ≫ i := (congrArg (l ≫ ·) he).trans hcv
  have h₄ : (l ≫ j) ≫ p = q' ≫ i := (congrArg (l ≫ ·) hp).trans hcq
  unfold RestrictsTo
  rw [pullbackMorphism_paste j' k hke hkp he' hp' h₁ h₂,
    pullbackMorphism_congr hl h₁ h₂ h₃ h₄,
    ← pullbackMorphism_paste l j he hp hcv hcq h₃ h₄]
  exact restrictionComparison_pullback i l hlv hlq hcv hcq ε h


private theorem isIso_closed_counit {X : TopCat.{u}} {Z : Set X} {hZ : IsClosed Z}
    (b : boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ)
    (F : BoundedBelow (TopCat.of Z)) : IsIso (b.counit.app F) := by
  let ff := Classical.choice (DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hZ)
  letI := ff.full
  letI := ff.faithful
  infer_instance

private theorem closedInclusion_map_injective {X : TopCat.{u}} {S : Set X} (hS : IsClosed S)
    {F G : BoundedBelow X} (hG : DerivedSupportedOn S G) {v w : F ⟶ G}
    (h : (boundedBelowInverseImage (closedInclusion S)).map v =
      (boundedBelowInverseImage (closedInclusion S)).map w) : v = w := by
  let a := closedInverseAdjunction hS
  let ff := Classical.choice (DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hS)
  letI := ff.full
  letI := ff.faithful
  haveI : IsIso (a.unit.app G) :=
    (a.isIso_unit_app_iff_mem_essImage).mpr
      ((DerivedLocalSheaves.derivedSupportedEssentialImage hS G).mpr hG)
  apply (cancel_mono (a.unit.app G)).mp
  have hn (t : F ⟶ G) : t ≫ a.unit.app G = a.unit.app F ≫
      (closedExtensionPlus hS).map ((boundedBelowInverseImage (closedInclusion S)).map t) :=
    a.unit.naturality t
  rw [hn, hn, h]

private theorem closedEmbedding_map_injective {U X : TopCat.{u}} {j : U ⟶ X}
    (hj : IsClosedEmbedding j) {F G : BoundedBelow X} (hG : DerivedSupportedOn (Set.range j) G)
    {v w : F ⟶ G} (h : (boundedBelowInverseImage j).map v =
      (boundedBelowInverseImage j).map w) : v = w := by
  let i := closedInclusion (Set.range j)
  let e := embeddingIsoOfRange j i hj.isEmbedding IsEmbedding.subtypeVal Subtype.range_coe.symm
  have he : e.hom ≫ i = j := embeddingIsoOfRange_comp _ _ _ _ _
  have h' : (boundedBelowInverseImage (e.hom ≫ i)).map v =
      (boundedBelowInverseImage (e.hom ≫ i)).map w := by rw [he, h]
  let c := (boundedBelowPullbackComposition e.hom i).hom
  have hn (t : F ⟶ G) : (boundedBelowInverseImage (e.hom ≫ i)).map t ≫ c.app G =
      c.app F ≫ (boundedBelowInverseImage e.hom).map ((boundedBelowInverseImage i).map t) :=
    c.naturality t
  letI : (boundedBelowInverseImage e.hom).IsEquivalence := (pullbackEquivalence e).isEquivalence_functor
  apply closedInclusion_map_injective hj.isClosed_range hG
  apply (boundedBelowInverseImage e.hom).map_injective
  apply (cancel_epi (c.app F)).mp
  rw [← hn, ← hn, h']

private theorem restrictsTo_injective {U X V W : TopCat.{u}} {i : U ⟶ X} {j : V ⟶ W}
    (hj : IsClosedEmbedding j) {e p : W ⟶ X} {v q : V ⟶ U}
    {he : j ≫ e = v ≫ i} {hp : j ≫ p = q ≫ i}
    {G : BoundedBelow X} {F : Derived U} {ε : (derivedInverseImage i).obj G.obj ⟶ F}
    [IsIso ε] (hG : DerivedSupportedOn (Set.range j) ((boundedBelowInverseImage p).obj G))
    {α α' : (derivedInverseImage e).obj G.obj ⟶ (derivedInverseImage p).obj G.obj}
    {β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F}
    (h : RestrictsTo i j he hp ε α β) (h' : RestrictsTo i j he hp ε α' β) : α = α' := by
  haveI := restrictionComparison_isIso i q ε
  have hr := (cancel_mono (restrictionComparison i q ε)).mp (h.trans h'.symm)
  simp only [pullbackMorphism_eq] at hr
  have hm := (cancel_mono (compositionAt j p hp G.obj).inv).mp
    ((cancel_epi (compositionAt j e he G.obj).hom).mp hr)
  let x : (boundedBelowInverseImage e).obj G ⟶ (boundedBelowInverseImage p).obj G :=
    ObjectProperty.homMk α
  let y : (boundedBelowInverseImage e).obj G ⟶ (boundedBelowInverseImage p).obj G :=
    ObjectProperty.homMk α'
  have hm' : (boundedBelowInverseImage j).map x = (boundedBelowInverseImage j).map y :=
    ObjectProperty.hom_ext _ hm
  exact congrArg (fun f => f.hom) (closedEmbedding_map_injective hj hG hm')

private theorem pullbackExtension_supported {X W : TopCat.{u}} {Z : Set X} {hZ : IsClosed Z}
    (p : W ⟶ X) (F : BoundedBelow (TopCat.of Z)) :
    DerivedSupportedOn (p ⁻¹' Z) ((boundedBelowInverseImage p).obj ((closedExtensionPlus hZ).obj F)) := by
  let G := (closedExtensionPlus hZ).obj F
  have hG := (DerivedLocalSheaves.derivedSupportedEssentialImage hZ G).mp ⟨F, ⟨Iso.refl G⟩⟩
  intro n x hx
  exact (hG n (p x) hx).of_iso (pullbackStalkIso p G n x)

private theorem parameterInclusion_closed (H : AnalyticGroup.{u}) {Y X : TopCat.{u}}
    {i : Y ⟶ X} (hi : IsClosedEmbedding i) : IsClosedEmbedding (parameterInclusion H i) := by
  have hid : IsClosedEmbedding (@id H.space) :=
    ⟨IsEmbedding.id, by simpa only [Set.range_id] using isClosed_univ⟩
  exact hid.prodMap hi

@[reassoc]
private theorem adjointSquareMap_counit {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
    {S : C ⥤ A} {R : D ⥤ B}
    (α : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R) (F : D) :
    J.map (adjointSquareMap α a b F) ≫ a.counit.app (V.obj F) =
      α.hom.app (R.obj F) ≫ V.map (b.counit.app F) :=
  (a.homEquiv_counit _ _ _).symm.trans ((a.homEquiv _ _).symm_apply_apply _)

private theorem pullbackFunctorEq_app_hom {X Y : TopCat.{u}} {e e' : X ⟶ Y}
    (h : e = e') (G : BoundedBelow Y) :
    ((eqToIso (congrArg (fun f => boundedBelowInverseImage f) h)).hom.app G).hom =
      eqToHom (congrArg (fun f => (derivedInverseImage f).obj G.obj) h) := by
  subst e'
  rfl

private theorem compositionAt_inv {W Y X : TopCat.{u}} (k : W ⟶ Y) (f : Y ⟶ X)
    {f' : W ⟶ X} (h : k ≫ f = f') (F : Derived X) :
    (compositionAt k f h F).inv =
      (derivedInverseImageComposition k f).inv.app F ≫
        eqToHom (congrArg (fun t => (derivedInverseImage t).obj F) h) := by
  subst f'
  simp [compositionAt]

private theorem pullbackSquare_hom_formula {U X V W : TopCat.{u}} {i : U ⟶ X} {j : V ⟶ W}
    {e : W ⟶ X} {v : V ⟶ U} (h : j ≫ e = v ≫ i) :
    (pullbackSquare h).hom =
      (boundedBelowPullbackComposition j e).inv ≫
        (eqToIso (congrArg (fun f : V ⟶ X => boundedBelowInverseImage f) h)).hom ≫
          (boundedBelowPullbackComposition v i).hom := rfl

private theorem pullbackSquare_app_hom_expand {U X V W : TopCat.{u}} {i : U ⟶ X} {j : V ⟶ W}
    {e : W ⟶ X} {v : V ⟶ U} (h : j ≫ e = v ≫ i) (G : BoundedBelow X) :
    ((pullbackSquare h).hom.app G).hom =
      ((boundedBelowPullbackComposition j e).inv.app G).hom ≫
        ((eqToIso (congrArg (fun f : V ⟶ X => boundedBelowInverseImage f) h)).hom.app G).hom ≫
          ((boundedBelowPullbackComposition v i).hom.app G).hom := by
  rw [pullbackSquare_hom_formula h]
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]

private theorem belowComposition_inv_hom {X Y Z : TopCat.{u}} (k : X ⟶ Y) (f : Y ⟶ Z)
    (G : BoundedBelow Z) :
    ((boundedBelowPullbackComposition k f).inv.app G).hom =
      (derivedInverseImageComposition k f).inv.app G.obj := rfl

private theorem belowComposition_hom_hom {X Y Z : TopCat.{u}} (k : X ⟶ Y) (f : Y ⟶ Z)
    (G : BoundedBelow Z) :
    ((boundedBelowPullbackComposition k f).hom.app G).hom = compComparison k f G.obj := rfl

private theorem pullbackSquare_app_hom {U X V W : TopCat.{u}} {i : U ⟶ X} {j : V ⟶ W}
    {e : W ⟶ X} {v : V ⟶ U} (h : j ≫ e = v ≫ i) (G : BoundedBelow X) :
    ((pullbackSquare h).hom.app G).hom =
      (compositionAt j e h G.obj).inv ≫ compComparison v i G.obj := by
  rw [pullbackSquare_app_hom_expand h G, belowComposition_inv_hom j e G,
    pullbackFunctorEq_app_hom h G, belowComposition_hom_hom v i G,
    compositionAt_inv j e h G.obj, Category.assoc]


private theorem restrictsTo_of_mates {X V W : TopCat.{u}} {Z : Set X} {hZ : IsClosed Z}
    {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ TopCat.of Z}
    (he : j ≫ e = v ≫ closedInclusion Z) (hp : j ≫ p = q ≫ closedInclusion Z)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ)
    (F : BoundedBelow (TopCat.of Z))
    {α : (boundedBelowInverseImage e).obj ((closedExtensionPlus hZ).obj F) ⟶
      (boundedBelowInverseImage p).obj ((closedExtensionPlus hZ).obj F)}
    {β : (boundedBelowInverseImage v).obj F ⟶ (boundedBelowInverseImage q).obj F}
    (h : α ≫ adjointSquareMap (pullbackSquare hp) a b F =
      adjointSquareMap (pullbackSquare he) a b F ≫ (derivedDirectImage j).map β) :
    RestrictsTo (closedInclusion Z) j he hp (b.counit.app F).hom α.hom β.hom := by
  have hn := a.counit.naturality β
  change (boundedBelowInverseImage j).map ((derivedDirectImage j).map β) ≫
    a.counit.app ((boundedBelowInverseImage q).obj F) =
      a.counit.app ((boundedBelowInverseImage v).obj F) ≫ β at hn
  have hm := congrArg (fun f => (boundedBelowInverseImage j).map f ≫
    a.counit.app ((boundedBelowInverseImage q).obj F)) h
  simp only [Functor.map_comp, Category.assoc] at hm
  rw [adjointSquareMap_counit, hn, adjointSquareMap_counit_assoc] at hm
  let G : Derived X := ((closedExtensionPlus hZ).obj F).obj
  have hm' := congrArg (fun f => f.hom) hm
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackSquare_app_hom, Category.assoc] at hm'
  change (derivedInverseImage j).map α.hom ≫
      (compositionAt j p hp G).inv ≫ compComparison q (closedInclusion Z) G ≫
        (derivedInverseImage q).map (b.counit.app F).hom =
    (compositionAt j e he G).inv ≫ compComparison v (closedInclusion Z) G ≫
      (derivedInverseImage v).map (b.counit.app F).hom ≫ β.hom at hm'
  have hc := congrArg ((compositionAt j e he G).hom ≫ ·) hm'
  simp only [Iso.hom_inv_id_assoc] at hc
  unfold RestrictsTo restrictionComparison
  rw [pullbackMorphism_eq]
  simp only [Category.assoc]
  exact hc


private theorem pasteActionSquare {U X V W V' W' : TopCat.{u}}
    {i : U ⟶ X} {j : V ⟶ W} {j' : V' ⟶ W'} {k : W' ⟶ W} {l : V' ⟶ V}
    {e : W ⟶ X} {v : V ⟶ U} (hkl : j' ≫ k = l ≫ j) (he : j ≫ e = v ≫ i) :
    j' ≫ (k ≫ e) = (l ≫ v) ≫ i :=
  (congrArg (· ≫ e) hkl).trans (congrArg (l ≫ ·) he)

private theorem oneParameter_range {X : TopCat.{u}} (H : AnalyticGroup.{u}) (Z : Set X) :
    Set.range (parameterInclusion H (closedInclusion Z)) =
      (AnalyticAction.projection H X) ⁻¹' Z := by
  ext ⟨g, x⟩
  change (∃ p : H.space × Z, (p.1, p.2.val) = (g, x)) ↔ x ∈ Z
  constructor
  · rintro ⟨⟨h, z⟩, hz⟩
    have hzx : z.val = x := congrArg Prod.snd hz
    exact hzx ▸ z.property
  · intro hx
    exact ⟨(g, ⟨x, hx⟩), rfl⟩

private theorem twoParameters_range {X : TopCat.{u}} (H : AnalyticGroup.{u}) (Z : Set X) :
    Set.range (parameterInclusion H (parameterInclusion H (closedInclusion Z))) =
      (AnalyticAction.multiplyParameters H X ≫ AnalyticAction.projection H X) ⁻¹' Z := by
  ext ⟨g, h, x⟩
  change (∃ p : H.space × (H.space × Z), (p.1, p.2.1, p.2.2.val) = (g, h, x)) ↔ x ∈ Z
  constructor
  · rintro ⟨⟨g', h', z⟩, hz⟩
    have hzx : z.val = x := congrArg (fun p => p.2.2) hz
    exact hzx ▸ z.property
  · intro hx
    exact ⟨(g, h, ⟨x, hx⟩), rfl⟩

/-- Transport the identity and multiplication laws across the closed inclusion. -/
private def extendDatum {H : AnalyticGroup.{u}} {X : TopCat.{u}} {Z : Set X}
    (hZ : IsClosed Z) (A : AnalyticAction H X) (B : AnalyticAction H (TopCat.of Z))
    (hA : parameterInclusion H (closedInclusion Z) ≫ A.act = B.act ≫ closedInclusion Z)
    (b : boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ)
    (F : BoundedBelow (TopCat.of Z)) (β : B.Equivariance F.obj)
    (δ : (derivedInverseImage A.act).obj ((closedExtensionPlus hZ).obj F).obj ≅
      (derivedInverseImage (AnalyticAction.projection H X)).obj ((closedExtensionPlus hZ).obj F).obj)
    (hδ : RestrictsTo (closedInclusion Z) (parameterInclusion H (closedInclusion Z))
      hA (projectionSquare H _) (b.counit.app F).hom δ.hom β.iso.hom) :
    A.Equivariance ((closedExtensionPlus hZ).obj F).obj where
  iso := δ
  identity := by
    let U := TopCat.of Z
    let i := closedInclusion Z
    let j := parameterInclusion H i
    let G := (closedExtensionPlus hZ).obj F
    let ε := (b.counit.app F).hom
    letI : IsIso (b.counit.app F) := isIso_closed_counit b F
    letI : IsIso ε := (DerivedCategory.Plus.ι (C := Sheaves U)).map_isIso (b.counit.app F)
    have hi : i ≫ AnalyticAction.identitySection H X = AnalyticAction.identitySection H U ≫ j :=
      TopCat.ext (fun _ => rfl)
    have hId : i ≫ 𝟙 X = 𝟙 U ≫ i := rfl
    have he := hδ.pullback (AnalyticAction.identitySection H X) (AnalyticAction.identitySection H U)
      hi (AnalyticAction.identity_act A) AnalyticAction.identity_projection
      (AnalyticAction.identity_act B) AnalyticAction.identity_projection hId hId
    rw [β.identity] at he
    have hs : DerivedSupportedOn (Set.range i) ((boundedBelowInverseImage (𝟙 X)).obj G) := by
      rw [show Set.range i = Z from Subtype.range_coe]
      exact pullbackExtension_supported (𝟙 X) F (hZ := hZ)
    exact restrictsTo_injective hZ.isClosedEmbedding_subtypeVal hs he
      (restrictsTo_id i i hId ε)
  multiplication := by
    let U := TopCat.of Z
    let i := closedInclusion Z
    let j := parameterInclusion H i
    let j₂ := parameterInclusion H j
    let G := (closedExtensionPlus hZ).obj F
    let ε := (b.counit.app F).hom
    letI : IsIso (b.counit.app F) := isIso_closed_counit b F
    letI : IsIso ε := (DerivedCategory.Plus.ι (C := Sheaves U)).map_isIso (b.counit.app F)
    let mx := AnalyticAction.multiplyParameters H X
    let mz := AnalyticAction.multiplyParameters H U
    let sx := AnalyticAction.secondParameter H X
    let sz := AnalyticAction.secondParameter H U
    let fx := AnalyticAction.firstAfterSecond A
    let fz := AnalyticAction.firstAfterSecond B
    let px := AnalyticAction.projection H X
    let pz := AnalyticAction.projection H U
    have hm : j₂ ≫ mx = mz ≫ j := TopCat.ext (fun _ => rfl)
    have hs : j₂ ≫ sx = sz ≫ j := TopCat.ext (fun _ => rfl)
    have hf : j₂ ≫ fx = fz ≫ j := TopCat.ext (fun ⟨g, h, z⟩ =>
      congrArg (g, ·) (congrArg (fun f : AnalyticAction.Parameters H U ⟶ X => f (h, z)) hA))
    have he : j₂ ≫ (mx ≫ A.act) = (mz ≫ B.act) ≫ i := pasteActionSquare hm hA
    have hp : j₂ ≫ (mx ≫ px) = (mz ≫ pz) ≫ i := pasteActionSquare hm (projectionSquare H i)
    have ht : j₂ ≫ (sx ≫ A.act) = (sz ≫ B.act) ≫ i := pasteActionSquare hs hA
    have hm' := hδ.pullback mx mz hm rfl rfl rfl rfl he hp
    have hf' := hδ.pullback fx fz hf (AnalyticAction.multiply_act A) (AnalyticAction.first_projection A)
      (AnalyticAction.multiply_act B) (AnalyticAction.first_projection B) he ht
    have hs' := hδ.pullback sx sz hs rfl (AnalyticAction.multiply_projection (H := H) (X := X))
      rfl (AnalyticAction.multiply_projection (H := H) (X := U)) ht hp
    have hc := hf'.comp hs'
    rw [← β.multiplication] at hc
    have hG : DerivedSupportedOn (Set.range j₂) ((boundedBelowInverseImage (mx ≫ px)).obj G) := by
      rw [twoParameters_range H Z]
      exact pullbackExtension_supported _ F
    exact restrictsTo_injective
      (parameterInclusion_closed H (parameterInclusion_closed H hZ.isClosedEmbedding_subtypeVal))
      hG hm' hc


theorem closedEquivarianceExtension : ClosedEquivarianceExtensionSpecs.ClosedEquivarianceExtension.{u} := by
  intro J X Z hZ A B h a b F β hIso
  let U := TopCat.of Z
  let i := closedInclusion Z
  let G := (closedExtensionPlus hZ).obj F
  let ε := (b.counit.app F).hom
  letI : IsIso (b.counit.app F) := isIso_closed_counit b F
  letI : IsIso ε := (DerivedCategory.Plus.ι (C := Sheaves U)).map_isIso (b.counit.app F)
  let A' := above A B.cutoff
  let hz (k : ℕ) (hk : A'.cutoff ≤ k) : B.cutoff ≤ k := (le_max_right _ _).trans hk
  let hx (k : ℕ) (hk : A'.cutoff ≤ k) : A.cutoff ≤ k := (le_max_left _ _).trans hk
  let j (k : ℕ) := parameterInclusion (J.group k) i
  let βPlus (k : ℕ) (hk : A'.cutoff ≤ k) :
      (boundedBelowInverseImage (B.action k (hz k hk)).act).obj F ≅
        (boundedBelowInverseImage (AnalyticAction.projection (J.group k) U)).obj F :=
    ObjectProperty.isoMk _ (β.datum k (hz k hk)).iso
  let δPlus (k : ℕ) (hk : A'.cutoff ≤ k) :
      (boundedBelowInverseImage (A'.action k hk).act).obj G ≅
        (boundedBelowInverseImage (AnalyticAction.projection (J.group k) X)).obj G := by
    haveI := (hIso k hk).1
    haveI := (hIso k hk).2
    exact asIso (actionComparison hZ h a b F k hk) ≪≫
      (derivedDirectImage (j k)).mapIso (βPlus k hk) ≪≫
      (asIso (projectionComparison hZ a b F (J.group k))).symm
  have hδ (k : ℕ) (hk : A'.cutoff ≤ k) :
      (δPlus k hk).hom ≫ projectionComparison hZ a b F (J.group k) =
        actionComparison hZ h a b F k hk ≫ (derivedDirectImage (j k)).map (βPlus k hk).hom := by
    dsimp only [δPlus, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    simp
  have hr (k : ℕ) (hk : A'.cutoff ≤ k) :
      RestrictsTo i (j k) (h k (hx k hk) (hz k hk)) (projectionSquare (J.group k) i)
        ε (δPlus k hk).hom.hom (β.datum k (hz k hk)).iso.hom :=
    restrictsTo_of_mates _ _ (a (j k)) b F (hδ k hk)
  let δ (k : ℕ) (hk : A'.cutoff ≤ k) :
      (A'.action k hk).Equivariance G.obj :=
    extendDatum hZ _ _ (h k (hx k hk) (hz k hk)) b F (β.datum k (hz k hk))
      (DerivedCategory.Plus.ι.mapIso (δPlus k hk)) (hr k hk)
  let α : A'.Equivariance G.obj :=
    { datum := δ
      compatibility := by
        intro k l hk hkl
        let hl := hk.trans hkl
        let kx := J.parameterMap hkl (𝟙 X)
        let kz := J.parameterMap hkl (𝟙 U)
        have hj : j l ≫ kx = kz ≫ j k := TopCat.ext (fun _ => rfl)
        have hkx : kx ≫ AnalyticAction.projection (J.group k) X =
            AnalyticAction.projection (J.group l) X := TopCat.ext (fun _ => rfl)
        have hkz : kz ≫ AnalyticAction.projection (J.group k) U =
            AnalyticAction.projection (J.group l) U := TopCat.ext (fun _ => rfl)
        have hh := (hr k hk).pullback kx kz hj (A'.factors hk hkl) hkx
          (B.factors (hz k hk) hkl) hkz (h l (hx l hl) (hz l hl)) (projectionSquare _ i)
        rw [β.compatibility (hz k hk) hkl] at hh
        have hG : DerivedSupportedOn (Set.range (j l))
            ((boundedBelowInverseImage (AnalyticAction.projection (J.group l) X)).obj G) := by
          rw [oneParameter_range (J.group l) Z]
          exact pullbackExtension_supported _ F
        exact restrictsTo_injective (parameterInclusion_closed _ hZ.isClosedEmbedding_subtypeVal)
          hG hh (hr l hl) }
  refine ⟨α, ?_⟩
  intro k hk
  exact congrArg (fun f => f.hom) (hδ k hk)

private theorem squareArrows_conjugate {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {E P : B ⥤ A} {S : C ⥤ A} {G : B} {V W : C} (τ : G ≅ G) (σ : S ≅ S)
    (v : V ⟶ W)
    {cA cA' : E.obj G ⟶ S.obj V} {cP cP' : P.obj G ⟶ S.obj W} [IsIso cP]
    (ha : cA' = E.map τ.inv ≫ cA ≫ σ.hom.app V)
    (hp : cP' = P.map τ.inv ≫ cP ≫ σ.hom.app W)
    {α α' : E.obj G ⟶ P.obj G}
    (h : α ≫ cP = cA ≫ S.map v) (h' : α' ≫ cP' = cA' ≫ S.map v) :
    E.map τ.hom ≫ α' = α ≫ P.map τ.hom := by
  haveI : IsIso cP' := by rw [hp]; infer_instance
  apply (cancel_mono cP').mp
  have hE : E.map τ.hom ≫ E.map τ.inv = 𝟙 _ := by rw [← Functor.map_comp, Iso.hom_inv_id, E.map_id]
  have hP : P.map τ.hom ≫ P.map τ.inv = 𝟙 _ := by rw [← Functor.map_comp, Iso.hom_inv_id, P.map_id]
  calc
    (E.map τ.hom ≫ α') ≫ cP' = E.map τ.hom ≫ cA' ≫ S.map v := by rw [Category.assoc, h']
    _ = cA ≫ S.map v ≫ σ.hom.app W := by
      rw [ha]
      simp only [Category.assoc, reassoc_of% hE, ← σ.hom.naturality v]
    _ = (α ≫ P.map τ.hom) ≫ cP' := by
      rw [hp]
      simp only [Category.assoc, reassoc_of% hP, reassoc_of% h]

theorem closedEquivarianceAdjunctionChange :
    ClosedEquivarianceAdjunctionChange.{u} := by
  intro J X Z hZ A B h a a' b b' F
  have hh (k : ℕ) (hk : max A.cutoff B.cutoff ≤ k) :=
    adjointSquareMap_change
      (pullbackSquare (h k ((le_max_left _ _).trans hk) ((le_max_right _ _).trans hk)))
      (a (parameterInclusion (J.group k) (closedInclusion Z)))
      (a' (parameterInclusion (J.group k) (closedInclusion Z))) b b' F
  have hp (k : ℕ) :=
    adjointSquareMap_change (pullbackSquare (projectionSquare (J.group k) (closedInclusion Z)))
      (a (parameterInclusion (J.group k) (closedInclusion Z)))
      (a' (parameterInclusion (J.group k) (closedInclusion Z))) b b' F
  refine ⟨fun k hk => ⟨hh k hk, hp k⟩, ?_⟩
  intro hIso β α α' hα hα' k hk
  let hz := (le_max_right A.cutoff B.cutoff).trans hk
  let H := J.group k
  let v : (boundedBelowInverseImage (B.action k hz).act).obj F ⟶
      (boundedBelowInverseImage (AnalyticAction.projection H (TopCat.of Z))).obj F :=
    ObjectProperty.homMk (β.datum k hz).iso.hom
  let G := (closedExtensionPlus hZ).obj F
  let e := (A.action k ((le_max_left _ _).trans hk)).act
  let p := AnalyticAction.projection H X
  let t : (boundedBelowInverseImage e).obj G ⟶ (boundedBelowInverseImage p).obj G :=
    ObjectProperty.homMk (α.datum k hk).iso.hom
  let t' : (boundedBelowInverseImage e).obj G ⟶ (boundedBelowInverseImage p).obj G :=
    ObjectProperty.homMk (α'.datum k hk).iso.hom
  let S := derivedDirectImage (parameterInclusion H (closedInclusion Z))
  have ht : t ≫ projectionComparison hZ a b F H =
      actionComparison hZ h a b F k hk ≫ S.map v :=
    ObjectProperty.hom_ext _ (hα k hk)
  have ht' : t' ≫ projectionComparison hZ a' b' F H =
      actionComparison hZ h a' b' F k hk ≫ S.map v :=
    ObjectProperty.hom_ext _ (hα' k hk)
  haveI : IsIso (projectionComparison hZ a b F H) := (hIso k hk).2
  exact congrArg (fun f => f.hom)
    (squareArrows_conjugate (E := boundedBelowInverseImage e) (P := boundedBelowInverseImage p)
      (cP := projectionComparison hZ a b F H)
      ((b.rightAdjointUniq b').app F) ((a (parameterInclusion H (closedInclusion Z))).rightAdjointUniq
        (a' (parameterInclusion H (closedInclusion Z)))) v (hh k hk) (hp k) ht ht')

end RepTheorySurvey.Geometric.ClosedEquivarianceExtension
