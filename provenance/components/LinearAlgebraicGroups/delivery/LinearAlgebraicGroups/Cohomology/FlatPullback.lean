import Specs.LinearAlgebraicGroups.Cohomology.FlatPullback
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.Grp.Zero

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v w

namespace LinearAlgebraicGroups.FlatCohomology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem affinePullback : AffinePullback.{u} := by
  intro R S φ
  let adj₁ := (tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))
  let adj₃ := adj₂.ofNatIsoRight (affinePushforwardSections φ).symm
  refine ⟨adj₁.leftAdjointUniq adj₃, fun M => ?_⟩
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app adj₁ adj₃ M
  rw [show adj₃.unit.app M =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
      ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) ≫
      (affinePushforwardSections φ).inv.app _ by
    dsimp [adj₃, Adjunction.ofNatIsoRight, adj₂, Adjunction.comp]
    rw [Adjunction.homEquiv_unit]
    rfl] at h
  dsimp only [adj₁] at h
  rw [Adjunction.comp_homEquiv] at h
  exact h

theorem flatScalarExtension : FlatScalarExtension.{u} := by
  intro k R _ _ _ X
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
    rw [Flat.SpecMap_iff]
    exact (RingHom.flat_algebraMap_iff).2 (inferInstance : Module.Flat k R)
  infer_instance

section Lifts

variable {C : Type w} [Category.{v} C] [Abelian C] {F : C}
    (I : InjectiveResolution F) (J : CochainComplex C ℕ) [∀ i, Injective (J.X i)]

private def liftFromResolution (a : F ⟶ J.X 0) (ha : a ≫ J.d 0 1 = 0) :
    I.cocomplex ⟶ J := by
  let l₀ := Injective.factorThru a (I.ι.f 0)
  have h₀ : I.ι.f 0 ≫ l₀ = a := Injective.comp_factorThru _ _
  let l₁ := I.exact₀.descToInjective (l₀ ≫ J.d 0 1) (by
    dsimp
    rw [← Category.assoc, h₀, ha])
  refine CochainComplex.mkHom _ _ l₀ l₁ (I.exact₀.comp_descToInjective _ _).symm ?_
  rintro n ⟨l, l', h⟩
  have hz : I.cocomplex.d n (n + 1) ≫ l' ≫ J.d (n + 1) (n + 2) = 0 := by
    rw [← Category.assoc, ← h, Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
  exact ⟨(I.exact_succ n).descToInjective _ hz,
    ((I.exact_succ n).comp_descToInjective _ hz).symm⟩

private theorem liftFromResolution_zero (a : F ⟶ J.X 0) (ha : a ≫ J.d 0 1 = 0) :
    I.ι.f 0 ≫ (liftFromResolution I J a ha).f 0 = a :=
  Injective.comp_factorThru _ _

private def homotopyOfLiftDifference (l : I.cocomplex ⟶ J)
    (hl : I.ι.f 0 ≫ l.f 0 = 0) : Homotopy l 0 := by
  let h₀ := I.exact₀.descToInjective (l.f 0) hl
  have w₀ : I.cocomplex.d 0 1 ≫ h₀ = l.f 0 := I.exact₀.comp_descToInjective _ _
  let h₁ := (I.exact_succ 0).descToInjective (l.f 1 - h₀ ≫ J.d 0 1) (by
    dsimp
    rw [Preadditive.comp_sub, ← Category.assoc _ h₀, w₀, l.comm, sub_self])
  have w₁ : l.f 1 = h₀ ≫ J.d 0 1 + I.cocomplex.d 1 2 ≫ h₁ := by
    rw [(I.exact_succ 0).comp_descToInjective]
    abel
  refine Homotopy.mkCoinductive l h₀ w₀.symm h₁ w₁ ?_
  rintro n ⟨h, h', w⟩
  have hz : I.cocomplex.d (n + 1) (n + 2) ≫
      (l.f (n + 2) - h' ≫ J.d (n + 1) (n + 2)) = 0 := by
    rw [Preadditive.comp_sub, ← l.comm, w, Preadditive.add_comp,
      Category.assoc _ (J.d n (n + 1)), HomologicalComplex.d_comp_d, comp_zero,
      zero_add, Category.assoc, sub_self]
  refine ⟨(I.exact_succ (n + 1)).descToInjective _ hz, ?_⟩
  rw [(I.exact_succ (n + 1)).comp_descToInjective]
  abel

private def homotopyOfLifts (l t : I.cocomplex ⟶ J)
    (h : I.ι.f 0 ≫ l.f 0 = I.ι.f 0 ≫ t.f 0) : Homotopy l t :=
  Homotopy.equivSubZero.invFun (homotopyOfLiftDifference I J (l - t)
    (by change I.ι.f 0 ≫ (l.f 0 - t.f 0) = 0
        rw [Preadditive.comp_sub, h, sub_self]))

end Lifts


section Comparisons

variable {A B : Type u} [CommRing A] [CommRing B] {X : OverRing A} {Y : OverRing B}
    (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)

private theorem lift_exists [(Scheme.Modules.pushforward f).PreservesInjectiveObjects] :
    ∃ l, IsLift f α I J l := by
  let P := Scheme.Modules.pushforward f
  let K := (onCochains P).obj J.cocomplex
  let (i : ℕ) : Injective (K.X i) := P.injective_obj_of_injective (J.injective i)
  have hz : (α ≫ P.map (J.ι.f 0)) ≫ K.d 0 1 = 0 := by
    change (α ≫ P.map (J.ι.f 0)) ≫ P.map (J.cocomplex.d 0 1) = 0
    simp only [Category.assoc, ← P.map_comp, J.ι_f_zero_comp_complex_d, P.map_zero, comp_zero]
  exact ⟨liftFromResolution I K _ hz, liftFromResolution_zero I K _ hz⟩

private theorem homology_of_lifts_eq [(Scheme.Modules.pushforward f).PreservesInjectiveObjects]
    (n : ℕ) {l t : I.cocomplex ⟶ (onCochains (Scheme.Modules.pushforward f)).obj J.cocomplex}
    (hl : IsLift f α I J l) (ht : IsLift f α I J t) :
    HomologicalComplex.homologyMap (sectionsLift φ f w l) n =
      HomologicalComplex.homologyMap (sectionsLift φ f w t) n := by
  let P := Scheme.Modules.pushforward f
  let K := (onCochains P).obj J.cocomplex
  let (i : ℕ) : Injective (K.X i) := P.injective_obj_of_injective (J.injective i)
  let h := homotopyOfLifts I K l t (hl.trans ht.symm)
  simp only [sectionsLift, HomologicalComplex.homologyMap_comp]
  rw [((sections X).mapHomotopy h).homologyMap_eq n]

private theorem restrictHomology_natural (φ : A →+* B)
    {J K : CochainComplex (ModuleCat.{u} B) ℕ} (d : J ⟶ K) (n : ℕ) :
    HomologicalComplex.homologyMap ((onCochains (restrict φ)).map d) n ≫
        (restrictHomology φ K n).hom =
      (restrictHomology φ J n).hom ≫
        (restrict φ).map (HomologicalComplex.homologyMap d n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map d) (restrict φ)

private theorem sectionsPushforwardComplex_natural {J K : CochainComplex Y.left.Modules ℕ}
    (d : J ⟶ K) :
    (onCochains (sections X)).map ((onCochains (Scheme.Modules.pushforward f)).map d) ≫
        (sectionsPushforwardComplex φ f w K).hom =
      (sectionsPushforwardComplex φ f w J).hom ≫
        (onCochains (restrict φ)).map ((onCochains (sections Y)).map d) := by
  exact ((Functor.mapHomologicalComplexCompIso
    (sectionsPushforward φ f w) (.up ℕ)) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (sections Y ⋙ restrict φ)) (.up ℕ)).symm).hom.naturality d

private def comparison (n : ℕ)
    (l : I.cocomplex ⟶ (onCochains (Scheme.Modules.pushforward f)).obj J.cocomplex) :
    (cohomology X n).obj F ⟶ (restrict φ).obj ((cohomology Y n).obj G) :=
  (I.isoRightDerivedObj (sections X) n).hom ≫
    HomologicalComplex.homologyMap (sectionsLift φ f w l) n ≫
    (restrictHomology φ ((onCochains (sections Y)).obj J.cocomplex) n).hom ≫
    (restrict φ).map (J.isoRightDerivedObj (sections Y) n).inv

private theorem comparison_independent [(Scheme.Modules.pushforward f).PreservesInjectiveObjects]
    (I' : InjectiveResolution F) (J' : InjectiveResolution G) (n : ℕ)
    {l : I.cocomplex ⟶ (onCochains (Scheme.Modules.pushforward f)).obj J.cocomplex}
    {l' : I'.cocomplex ⟶ (onCochains (Scheme.Modules.pushforward f)).obj J'.cocomplex}
    (hl : IsLift f α I J l) (hl' : IsLift f α I' J' l') :
    comparison φ f w I J n l = comparison φ f w I' J' n l' := by
  let P := Scheme.Modules.pushforward f
  let dI := InjectiveResolution.desc (𝟙 F) I' I
  let dJ := InjectiveResolution.desc (𝟙 G) J' J
  have hdI : I.ι.f 0 ≫ dI.f 0 = I'.ι.f 0 := by simp [dI]
  have hdJ : J.ι.f 0 ≫ dJ.f 0 = J'.ι.f 0 := by simp [dJ]
  have h₁ : IsLift f α I J' (l ≫ (onCochains P).map dJ) := by
    change I.ι.f 0 ≫ l.f 0 ≫ P.map (dJ.f 0) = α ≫ P.map (J'.ι.f 0)
    rw [← Category.assoc, hl, Category.assoc, ← P.map_comp, hdJ]
  have h₂ : IsLift f α I J' (dI ≫ l') := by
    change I.ι.f 0 ≫ dI.f 0 ≫ l'.f 0 = α ≫ P.map (J'.ι.f 0)
    rw [← Category.assoc, hdI]
    exact hl'
  have h := homology_of_lifts_eq φ f w α I J' n h₁ h₂
  have hI := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 F) I I' dI
    (by simpa only [Category.id_comp] using hdI) (sections X) n
  have hJ := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 G) J J' dJ
    (by simpa only [Category.id_comp] using hdJ) (sections Y) n
  rw [show (cohomology X n).map (𝟙 F) = 𝟙 _ from CategoryTheory.Functor.map_id _ _, Category.id_comp] at hI
  rw [show (cohomology Y n).map (𝟙 G) = 𝟙 _ from CategoryTheory.Functor.map_id _ _, Category.comp_id] at hJ
  change (I'.isoRightDerivedObj (sections X) n).hom =
    (I.isoRightDerivedObj (sections X) n).hom ≫
      HomologicalComplex.homologyMap ((onCochains (sections X)).map dI) n at hI
  change (J.isoRightDerivedObj (sections Y) n).inv =
    HomologicalComplex.homologyMap ((onCochains (sections Y)).map dJ) n ≫
      (J'.isoRightDerivedObj (sections Y) n).inv at hJ
  have hs₁ : sectionsLift φ f w (l ≫ (onCochains P).map dJ) =
      sectionsLift φ f w l ≫ (onCochains (restrict φ)).map ((onCochains (sections Y)).map dJ) := by
    simp only [sectionsLift, Functor.map_comp, Category.assoc]
    rw [sectionsPushforwardComplex_natural φ f w]
  have hs₂ : sectionsLift φ f w (dI ≫ l') =
      (onCochains (sections X)).map dI ≫ sectionsLift φ f w l' := by
    simp only [sectionsLift, Functor.map_comp, Category.assoc]
  rw [hs₁, hs₂, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  simp only [comparison]
  rw [hI, Category.assoc, ← reassoc_of% h,
    reassoc_of% restrictHomology_natural φ ((onCochains (sections Y)).map dJ) n,
    ← (restrict φ).map_comp, ← hJ]

private theorem hasCohomologyMap [(Scheme.Modules.pushforward f).PreservesInjectiveObjects]
    (n : ℕ) : ∃! m, IsCohomologyMap φ f w α n m := by
  let I₀ := injectiveResolution F
  let J₀ := injectiveResolution G
  obtain ⟨l₀, hl₀⟩ := lift_exists f α I₀ J₀
  refine ⟨comparison φ f w I₀ J₀ n l₀, ?_, ?_⟩
  · intro I J
    exact ⟨lift_exists f α I J, fun l hl =>
      comparison_independent φ f w α I₀ J₀ I J n hl₀ hl⟩
  · intro m hm
    exact (hm I₀ J₀).2 l₀ hl₀

end Comparisons


section Stalks

open TopologicalSpace TopCat
open StalkSkyscraperPresheafAdjunctionAuxs
open PresheafOfModules.ModuleColimit

local instance {X : Scheme.{u}} (x : X) (U : X.Opens) : Decidable (x ∈ U) :=
  Classical.propDecidable _

variable {X Y : Scheme.{u}}

private abbrev stalkRingCocone (x : X) :=
  (forget₂ CommRingCat RingCat).mapCocone
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf))

private abbrev stalkRingIsColimit (x : X) : IsColimit (stalkRingCocone x) :=
  isColimitOfPreserves (forget₂ CommRingCat RingCat) (colimit.isColimit _)

local instance (x : X) : InitiallySmall.{u} (OpenNhds x) :=
  InitiallySmall.mk' (𝟭 _)

private abbrev neighbors (x : X) : X.Modules ⥤
    PresheafOfModules.{u} ((OpenNhds.inclusion x).op ⋙ X.ringCatSheaf.obj) :=
  Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.pushforward₀ (OpenNhds.inclusion x) X.ringCatSheaf.obj

private def moduleStalk (x : X) : X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  neighbors x ⋙ PresheafOfModules.colimitFunctor (stalkRingIsColimit x)

private abbrev sky (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) :=
  skyscraperPresheaf x (AddCommGrpCat.of N)

private abbrev skyIso (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : X.Opens) (hx : x ∈ U) : (sky x N).obj (op U) ≅ AddCommGrpCat.of N :=
  eqToIso (ite_eq_left hx)

private theorem skySubsingleton (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : X.Opens) (hx : x ∉ U) : Subsingleton ((sky x N).obj (op U)) := by
  change Subsingleton (↑(if x ∈ U then AddCommGrpCat.of N else terminal Ab))
  rw [ite_eq_right hx]
  apply AddCommGrpCat.isZero_iff_subsingleton.mp
  exact terminalIsTerminal.isZero

@[instance_reducible] private def skyModule (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) :
    Module Γ(X, U) ((sky x N).obj (op U)) := by
  by_cases hx : x ∈ U
  · letI := Module.compHom N (X.presheaf.germ U x hx).hom
    exact (skyIso x N U hx).addCommGroupIsoToAddEquiv.module Γ(X, U)
  · letI := skySubsingleton x N U hx
    exact { smul := fun _ _ => 0
            one_smul := fun _ => Subsingleton.elim _ _
            mul_smul := fun _ _ _ => Subsingleton.elim _ _
            smul_zero := fun _ => Subsingleton.elim _ _
            smul_add := fun _ _ _ => Subsingleton.elim _ _
            add_smul := fun _ _ _ => Subsingleton.elim _ _
            zero_smul := fun _ => Subsingleton.elim _ _ }

private theorem skyIso_smul (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens)
    (hx : x ∈ U) (r : Γ(X, U)) (s : (sky x N).obj (op U)) :
    letI := skyModule x N U
    (skyIso x N U hx).hom (r • s) =
      (X.presheaf.germ U x hx) r • (skyIso x N U hx).hom s := by
  let e := (skyIso x N U hx).addCommGroupIsoToAddEquiv
  have he : skyModule x N U =
      (letI := Module.compHom N (X.presheaf.germ U x hx).hom; e.module Γ(X, U)) := by
    unfold skyModule
    rw [dite_eq_left hx]
  let eval (m : Module Γ(X, U) ((sky x N).obj (op U))) :=
    letI := m
    e (r • s)
  exact (congrArg eval he).trans (e.apply_symm_apply _)

private theorem sky_map_of_mem (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    {U V : X.Opensᵒᵖ} (i : U ⟶ V) (hx : x ∈ V.unop) :
    (sky x N).map i ≫ (skyIso x N V.unop hx).hom =
      (skyIso x N U.unop (i.unop.le hx)).hom := by
  simp [sky, skyscraperPresheaf_map, hx, skyIso, eqToHom_trans]

private def skyscraperModule (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) : X.Modules := by
  letI (U : X.Opensᵒᵖ) : Module (X.ringCatSheaf.obj.obj U) ((sky x N).obj U) :=
    skyModule x N U.unop
  refine ⟨PresheafOfModules.ofPresheaf (R := X.ringCatSheaf.obj) (sky x N) ?_, ?_⟩
  · intro U V i r s
    by_cases hx : x ∈ V.unop
    · apply (skyIso x N V.unop hx).addCommGroupIsoToAddEquiv.injective
      let := skyModule x N U.unop
      let := skyModule x N V.unop
      change (((sky x N).map i) ≫ (skyIso x N V.unop hx).hom) (r • s) =
        (skyIso x N V.unop hx).hom (X.presheaf.map i r • (sky x N).map i s)
      rw [sky_map_of_mem x N i hx, skyIso_smul, skyIso_smul]
      have h := sky_map_of_mem x N i hx
      have hs : (skyIso x N V.unop hx).hom ((sky x N).map i s) =
          (skyIso x N U.unop (i.unop.le hx)).hom s := congr($h s)
      rw [hs]
      exact congrArg (fun a : X.presheaf.stalk x =>
        a • (skyIso x N U.unop (i.unop.le hx)).hom s)
        (congr($(X.presheaf.germ_res' i x hx) r)).symm
    · exact (skySubsingleton x N V.unop hx).elim _ _
  · exact skyscraperPresheaf_isSheaf x (AddCommGrpCat.of N)

private def skyscraperModuleFunctor (x : X) :
    ModuleCat.{u} (X.presheaf.stalk x) ⥤ X.Modules where
  obj := skyscraperModule x
  map {M N} f := ⟨PresheafOfModules.homMk
    ((skyscraperPresheafFunctor x).map ((forget₂ _ Ab).map f)) (by
      intro U r s
      by_cases hx : x ∈ U.unop
      · apply (skyIso x N U.unop hx).addCommGroupIsoToAddEquiv.injective
        let := skyModule x M U.unop
        let := skyModule x N U.unop
        change Γ(X, U.unop) at r
        have he (m : (sky x M).obj U) :
            (skyIso x N U.unop hx).hom
              (((skyscraperPresheafFunctor x).map ((forget₂ _ Ab).map f)).app U m) =
                f ((skyIso x M U.unop hx).hom m) := by
          have hp : ((skyscraperPresheafFunctor x).map ((forget₂ _ Ab).map f)).app U ≫
              (skyIso x N U.unop hx).hom =
              (skyIso x M U.unop hx).hom ≫ (forget₂ _ Ab).map f := by
            change (SkyscraperPresheafFunctor.map' x ((forget₂ _ Ab).map f)).app U ≫ _ = _
            simp only [SkyscraperPresheafFunctor.map'_app, dite_eq_left hx, skyIso, eqToIso.hom,
              Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
          exact congr($hp m)
        let t : sky x M ⟶ sky x N := (skyscraperPresheafFunctor x).map ((forget₂ _ Ab).map f)
        change (skyIso x N U.unop hx).hom (t.app U (r • s)) =
          (skyIso x N U.unop hx).hom (r • t.app U s)
        change ∀ m, (skyIso x N U.unop hx).hom (t.app U m) =
          f ((skyIso x M U.unop hx).hom m) at he
        rw [he, skyIso_smul, skyIso_smul, he, map_smul]
      · exact (skySubsingleton x N U.unop hx).elim _ _)⟩
  map_id M := (Scheme.Modules.toPresheaf X).map_injective
    ((skyscraperPresheafFunctor x).map_id (AddCommGrpCat.of M))
  map_comp f g := (Scheme.Modules.toPresheaf X).map_injective
    ((skyscraperPresheafFunctor x).map_comp ((forget₂ _ Ab).map f) ((forget₂ _ Ab).map g))

private theorem moduleStalk_germ_smul (x : X) (F : X.Modules) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) (s : Γ(F, U)) :
    letI := ((moduleStalk x).obj F).isModule
    F.presheaf.germ U x hx (r • s) =
      X.presheaf.germ U x hx r • (show (moduleStalk x).obj F from F.presheaf.germ U x hx s) :=
  (smul_eq (M := (neighbors x).obj F) (stalkRingIsColimit x)
    (colimit.isColimit _) (U := op (⟨U, hx⟩ : OpenNhds x)) r s).symm

private theorem moduleStalk_representatives (x : X) (F : X.Modules)
    (r : X.presheaf.stalk x) (s : (moduleStalk x).obj F) :
    ∃ (U : X.Opens) (h : x ∈ U) (a : Γ(X, U)) (b : Γ(F, U)),
      X.presheaf.germ U x h a = r ∧ F.presheaf.germ U x h b = s := by
  obtain ⟨U, a, b, ha, hb⟩ := jointly_surjective₂
    (hcR := stalkRingIsColimit x) (M := (neighbors x).obj F)
    (hcM := colimit.isColimit _) r s
  exact ⟨U.unop.1, U.unop.2, a, b, ha, hb⟩

private theorem moduleStalk_map_forget (x : X) {F G : X.Modules} (f : F ⟶ G) :
    (forget₂ _ Ab).map ((moduleStalk x).map f) =
      (TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf := rfl

private theorem skyTo_stalk (x : X) (F : X.Modules) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (l : (moduleStalk x).obj F ⟶ N) (U : X.Opens) (hx : x ∈ U) (s : Γ(F, U)) :
    (skyIso x N U hx).hom
      ((toSkyscraperPresheaf x (𝓕 := F.presheaf) ((forget₂ _ Ab).map l)).app (op U) s) =
      l (F.presheaf.germ U x hx s) := by
  have h : (toSkyscraperPresheaf x (𝓕 := F.presheaf) ((forget₂ _ Ab).map l)).app (op U) ≫
      (skyIso x N U hx).hom = F.presheaf.germ U x hx ≫ (forget₂ _ Ab).map l := by
    simp only [toSkyscraperPresheaf_app, unop_op, dite_eq_left hx, skyIso, eqToIso.hom,
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact congr($h s)

private def stalkSkyscraperHomEquiv (x : X) (F : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((moduleStalk x).obj F ⟶ N) ≃ (F ⟶ (skyscraperModuleFunctor x).obj N) where
  toFun l := ⟨PresheafOfModules.homMk (toSkyscraperPresheaf x (𝓕 := F.presheaf) ((forget₂ _ Ab).map l)) (by
    intro U r s
    by_cases hx : x ∈ U.unop
    · apply (skyIso x N U.unop hx).addCommGroupIsoToAddEquiv.injective
      let := skyModule x N U.unop
      let := ((moduleStalk x).obj F).isModule
      change Γ(X, U.unop) at r
      change Γ(F, U.unop) at s
      let t : F.presheaf ⟶ sky x N := toSkyscraperPresheaf x (𝓕 := F.presheaf) ((forget₂ _ Ab).map l)
      change (skyIso x N U.unop hx).hom (t.app U (r • s)) =
        (skyIso x N U.unop hx).hom (r • t.app U s)
      have h (z : Γ(F, U.unop)) : (skyIso x N U.unop hx).hom (t.app U z) =
          l (F.presheaf.germ U.unop x hx z) := skyTo_stalk x F N l U.unop hx z
      rw [skyIso_smul, h, h, moduleStalk_germ_smul, map_smul]
    · exact (skySubsingleton x N U.unop hx).elim _ _)⟩
  invFun ψ := ModuleCat.ofHom {
    toFun := fromStalk x ψ.mapPresheaf
    map_add' := map_add _
    map_smul' := by
      intro r s
      obtain ⟨U, hx, a, b, rfl, rfl⟩ := moduleStalk_representatives x F r s
      let τ := fromStalk x ψ.mapPresheaf
      have h (z : Γ(F, U)) : τ (F.presheaf.germ U x hx z) =
          (skyIso x N U hx).hom (ψ.app U z) := by
        have h := germ_fromStalk x ψ.mapPresheaf U hx
        exact congr($h z)
      let := ((moduleStalk x).obj F).isModule
      change τ (X.presheaf.germ U x hx a •
        (show (moduleStalk x).obj F from F.presheaf.germ U x hx b)) =
        X.presheaf.germ U x hx a • τ (F.presheaf.germ U x hx b)
      rw [← moduleStalk_germ_smul, h, h, ψ.app_smul]
      exact skyIso_smul x N U hx a _ }
  left_inv l := by
    apply (forget₂ _ Ab).map_injective
    exact fromStalk_to_skyscraper x (𝓕 := F.presheaf) ((forget₂ _ Ab).map l)
  right_inv ψ := by
    apply (Scheme.Modules.toPresheaf X).map_injective
    exact to_skyscraper_fromStalk x ψ.mapPresheaf

private def moduleStalkAdjunction (x : X) : moduleStalk x ⊣ skyscraperModuleFunctor x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := stalkSkyscraperHomEquiv x
      homEquiv_naturality_left_symm := by
        intro F G N f ψ
        apply (forget₂ _ Ab).map_injective
        rw [CategoryTheory.Functor.map_comp, moduleStalk_map_forget]
        apply F.presheaf.stalk_hom_ext
        intro U hx
        change F.presheaf.germ U x hx ≫ fromStalk x (f ≫ ψ).mapPresheaf =
          F.presheaf.germ U x hx ≫ (TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf ≫
            fromStalk x ψ.mapPresheaf
        simp [Category.assoc]
      homEquiv_naturality_right := by
        intro F M N l g
        apply (Scheme.Modules.toPresheaf X).map_injective
        change toSkyscraperPresheaf x (𝓕 := F.presheaf) ((forget₂ _ Ab).map (l ≫ g)) =
          toSkyscraperPresheaf x (𝓕 := F.presheaf) ((forget₂ _ Ab).map l) ≫
            (skyscraperPresheafFunctor x).map ((forget₂ _ Ab).map g)
        ext U : 1
        by_cases hx : x ∈ U
        · change _ = (toSkyscraperPresheaf x (𝓕 := F.presheaf) ((forget₂ _ Ab).map l)).app
            (op U) ≫ (SkyscraperPresheafFunctor.map' x ((forget₂ _ Ab).map g)).app (op U)
          simp [toSkyscraperPresheaf_app, SkyscraperPresheafFunctor.map'_app, hx,
            Category.assoc]
          rfl
        · exact ((terminalIsTerminal (C := Ab)).ofIso
            (eqToIso (ite_eq_right hx)).symm).hom_ext _ _ }


private theorem pushSkyPresheaf (f : X ⟶ Y) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((Scheme.Modules.pushforward f).obj (skyscraperModule x N)).presheaf =
      (skyscraperModule (f x) ((restrict (f.stalkMap x).hom).obj N)).presheaf := by
  rfl

private def pushSky (f : X ⟶ Y) (x : X) :
    skyscraperModuleFunctor x ⋙ Scheme.Modules.pushforward f ≅
      restrict (f.stalkMap x).hom ⋙ skyscraperModuleFunctor (f x) := by
  refine NatIso.ofComponents (fun N => ?_) ?_
  · let M := (restrict (f.stalkMap x).hom).obj N
    let P := (Scheme.Modules.pushforward f).obj (skyscraperModule x N)
    let Q := skyscraperModule (f x) M
    have e : P.presheaf = Q.presheaf := pushSkyPresheaf f x N
    let h : P ⟶ Q := ⟨PresheafOfModules.homMk (eqToHom e) (by
      intro U r s
      by_cases hx : f x ∈ U.unop
      · let V := f ⁻¹ᵁ U.unop
        let ex := skyIso x N V hx
        let ey := skyIso (f x) M U.unop hx
        apply ey.addCommGroupIsoToAddEquiv.injective
        change ey.hom ((eqToHom e).app U (r • s)) =
          ey.hom (r • (show Q.val.obj U from (eqToHom e).app U s))
        have hc : ey.hom ((eqToHom e).app U s) = ex.hom s := rfl
        have hs : ey.hom ((eqToHom e).app U (r • s)) = ex.hom (r • s) := rfl
        have hy := skyIso_smul (f x) M U.unop hx r ((eqToHom e).app U s)
        change ey.hom (r • (show Q.val.obj U from (eqToHom e).app U s)) =
          Y.presheaf.germ U.unop (f x) hx r • ey.hom ((eqToHom e).app U s) at hy
        rw [hs, hy, hc]
        have hs₁ := skyIso_smul x N V hx (f.app U.unop r) s
        change ex.hom (r • s) =
          (f.stalkMap x (Y.presheaf.germ U.unop (f x) hx r)) • ex.hom s
        rw [f.germ_stalkMap_apply U.unop x hx]
        exact hs₁
      · exact (skySubsingleton (f x) M U.unop hx).elim _ _)⟩
    have hh : IsIso ((Scheme.Modules.toPresheaf Y).map h) := by
      change IsIso (eqToHom e)
      infer_instance
    have := isIso_of_reflects_iso h (Scheme.Modules.toPresheaf Y)
    exact asIso h
  · intro M N g
    apply (Scheme.Modules.toPresheaf Y).map_injective
    ext U : 1
    rfl

private def pullbackStalk (f : X ⟶ Y) (x : X) :
    Scheme.Modules.pullback f ⋙ moduleStalk x ≅
      moduleStalk (f x) ⋙ ModuleCat.extendScalars.{u,u,u} (f.stalkMap x).hom :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (moduleStalkAdjunction x)).leftAdjointUniq
    (Adjunction.ofNatIsoRight
      ((moduleStalkAdjunction (f x)).comp (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))
      (pushSky f x).symm)

private instance (x : X) : (moduleStalk x).PreservesMonomorphisms where
  preserves {F G} t ht := by
    let P := Scheme.Modules.toPresheaf X
    let S := SheafOfModules.toSheaf X.ringCatSheaf
    have h : Mono (P.map t) := P.map_mono t
    have ht' : Mono (S.map t) :=
      (TopCat.Sheaf.forget Ab X).mono_of_mono_map h
    apply (forget₂ _ Ab).mono_of_mono_map
    rw [moduleStalk_map_forget]
    exact TopCat.Presheaf.stalk_mono_of_mono (S.map t) x

theorem flatPullbackExact : IsExactFlatPullback.{u} := by
  intro X Y f hflat
  let L := Scheme.Modules.pullback f
  have : L.PreservesMonomorphisms := by
    constructor
    intro F G t ht
    let S := SheafOfModules.toSheaf Y.ringCatSheaf
    apply S.mono_of_mono_map
    have hStalk (y : Y) :
        Mono ((TopCat.Presheaf.stalkFunctor Ab y).map (S.map (L.map t)).hom) := by
      have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (Flat.stalkMap f y)
      let e := pullbackStalk f y
      have hpres : (L ⋙ moduleStalk y).PreservesMonomorphisms :=
        Functor.PreservesMonomorphisms.of_iso e.symm
      have hm : Mono ((moduleStalk y).map (L.map t)) := (L ⋙ moduleStalk y).map_mono t
      have h := (forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) Ab).map_mono
        ((moduleStalk y).map (L.map t))
      change Mono ((TopCat.Presheaf.stalkFunctor Ab y).map (L.map t).mapPresheaf)
      rw [← moduleStalk_map_forget]
      exact h
    exact TopCat.Presheaf.mono_of_stalk_mono (S.map (L.map t))
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels L

theorem flatPushforwardPreservesInjectives : FlatPushforwardPreservesInjectives.{u} := by
  intro X Y f hf
  have := flatPullbackExact f
  have := Functor.preservesFiniteLimits_of_preservesHomology (Scheme.Modules.pullback f)
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Scheme.Modules.pullbackPushforwardAdjunction f)

theorem flatCohomologyMap : HasFlatCohomologyMap.{u} := by
  intro A B _ _ X Y φ f hf w F G α n
  have := flatPushforwardPreservesInjectives f
  exact hasCohomologyMap φ f w α n


end Stalks
section HomologyCoherence

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Abelian C₁] [Abelian C₂] [Abelian C₃]
    (S : ShortComplex C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology]

private theorem comparison_π :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let L := S.homologyData.left
  rw [L.mapCyclesIso_eq F, L.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Functor.mapIso_hom]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  change (L.map F).cyclesIso.hom ≫ F.map L.π ≫ F.map L.homologyIso.inv =
    (L.map F).cyclesIso.hom ≫ F.map L.cyclesIso.inv ≫ F.map S.homologyπ
  rw [← F.map_comp, ← F.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]

private theorem comparison_comp :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  have hc : (S.mapCyclesIso (F ⋙ G)).hom =
      ((S.map F).mapCyclesIso G).hom ≫ G.map (S.mapCyclesIso F).hom := by
    apply (cancel_mono (G.map (F.map S.iCycles))).mp
    have hh := S.mapCyclesIso_hom_iCycles (F ⋙ G)
    change (S.mapCyclesIso (F ⋙ G)).hom ≫ G.map (F.map S.iCycles) = _ at hh
    rw [hh, Category.assoc, ← G.map_comp, ShortComplex.mapCyclesIso_hom_iCycles,
      ShortComplex.mapCyclesIso_hom_iCycles]
    rfl
  apply (cancel_epi ((S.map F).map G).homologyπ).mp
  change (S.map (F ⋙ G)).homologyπ ≫ (S.mapHomologyIso (F ⋙ G)).hom =
    ((S.map F).map G).homologyπ ≫
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom
  rw [comparison_π, hc, reassoc_of% comparison_π (S.map F) G,
    Category.assoc, ← G.map_comp, comparison_π, G.map_comp]
  rfl

private theorem comparison_id :
    (S.mapHomologyIso (𝟭 C₁)).hom = 𝟙 S.homology := by
  have hc : (S.mapCyclesIso (𝟭 C₁)).hom = 𝟙 S.cycles := by
    apply (cancel_mono S.iCycles).mp
    exact (S.mapCyclesIso_hom_iCycles (𝟭 C₁)).trans (Category.id_comp _).symm
  apply (cancel_epi S.homologyπ).mp
  change (S.map (𝟭 C₁)).homologyπ ≫ (S.mapHomologyIso (𝟭 C₁)).hom = _
  rw [comparison_π, hc]
  change 𝟙 S.cycles ≫ S.homologyπ = S.homologyπ ≫ 𝟙 S.homology
  simp

end HomologyCoherence


section Composition

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    {X : OverRing A} {Y : OverRing B} {Z : OverRing D}

private def restrictCompComplex (φ : A →+* B) (ψ : B →+* D)
    (K : CochainComplex (ModuleCat.{u} D) ℕ) :
    (onCochains (restrict φ)).obj ((onCochains (restrict ψ)).obj K) ⟶
      (onCochains (restrict (ψ.comp φ))).obj K :=
  ((ModuleCat.restrictScalarsComp φ ψ).inv.mapHomologicalComplex (.up ℕ)).app K

private theorem restrictHomology_comp (φ : A →+* B) (ψ : B →+* D)
    (K : CochainComplex (ModuleCat.{u} D) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (restrictCompComplex φ ψ K) n ≫
      (restrictHomology (ψ.comp φ) K n).hom =
        (restrictHomology φ ((onCochains (restrict ψ)).obj K) n).hom ≫
        (restrict φ).map (restrictHomology ψ K n).hom ≫
          (ModuleCat.restrictScalarsComp φ ψ).inv.app (K.homology n) := by
  let S := K.sc n
  let e := ModuleCat.restrictScalarsComp φ ψ
  have h := S.homologyMap_mapNatTrans e.inv
  change HomologicalComplex.homologyMap (restrictCompComplex φ ψ K) n =
    (S.mapHomologyIso (restrict ψ ⋙ restrict φ)).hom ≫
      e.inv.app S.homology ≫ (S.mapHomologyIso (restrict (ψ.comp φ))).inv at h
  rw [h, comparison_comp]
  change ((_ ≫ _ ≫ (restrictHomology (ψ.comp φ) K n).inv) ≫
    (restrictHomology (ψ.comp φ) K n).hom) = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private def composeLifts (f : Y.left ⟶ X.left) (g : Z.left ⟶ Y.left)
    {I : CochainComplex X.left.Modules ℕ} {J : CochainComplex Y.left.Modules ℕ}
    {K : CochainComplex Z.left.Modules ℕ}
    (l : I ⟶ (onCochains (Scheme.Modules.pushforward f)).obj J)
    (t : J ⟶ (onCochains (Scheme.Modules.pushforward g)).obj K) :
    I ⟶ (onCochains (Scheme.Modules.pushforward (g ≫ f))).obj K :=
  l ≫ (onCochains (Scheme.Modules.pushforward f)).map t ≫
    (Functor.mapHomologicalComplexCompIso (Scheme.Modules.pushforwardComp g f) (.up ℕ)).hom.app K

private theorem composeLifts_isLift (f : Y.left ⟶ X.left) (g : Z.left ⟶ Y.left)
    {F : X.left.Modules} {G : Y.left.Modules} {H : Z.left.Modules}
    {α : F ⟶ (Scheme.Modules.pushforward f).obj G}
    {β : G ⟶ (Scheme.Modules.pushforward g).obj H}
    {I : InjectiveResolution F} {J : InjectiveResolution G} {K : InjectiveResolution H}
    {l : I.cocomplex ⟶ (onCochains (Scheme.Modules.pushforward f)).obj J.cocomplex}
    {t : J.cocomplex ⟶ (onCochains (Scheme.Modules.pushforward g)).obj K.cocomplex}
    (hl : IsLift f α I J l) (ht : IsLift g β J K t) :
    IsLift (g ≫ f)
      (α ≫ (Scheme.Modules.pushforward f).map β ≫
        (Scheme.Modules.pushforwardComp g f).hom.app H) I K (composeLifts f g l t) := by
  let P := Scheme.Modules.pushforward f
  let Q := Scheme.Modules.pushforward g
  let e := (Scheme.Modules.pushforwardComp g f).hom
  change I.ι.f 0 ≫ l.f 0 ≫ P.map (t.f 0) ≫ e.app (K.cocomplex.X 0) =
      (α ≫ P.map β ≫ e.app H) ≫ (Scheme.Modules.pushforward (g ≫ f)).map (K.ι.f 0)
  change I.ι.f 0 ≫ l.f 0 = α ≫ P.map (J.ι.f 0) at hl
  change J.ι.f 0 ≫ t.f 0 = β ≫ Q.map (K.ι.f 0) at ht
  rw [← Category.assoc (I.ι.f 0), hl, Category.assoc, ← P.map_comp_assoc, ht, P.map_comp,
    Category.assoc]
  have hn := e.naturality (K.ι.f 0)
  change P.map (Q.map (K.ι.f 0)) ≫ e.app (K.cocomplex.X 0) =
    e.app H ≫ (Scheme.Modules.pushforward (g ≫ f)).map (K.ι.f 0) at hn
  rw [hn]
  simp only [Category.assoc]

private theorem sectionsLift_comp (φ : A →+* B) (ψ : B →+* D)
    (f : Y.left ⟶ X.left) (g : Z.left ⟶ Y.left)
    (wf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (wg : g ≫ Y.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom ψ))
    {I : CochainComplex X.left.Modules ℕ} {J : CochainComplex Y.left.Modules ℕ}
    {K : CochainComplex Z.left.Modules ℕ}
    (l : I ⟶ (onCochains (Scheme.Modules.pushforward f)).obj J)
    (t : J ⟶ (onCochains (Scheme.Modules.pushforward g)).obj K) :
    sectionsLift (ψ.comp φ) (g ≫ f) (comp_over φ ψ f g wf wg) (composeLifts f g l t) =
      sectionsLift φ f wf l ≫ (onCochains (restrict φ)).map (sectionsLift ψ g wg t) ≫
        restrictCompComplex φ ψ ((onCochains (sections Z)).obj K) := by
  ext i : 1
  apply ModuleCat.hom_ext
  ext x : 1
  rfl

theorem cohomologyMapComp : CohomologyMapComp.{u} := by
  intro A B D _ _ _ X Y Z φ ψ f g hf hg wf wg F G H α β n m₁ m₂ h₁ h₂ I K
  let J := injectiveResolution G
  obtain ⟨⟨l, hl⟩, h₁'⟩ := h₁ I J
  obtain ⟨⟨t, ht⟩, h₂'⟩ := h₂ J K
  let e := ModuleCat.restrictScalarsComp φ ψ
  let w := comp_over φ ψ f g wf wg
  let γ := α ≫ (Scheme.Modules.pushforward f).map β ≫
    (Scheme.Modules.pushforwardComp g f).hom.app H
  let j := composeLifts f g l t
  have hj := composeLifts_isLift f g hl ht
  refine ⟨⟨j, hj⟩, ?_⟩
  intro v hv
  have : (Scheme.Modules.pushforward (g ≫ f)).PreservesInjectiveObjects :=
    flatPushforwardPreservesInjectives (g ≫ f)
  change m₁ ≫ (restrict φ).map m₂ ≫ e.inv.app _ =
    comparison (ψ.comp φ) (g ≫ f) w I K n v
  have hh := homology_of_lifts_eq (ψ.comp φ) (g ≫ f) w γ I K n hv hj
  simp only [comparison]
  rw [hh, sectionsLift_comp φ ψ f g wf wg, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  rw [reassoc_of% restrictHomology_comp φ ψ ((onCochains (sections Z)).obj K.cocomplex) n,
    reassoc_of% restrictHomology_natural φ (sectionsLift ψ g wg t) n, h₁' l hl, h₂' t ht]
  let kIso := K.isoRightDerivedObj (sections Z) n
  have hcancel : (restrict φ).map (J.isoRightDerivedObj (sections Y) n).inv ≫
      (restrict φ).map (J.isoRightDerivedObj (sections Y) n).hom =
        𝟙 ((restrict φ).obj (((onCochains (sections Y)).obj J.cocomplex).homology n)) := by
    rw [← (restrict φ).map_comp, Iso.inv_hom_id, (restrict φ).map_id]
    rfl
  have htail := e.inv.naturality kIso.inv
  change (restrict φ).map ((restrict ψ).map (K.isoRightDerivedObj (sections Z) n).inv) ≫
      e.inv.app ((cohomology Z n).obj H) =
      (ModuleCat.restrictScalarsComp φ ψ).inv.app (((onCochains (sections Z)).obj K.cocomplex).homology n) ≫
        (restrict (ψ.comp φ)).map (K.isoRightDerivedObj (sections Z) n).inv at htail
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hcancel, htail]
  apply congrArg (fun m => (I.isoRightDerivedObj (sections X) n).hom ≫
    HomologicalComplex.homologyMap (sectionsLift φ f wf l) n ≫
    (restrictHomology φ ((onCochains (sections Y)).obj J.cocomplex) n).hom ≫ m)
  exact Category.id_comp _

end Composition


section Identity

variable {A : Type u} [CommRing A]

private abbrev idRestriction :=
  ModuleCat.restrictScalarsId'.{u} (RingHom.id A) rfl

private def idRestrictionComplex (K : CochainComplex (ModuleCat.{u} A) ℕ) :
    K ⟶ (onCochains (restrict (RingHom.id A))).obj K :=
  (idRestriction.inv.mapHomologicalComplex (.up ℕ)).app K

private theorem restrictHomology_id (K : CochainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (idRestrictionComplex K) n ≫
      (restrictHomology (RingHom.id A) K n).hom = idRestriction.inv.app (K.homology n) := by
  let S := K.sc n
  have h := S.homologyMap_mapNatTrans idRestriction.inv
  change HomologicalComplex.homologyMap (idRestrictionComplex K) n =
    (S.mapHomologyIso (𝟭 _)).hom ≫ idRestriction.inv.app S.homology ≫
      (restrictHomology (RingHom.id A) K n).inv at h
  rw [h, comparison_id]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem cohomologyMapId : CohomologyMapId.{u} := by
  intro A _ X F G α n I J
  let f : X.left ⟶ X.left := 𝟙 _
  let w : f ≫ X.hom = X.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id A)) := by simp [f]
  let P := Scheme.Modules.pushforward f
  let e := Scheme.Modules.pushforwardId X.left
  let β := α ≫ e.inv.app G
  let t := InjectiveResolution.desc α J I
  let j : J.cocomplex ⟶ (onCochains P).obj J.cocomplex :=
    (e.inv.mapHomologicalComplex (.up ℕ)).app J.cocomplex
  have h : IsLift f β I J (t ≫ j) := by
    change I.ι.f 0 ≫ t.f 0 ≫ e.inv.app (J.cocomplex.X 0) =
      (α ≫ e.inv.app G) ≫ P.map (J.ι.f 0)
    have he := e.inv.naturality (J.ι.f 0)
    change J.ι.f 0 ≫ e.inv.app (J.cocomplex.X 0) = e.inv.app G ≫ P.map (J.ι.f 0) at he
    rw [← Category.assoc, InjectiveResolution.desc_commutes_zero, Category.assoc,
      he, Category.assoc]
  refine ⟨⟨t ≫ j, h⟩, fun l hl => ?_⟩
  have : P.PreservesInjectiveObjects := flatPushforwardPreservesInjectives f
  have hh := homology_of_lifts_eq (RingHom.id A) f w β I J n hl h
  have hs : sectionsLift (RingHom.id A) f w (t ≫ j) =
      (onCochains (sections X)).map t ≫
        idRestrictionComplex ((onCochains (sections X)).obj J.cocomplex) := by
    ext i : 1
    apply ModuleCat.hom_ext
    ext x : 1
    rfl
  have hj := InjectiveResolution.isoRightDerivedObj_hom_naturality α I J t
    (InjectiveResolution.desc_commutes_zero α J I) (sections X) n
  change (cohomology X n).map α ≫ (J.isoRightDerivedObj (sections X) n).hom =
    (I.isoRightDerivedObj (sections X) n).hom ≫
      HomologicalComplex.homologyMap ((onCochains (sections X)).map t) n at hj
  change (cohomology X n).map α ≫ idRestriction.inv.app _ =
    comparison (RingHom.id A) f w I J n l
  rw [comparison, hh, hs, HomologicalComplex.homologyMap_comp, Category.assoc,
    reassoc_of% restrictHomology_id ((onCochains (sections X)).obj J.cocomplex) n,
    ← reassoc_of% hj]
  have hn := ModuleCat.restrictScalarsId'App_inv_naturality (RingHom.id A) rfl
    (J.isoRightDerivedObj (sections X) n).inv
  change (J.isoRightDerivedObj (sections X) n).inv ≫
      idRestriction.inv.app ((cohomology X n).obj G) =
    idRestriction.inv.app (((onCochains (sections X)).obj J.cocomplex).homology n) ≫
      (restrict (RingHom.id A)).map (J.isoRightDerivedObj (sections X) n).inv at hn
  rw [← hn, Iso.hom_inv_id_assoc]
  rfl

end Identity

theorem scalarExtensionCohomologyMap : HasScalarExtensionCohomologyMap.{u} := by
  intro k R _ _ _ X F n Y p a H H'
  have : Flat p := flatScalarExtension k R X
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap k R)
  obtain ⟨m, hm, hu⟩ := flatCohomologyMap (X := X) (Y := Y) (algebraMap k R) p
    (scalarExtension_over k R X) (a.unit.app F) n
  refine ⟨(adj.homEquiv H H').symm m, ?_, ?_⟩
  · change IsCohomologyMap (X := X) (Y := Y) (algebraMap k R) p
      (scalarExtension_over k R X) (a.unit.app F) n
      ((adj.homEquiv H H') ((adj.homEquiv H H').symm m))
    rw [Equiv.apply_symm_apply]
    exact hm
  · intro m' hm'
    apply (adj.homEquiv H H').injective
    rw [Equiv.apply_symm_apply]
    exact hu _ hm'

end LinearAlgebraicGroups.FlatCohomology
