import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Exact
-- Contains adaptations from Mathlib (Joël Riou, Apache-2.0). See the notice below.
/-!
Proof of the sheaf-category preliminaries at source lines 3525–3556.
There are no additional assumptions on the space or on the ring sheaf.
Exact stalks and skyscrapers give injective embeddings. Explicit presheaf
zero extension and sheafification establish exact extension by zero.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits
open AdvancedHomologicalAlgebra.SheafTheory

universe u

namespace AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction

variable {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X)

variable (x : X)

instance stalkPreservesFiniteLimits : PreservesFiniteLimits (stalkFunctor R x) := by
  let h₁ : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R) := by infer_instance
  let h₂ : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by
    infer_instance
  have : PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u} R ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)) := by
    exact comp_preservesFiniteLimits (SheafOfModules.toSheaf.{u} R)
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  have : PreservesFiniteLimits
      (stalkFunctor R x ⋙ forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso (stalkForgetIso R x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (stalkFunctor R x)
    (forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u})

lemma stalkFunctor_map_germ {M N : Modules R} (f : M ⟶ N)
    (U : Opens X) (hx : x ∈ U) (s : M.val.obj (op U)) :
    (stalkFunctor R x).map f (TopCat.Presheaf.germ M.val.presheaf U x hx s) =
      TopCat.Presheaf.germ N.val.presheaf U x hx (f.val.app (op U) s) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf R.obj).map f.val) s

instance stalkAdditive : (stalkFunctor R x).Additive := by
  constructor
  intro M N f g
  ext s
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf s
  change (stalkFunctor R x).map (f + g) _ =
    (stalkFunctor R x).map f _ + (stalkFunctor R x).map g _
  rw [stalkFunctor_map_germ, stalkFunctor_map_germ, stalkFunctor_map_germ]
  change TopCat.Presheaf.germ N.val.presheaf U x hx
    (f.val.app (op U) s + g.val.app (op U) s) = _
  exact map_add _ _ _

instance toSheafPreservesFiniteColimits : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) where
  preservesFiniteColimits J _ _ := by
    constructor
    intro F
    let S := PresheafOfModules.sheafification (𝟙 R.obj)
    let T := SheafOfModules.forget R
    let A := SheafOfModules.toSheaf R
    have : PreservesColimitsOfShape J (S ⋙ A) := by
      change PreservesColimitsOfShape J
        (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf _ AddCommGrpCat.{u})
      infer_instance
    let c := colimit.cocone (F ⋙ T)
    let t : IsColimit (S.mapCocone c) := isColimitOfPreserves S (colimit.isColimit (F ⋙ T))
    have : PreservesColimit ((F ⋙ T) ⋙ S) A :=
      preservesColimit_of_preserves_colimit_cocone t
        (isColimitOfPreserves (S ⋙ A) (colimit.isColimit (F ⋙ T)))
    have e : ((F ⋙ T) ⋙ S) ≅ F :=
      Functor.isoWhiskerLeft F (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit)
    exact preservesColimit_of_iso_diagram A e

instance stalkPreservesFiniteColimits : PreservesFiniteColimits (stalkFunctor R x) := by
  have : PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by
    classical
    have : PreservesColimitsOfSize.{0, 0}
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
      (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) x).leftAdjoint_preservesColimits
    infer_instance
  have : PreservesFiniteColimits
      (SheafOfModules.toSheaf.{u} R ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)) := by
    exact comp_preservesFiniteColimits (SheafOfModules.toSheaf.{u} R)
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  have : PreservesFiniteColimits
      (stalkFunctor R x ⋙ forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u}) :=
    preservesFiniteColimits_of_natIso (stalkForgetIso R x).symm
  exact preservesFiniteColimits_of_reflects_of_preserves (stalkFunctor R x)
    (forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u})

namespace Expected
open Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction

theorem stalk_exact : stalkExact.{u} := by
  intro X R x
  exact ⟨inferInstance, inferInstance⟩

end Expected

def skyscraperSectionsEquiv (N : ModuleCat.{u} (stalkRing R x))
    (U : Opens X) (hx : x ∈ U) : sections R (skyscraper R x N) U ≃+ N :=
  { toFun := fun s ↦ s ⟨hx⟩
    invFun := fun n _ ↦ n
    left_inv := by intro s; rfl
    right_inv := by intro n; rfl
    map_add' := by intros; rfl }

lemma skyscraperSections_smul (N : ModuleCat.{u} (stalkRing R x))
    (U : Opens X) (hx : x ∈ U) (r : sectionRing R U) (s : sections R (skyscraper R x N) U) :
    skyscraperSectionsEquiv R x N U hx (r • s) =
      (TopCat.Presheaf.germ R.obj U x hx) r • skyscraperSectionsEquiv R x N U hx s := rfl

lemma skyscraperSections_zero (N : ModuleCat.{u} (stalkRing R x))
    (U : Opens X) (hx : x ∉ U) : Subsingleton (sections R (skyscraper R x N) U) := by
  have : IsEmpty (PLift (x ∈ U)) := ⟨fun h ↦ hx h.down⟩
  exact inferInstanceAs (Subsingleton (PLift (x ∈ U) → N))

/-- A linear map on germs determines a morphism to the skyscraper. -/
def toSkyscraper {M : Modules R} {N : ModuleCat.{u} (stalkRing R x)}
    (f : stalkModule R x M ⟶ N) : M ⟶ skyscraper R x N :=
  ⟨{
    app U := ModuleCat.ofHom
      { toFun := fun s hx ↦ f (TopCat.Presheaf.germ M.val.presheaf U.unop x hx.down s)
        map_add' := by
          intro s t
          funext hx
          simp only [map_add]
          rfl
        map_smul' := by
          intro r s
          funext hx
          change f (TopCat.Presheaf.germ M.val.presheaf U.unop x hx.down (r • s)) =
            (TopCat.Presheaf.germ R.obj U.unop x hx.down) r •
              f (TopCat.Presheaf.germ M.val.presheaf U.unop x hx.down s)
          rw [M.val.germ_ringCat_smul]
          exact f.hom.map_smul _ _ }
    naturality := by
      intro U V i
      ext s
      funext hx
      change f (TopCat.Presheaf.germ M.val.presheaf V.unop x hx.down (M.val.map i s)) =
        f (TopCat.Presheaf.germ M.val.presheaf U.unop x (i.unop.le hx.down) s)
      congr 1
      exact TopCat.Presheaf.germ_res_apply M.val.presheaf i.unop x hx.down s }⟩

/-- A morphism to the skyscraper gives compatible values on germs. -/
def fromSkyscraperAdd {M : Modules R} {N : ModuleCat.{u} (stalkRing R x)}
    (f : M ⟶ skyscraper R x N) :
    TopCat.Presheaf.stalk M.val.presheaf x ⟶ ((forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u}).obj N) :=
  colimit.desc _
    { pt := ((forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u}).obj N)
      ι :=
        { app U := AddCommGrpCat.ofHom
            { toFun := fun s ↦ f.val.app (op U.unop.1) s ⟨U.unop.2⟩
              map_zero' := by rw [(f.val.app (op U.unop.1)).hom.map_zero]; rfl
              map_add' := by intro s t; rw [(f.val.app (op U.unop.1)).hom.map_add]; rfl }
          naturality := by
            intro U V i
            ext s
            change f.val.app (op V.unop.1) (M.val.map ((OpenNhds.inclusion x).op.map i) s) _ = _
            have h := congr($(f.val.naturality ((OpenNhds.inclusion x).op.map i)) s)
            exact congrFun h ⟨V.unop.2⟩ } }

lemma germ_fromSkyscraperAdd {M : Modules R} {N : ModuleCat.{u} (stalkRing R x)}
    (f : M ⟶ skyscraper R x N) (U : Opens X) (hx : x ∈ U) (s : sections R M U) :
    fromSkyscraperAdd R x f (TopCat.Presheaf.germ M.val.presheaf U x hx s) =
      f.val.app (op U) s ⟨hx⟩ := by
  change ((colimit.ι ((OpenNhds.inclusion x).op ⋙ M.val.presheaf) (op (⟨U, hx⟩ : OpenNhds x))) ≫
    colimit.desc _ _) s = _
  rw [colimit.ι_desc]
  rfl

def fromSkyscraper {M : Modules R} {N : ModuleCat.{u} (stalkRing R x)}
    (f : M ⟶ skyscraper R x N) : stalkModule R x M ⟶ N :=
  ModuleCat.ofHom
    { toFun := fromSkyscraperAdd R x f
      map_add' := map_add _
      map_smul' := by
        intro r m
        obtain ⟨U, hx, a, s, rfl, rfl⟩ := stalkGermsJoint R x M r m
        rw [← M.val.germ_ringCat_smul, germ_fromSkyscraperAdd, germ_fromSkyscraperAdd]
        exact congrFun ((f.val.app (op U)).hom.map_smul a s) ⟨hx⟩ }

lemma to_fromSkyscraper {M : Modules R} {N : ModuleCat.{u} (stalkRing R x)}
    (f : M ⟶ skyscraper R x N) : toSkyscraper R x (fromSkyscraper R x f) = f := by
  ext U s
  funext hx
  change fromSkyscraperAdd R x f (TopCat.Presheaf.germ M.val.presheaf U.unop x hx.down s) = _
  exact germ_fromSkyscraperAdd R x f U.unop hx.down s

lemma from_toSkyscraper {M : Modules R} {N : ModuleCat.{u} (stalkRing R x)}
    (f : stalkModule R x M ⟶ N) : fromSkyscraper R x (toSkyscraper R x f) = f := by
  ext m
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  change fromSkyscraperAdd R x (toSkyscraper R x f)
    (TopCat.Presheaf.germ M.val.presheaf U x hx s) = _
  rw [germ_fromSkyscraperAdd]
  rfl

def stalkSkyscraperHomEquiv (M : Modules R) (N : ModuleCat.{u} (stalkRing R x)) :
    (stalkModule R x M ⟶ N) ≃ (M ⟶ skyscraper R x N) where
  toFun := toSkyscraper R x
  invFun := fromSkyscraper R x
  left_inv := from_toSkyscraper R x
  right_inv := to_fromSkyscraper R x

def stalkSkyscraperAdjunction : stalkFunctor R x ⊣ skyscraperFunctor R x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := stalkSkyscraperHomEquiv R x
      homEquiv_naturality_left_symm := by
        intro M P N f g
        ext m
        obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
        change fromSkyscraperAdd R x (f ≫ g) (TopCat.Presheaf.germ M.val.presheaf U x hx s) =
          fromSkyscraperAdd R x g ((stalkFunctor R x).map f (TopCat.Presheaf.germ M.val.presheaf U x hx s))
        rw [AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction.stalkFunctor_map_germ, germ_fromSkyscraperAdd, germ_fromSkyscraperAdd]
        rfl
      homEquiv_naturality_right := by
        intro M N P f g
        ext U s
        funext hx
        rfl }

lemma mono_of_stalk_map_mono {M N : Modules R} (f : M ⟶ N)
    [∀ x : X, Mono ((stalkFunctor R x).map f)] : Mono f := by
  apply (SheafOfModules.toSheaf R).mono_of_mono_map
  have (x : X) : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((SheafOfModules.toSheaf R).map f).hom) := by
    change Mono ((forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u}).map
      ((stalkFunctor R x).map f))
    infer_instance
  exact TopCat.Presheaf.mono_of_stalk_mono _

abbrev injectiveSkyscrapers (M : Modules R) (x : X) : Modules R :=
  (skyscraperFunctor R x).obj (Injective.under ((stalkFunctor R x).obj M))

def stalkInjectiveEmbedding (M : Modules R) : M ⟶ ∏ᶜ (injectiveSkyscrapers R M) :=
  Pi.lift (fun x ↦ (stalkSkyscraperAdjunction R x).homEquiv M _ (Injective.ι ((stalkFunctor R x).obj M)))

lemma injectiveSkyscraperProduct (M : Modules R) :
    Injective (∏ᶜ (injectiveSkyscrapers R M)) := by
  have (x : X) : Injective (injectiveSkyscrapers R M x) :=
    (stalkSkyscraperAdjunction R x).map_injective _ inferInstance
  infer_instance

instance stalkInjectiveEmbedding_mono (M : Modules R) : Mono (stalkInjectiveEmbedding R M) := by
  suffices ∀ x : X, Mono ((stalkFunctor R x).map (stalkInjectiveEmbedding R M)) from
    @mono_of_stalk_map_mono X R _ _ (stalkInjectiveEmbedding R M) this
  intro x
  let i := Injective.ι ((stalkFunctor R x).obj M)
  let f := (stalkSkyscraperAdjunction R x).homEquiv M _ i
  have hf : (stalkFunctor R x).map f ≫ (stalkSkyscraperAdjunction R x).counit.app _ = i := by
    calc
      _ = ((stalkSkyscraperAdjunction R x).homEquiv M _).symm f := ((stalkSkyscraperAdjunction R x).homEquiv_counit M _ f).symm
      _ = i := ((stalkSkyscraperAdjunction R x).homEquiv M _).symm_apply_apply i
  have : Mono ((stalkFunctor R x).map f) := by
    apply mono_of_mono_fac hf
  have h : (stalkFunctor R x).map (stalkInjectiveEmbedding R M) ≫
      (stalkFunctor R x).map (Pi.π (injectiveSkyscrapers R M) x) =
      (stalkFunctor R x).map f := by
    rw [← Functor.map_comp]
    simp only [stalkInjectiveEmbedding, limit.lift_π]
    rfl
  exact mono_of_mono_fac h

/-- The source construction: embed every stalk and take the product of its
injective skyscrapers. Exact stalks ensure that each factor is injective. -/
theorem enoughInjectivesByStalks : EnoughInjectives (Modules R) where
  presentation M := ⟨{
    J := ∏ᶜ (injectiveSkyscrapers R M)
    injective := injectiveSkyscraperProduct R M
    f := stalkInjectiveEmbedding R M
    mono := inferInstance }⟩

namespace Expected
open Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction

theorem skyscraper_adjoint : skyscraperAdjoint.{u} := by
  intro X R x
  exact ⟨stalkSkyscraperAdjunction R x⟩

theorem skyscraper_sections : skyscraperSections.{u} := by
  intro X R x N U
  exact ⟨fun hx ↦ ⟨skyscraperSectionsEquiv R x N U hx,
    skyscraperSections_smul R x N U hx⟩, skyscraperSections_zero R x N U⟩

theorem skyscraper_injective : skyscraperInjective.{u} := by
  intro X R x N hN
  exact (stalkSkyscraperAdjunction R x).map_injective N hN

end Expected

noncomputable def extensionAdjunction : extensionByZero R U ⊣ restriction R U :=
  (U.sheafOfModulesEquivOver R).symm.toAdjunction.comp
    (Adjunction.ofIsRightAdjoint (SheafOfModules.overFunctor R U))
abbrev overRing : (Over U)ᵒᵖ ⥤ RingCat.{u} := (Over.forget U).op ⋙ R.obj

abbrev zeroExtendObj (M : PresheafOfModules.{u} (overRing R U)) (W : (Opens X)ᵒᵖ) :
    ModuleCat.{u} (R.obj.obj W) :=
  ModuleCat.of _ (∀ h : PLift (W.unop ≤ U), M.obj (op (Over.mk (homOfLE h.down))))

def zeroExtendMap (M : PresheafOfModules.{u} (overRing R U))
    {W V : (Opens X)ᵒᵖ} (f : W ⟶ V) :
    zeroExtendObj R U M W ⟶
      (ModuleCat.restrictScalars (R.obj.map f).hom).obj (zeroExtendObj R U M V) := by
  classical
  exact ModuleCat.semilinearMapAddEquiv (R.obj.map f).hom
    (zeroExtendObj R U M W) (zeroExtendObj R U M V)
    { toFun := fun m hV ↦ if hW : W.unop ≤ U then
        M.map (Over.homMk (V := Over.mk (homOfLE hW))
          (U := Over.mk (homOfLE hV.down)) f.unop).op (m ⟨hW⟩) else 0
      map_add' := by
        intros x y
        funext hV
        split_ifs with hW
        · simpa only [zeroExtendObj, Pi.add_apply] using
            (M.map (Over.homMk (V := Over.mk (homOfLE hW))
              (U := Over.mk (homOfLE hV.down)) f.unop).op).hom.map_add (x ⟨hW⟩) (y ⟨hW⟩)
        · simp [zeroExtendObj]
      map_smul' := by
        intros r x
        funext hV
        split_ifs <;> simp [zeroExtendObj] }

lemma zeroExtendMap_apply (M : PresheafOfModules.{u} (overRing R U))
    {W V : (Opens X)ᵒᵖ} (f : W ⟶ V) (m : zeroExtendObj R U M W) (hV : PLift (V.unop ≤ U))
    (hW : W.unop ≤ U) :
    zeroExtendMap R U M f m hV = M.map
      (Over.homMk (V := Over.mk (homOfLE hW))
        (U := Over.mk (homOfLE hV.down)) f.unop).op (m ⟨hW⟩) := by
  classical
  simp [zeroExtendMap, ModuleCat.semilinearMapAddEquiv, hW]

lemma zeroExtendMap_id (M : PresheafOfModules.{u} (overRing R U)) (W : (Opens X)ᵒᵖ)
    (m : zeroExtendObj R U M W) : zeroExtendMap R U M (𝟙 W) m = m := by
  funext hW
  rw [zeroExtendMap_apply _ _ _ _ _ _ hW.down]
  change M.presheaf.map (𝟙 _) (m hW) = m hW
  simp

lemma zeroExtendMap_comp (M : PresheafOfModules.{u} (overRing R U))
    {W V Z : (Opens X)ᵒᵖ} (f : W ⟶ V) (g : V ⟶ Z)
    (m : zeroExtendObj R U M W) :
    zeroExtendMap R U M (f ≫ g) m = zeroExtendMap R U M g (zeroExtendMap R U M f m) := by
  classical
  funext hZ
  by_cases hW : W.unop ≤ U
  · have hV : V.unop ≤ U := (leOfHom f.unop).trans hW
    rw [zeroExtendMap_apply _ _ _ _ _ _ hW, zeroExtendMap_apply _ _ _ _ _ _ hV,
      zeroExtendMap_apply _ _ _ _ _ _ hW]
    exact M.map_comp_apply _ _ _
  · simp only [zeroExtendMap, ModuleCat.semilinearMapAddEquiv, hW, ↓reduceDIte,
      AddEquiv.coe_mk]
    by_cases hV : V.unop ≤ U <;> simp [hV]
    exact (M.map (Over.homMk (V := Over.mk (homOfLE hV))
      (U := Over.mk (homOfLE hZ.down)) g.unop).op).hom.map_zero.symm

def zeroExtend (M : PresheafOfModules.{u} (overRing R U)) : PresheafOfModules.{u} R.obj where
  obj := zeroExtendObj R U M
  map := zeroExtendMap R U M
  map_id W := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro m; exact zeroExtendMap_id R U M W m
  map_comp f g := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro m; exact zeroExtendMap_comp R U M f g m

lemma zeroExtendMap_of_not_le (M : PresheafOfModules.{u} (overRing R U))
    {W V : (Opens X)ᵒᵖ} (f : W ⟶ V) (m : zeroExtendObj R U M W)
    (hW : ¬ W.unop ≤ U) : zeroExtendMap R U M f m = 0 := by
  classical
  funext hV
  simp only [zeroExtendMap, ModuleCat.semilinearMapAddEquiv, dite_eq_right hW]
  rfl

def zeroExtendHom {M N : PresheafOfModules.{u} (overRing R U)} (f : M ⟶ N) :
    zeroExtend R U M ⟶ zeroExtend R U N where
  app W := ModuleCat.ofHom (X := zeroExtendObj R U M W) (Y := zeroExtendObj R U N W)
    { toFun := fun m hW ↦ f.app _ (m hW)
      map_add' := by intros; funext hW; exact (f.app _).hom.map_add _ _
      map_smul' := by intros; funext hW; exact (f.app _).hom.map_smul _ _ }
  naturality {W V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    funext hV
    by_cases hW : W.unop ≤ U
    · change f.app _ (zeroExtendMap R U M i m hV) =
        zeroExtendMap R U N i (fun hW ↦ f.app _ (m hW)) hV
      rw [zeroExtendMap_apply _ _ _ _ _ _ hW, zeroExtendMap_apply _ _ _ _ _ _ hW]
      exact PresheafOfModules.naturality_apply f _ _
    · change f.app _ (zeroExtendMap R U M i m hV) = zeroExtendMap R U N i _ hV
      rw [zeroExtendMap_of_not_le _ _ _ _ _ hW, zeroExtendMap_of_not_le _ _ _ _ _ hW]
      exact (f.app _).hom.map_zero

def zeroExtendFunctor : PresheafOfModules.{u} (overRing R U) ⥤ PresheafOfModules.{u} R.obj where
  obj := zeroExtend R U
  map := zeroExtendHom R U
  map_id M := by ext W m; rfl
  map_comp f g := by ext W m; rfl

instance zeroExtendFunctor_preservesMonomorphisms : (zeroExtendFunctor R U).PreservesMonomorphisms where
  preserves f hf := by
    apply PresheafOfModules.mono_of_injective
    intro W m n h
    funext hW
    exact (ModuleCat.mono_iff_injective (f.app (op (Over.mk (homOfLE hW.down))))).1
      (inferInstance) (congrFun h hW)

abbrev overPresheafFunctor : PresheafOfModules.{u} R.obj ⥤ PresheafOfModules.{u} (overRing R U) :=
  PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)

def zeroExtendUnit (M : PresheafOfModules.{u} (overRing R U)) :
    M ⟶ (overPresheafFunctor R U).obj ((zeroExtendFunctor R U).obj M) where
  app W := ModuleCat.ofHom (X := M.obj W)
    (Y := zeroExtendObj R U M (op W.unop.left))
    { toFun := fun m _ ↦ m
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  naturality {W V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    funext hV
    change _ = zeroExtendMap R U M (f.unop.left).op (fun _ ↦ m) hV
    rw [zeroExtendMap_apply _ _ _ _ _ _ (leOfHom W.unop.hom)]
    rfl

def zeroExtendCounit (M : PresheafOfModules.{u} R.obj) :
    (zeroExtendFunctor R U).obj ((overPresheafFunctor R U).obj M) ⟶ M where
  app W := by
    classical
    exact ModuleCat.ofHom (X := zeroExtendObj R U ((overPresheafFunctor R U).obj M) W)
      (Y := M.obj W)
      { toFun := fun m ↦ if hW : W.unop ≤ U then m ⟨hW⟩ else 0
        map_add' := by intros; split_ifs <;> simp [zeroExtendObj]
        map_smul' := by intros; split_ifs <;> simp [zeroExtendObj] }
  naturality {W V} f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (if hV : V.unop ≤ U then
      zeroExtendMap R U ((overPresheafFunctor R U).obj M) f m ⟨hV⟩ else 0) =
      M.map f (if hW : W.unop ≤ U then m ⟨hW⟩ else 0)
    by_cases hW : W.unop ≤ U
    · have hV : V.unop ≤ U := (leOfHom f.unop).trans hW
      simp only [hW, hV, ↓reduceDIte]
      rw [zeroExtendMap_apply _ _ _ _ _ _ hW]
      rfl
    · simp only [hW, ↓reduceDIte]
      rw [zeroExtendMap_of_not_le _ _ _ _ _ hW]
      split_ifs <;> exact (M.map f).hom.map_zero.symm


def zeroExtendAdjunction : zeroExtendFunctor R U ⊣ overPresheafFunctor R U where
  unit :=
    { app := zeroExtendUnit R U
      naturality := by intros; ext W m; rfl }
  counit :=
    { app := zeroExtendCounit R U
      naturality := by
        classical
        intro M N f
        ext W m
        change (if hW : W.unop ≤ U then f.app W (m ⟨hW⟩) else 0) =
          f.app W (if hW : W.unop ≤ U then m ⟨hW⟩ else 0)
        split_ifs
        · rfl
        · exact (f.app W).hom.map_zero.symm }
  left_triangle_components M := by
    classical
    ext W m
    funext hW
    change (if h : W.unop ≤ U then fun _ : PLift (W.unop ≤ U) ↦ m ⟨h⟩ else (0 : zeroExtendObj R U M W)) hW = m hW
    simp only [hW.down, ↓reduceDIte]
  right_triangle_components M := by
    classical
    ext W m
    change (if h : W.unop.left ≤ U then m else 0) = m
    simp only [leOfHom W.unop.hom, ↓reduceDIte]

def explicitExtension : SheafOfModules.{u} (R.over U) ⥤ Modules R :=
  SheafOfModules.forget.{u} (R.over U) ⋙ zeroExtendFunctor R U ⋙
    PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)

instance explicitExtension_preservesMonomorphisms : (explicitExtension R U).PreservesMonomorphisms := by
  have : (SheafOfModules.forget.{u} (R.over U)).PreservesMonomorphisms := by infer_instance
  have : (zeroExtendFunctor R U).PreservesMonomorphisms := by infer_instance
  have : (PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).PreservesMonomorphisms := by infer_instance
  unfold explicitExtension
  infer_instance

def explicitExtensionAdjunction : explicitExtension R U ⊣ SheafOfModules.overFunctor R U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G ↦
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).trans
          (((zeroExtendAdjunction R U).homEquiv F.val G.val).trans
            ((SheafOfModules.fullyFaithfulForget (R.over U)).homEquiv
              (Y := (SheafOfModules.overFunctor R U).obj G)).symm)
      homEquiv_naturality_left_symm := by
        intros
        dsimp [Functor.FullyFaithful.homEquiv]
        erw [Adjunction.homEquiv_naturality_left_symm,
          Adjunction.homEquiv_naturality_left_symm]
        dsimp [SheafOfModules.pushforward_obj_val]
        simp only [Functor.map_comp, Category.assoc]
        rfl
      homEquiv_naturality_right := by
        tauto }

/-- Transfer preservation of monomorphisms along the isomorphism of left adjoints. -/
lemma extensionFromOver_preservesMonomorphisms
    (L : SheafOfModules.{u} (R.over U) ⥤ Modules R)
    (adj : L ⊣ SheafOfModules.overFunctor R U) [L.PreservesMonomorphisms] :
    (extensionFromOver R U).PreservesMonomorphisms := by
  exact Functor.PreservesMonomorphisms.of_iso
    (Adjunction.leftAdjointUniq adj
      (Adjunction.ofIsRightAdjoint (SheafOfModules.overFunctor R U)))

instance extensionFromOverPreservesMonomorphisms :
    (extensionFromOver R U).PreservesMonomorphisms :=
  extensionFromOver_preservesMonomorphisms R U (explicitExtension R U)
    (explicitExtensionAdjunction R U)

instance extensionPreservesFiniteLimits :
    PreservesFiniteLimits (extensionByZero R U) := by
  have : (extensionByZero R U).PreservesMonomorphisms := by
    unfold extensionByZero
    infer_instance
  let := (extensionAdjunction R U).isLeftAdjoint
  have : PreservesBinaryBiproducts (extensionByZero R U) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (extensionByZero R U).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have : (extensionByZero R U).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

lemma restriction_injective
    (I : Modules R) (hI : Injective I) : Injective ((restriction R U).obj I) := by
  have : (extensionByZero R U).PreservesMonomorphisms := by
    unfold extensionByZero
    infer_instance
  exact (extensionAdjunction R U).map_injective I hI

namespace Expected
open Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction

theorem extension_exact : extensionExact.{u} := by
  intro X R U
  let := (extensionAdjunction R U).isLeftAdjoint
  exact ⟨inferInstance, inferInstance⟩

theorem restriction_preserves_injectives : restrictionPreservesInjectives.{u} := by
  intro X R U I hI
  exact restriction_injective R U I hI

end Expected

noncomputable def homOpenUnit (M : SheafOfModules.{u} R) :
    ((extensionByZero R U).obj (SheafOfModules.unit _) ⟶ M) ≃ M.val.obj (op U) :=
  ((Iso.homCongr (openUnitIso R U) (Iso.refl M)).trans
    ((Adjunction.ofIsRightAdjoint (SheafOfModules.overFunctor R U)).homEquiv _ M)).trans
      ((M.over U).unitHomEquiv.trans (overSections R U M))

/-- The section representation evaluates a morphism on the adjunction's
distinguished section of the extended open unit. -/
lemma homOpenUnit_eval (M : Modules R) (f : openUnit R U ⟶ M) :
    homOpenUnit R U M f = f.val.app (op U) (openUnitGenerator R U) := by
  simp only [homOpenUnit, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id, Adjunction.homEquiv_unit]
  rfl

lemma homOpenUnit_naturality {M N : SheafOfModules.{u} R}
    (f : (extensionByZero R U).obj (SheafOfModules.unit _) ⟶ M) (g : M ⟶ N) :
    homOpenUnit R U N (f ≫ g) = g.val.app (op U) (homOpenUnit R U M f) := by
  simp only [homOpenUnit, Equiv.trans_apply, Iso.homCongr_apply]
  simp only [Iso.refl_hom, Category.comp_id]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  rfl

lemma homOpenUnit_add {M : SheafOfModules.{u} R}
    (f g : (extensionByZero R U).obj (SheafOfModules.unit _) ⟶ M) :
    homOpenUnit R U M (f + g) = homOpenUnit R U M f + homOpenUnit R U M g := by
  simp only [homOpenUnit, Equiv.trans_apply, Iso.homCongr_apply]
  simp only [Iso.refl_hom, Category.comp_id, Preadditive.comp_add]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rfl

lemma overUnitRightMul_apply (r : sectionRing R U) (a : sectionRing R U) :
    (overUnitRightMul R U r).val.app (op (Over.mk (𝟙 U))) a = a * r := by
  let e := sectionsAtInitial (SheafOfModules.unit (R.over U)).val
    (op (Over.mk (𝟙 U))) ((Over.mkIdTerminal (X := U)).op _)
  change a * (show sectionRing R U from (e.symm r).val (op (Over.mk (𝟙 U)))) = a * r
  have h := e.apply_symm_apply r
  change (e.symm r).val (op (Over.mk (𝟙 U))) = r at h
  rw [h]

lemma homOpenUnit_smul (M : Modules R) (r : sectionRing R U)
    (f : openUnit R U ⟶ M) :
    homOpenUnit R U M (openRightMul R U r ≫ f) = r • homOpenUnit R U M f := by
  simp only [homOpenUnit, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id, openRightMul]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  simp only [Category.assoc]
  rw [Adjunction.homEquiv_naturality_left]
  let g : SheafOfModules.unit (R.over U) ⟶ M.over U :=
    ((Adjunction.ofIsRightAdjoint (SheafOfModules.overFunctor R U)).homEquiv _ M)
      ((openUnitIso R U).inv ≫ f)
  change g.val.app (op (Over.mk (𝟙 U)))
    ((overUnitRightMul R U r).val.app (op (Over.mk (𝟙 U))) (1 : sectionRing R U)) =
    r • g.val.app (op (Over.mk (𝟙 U))) (1 : sectionRing R U)
  rw [overUnitRightMul_apply, one_mul]
  simpa using (g.val.app (op (Over.mk (𝟙 U)))).hom.map_smul r (1 : sectionRing R U)

instance openUnitHomSMul (M : Modules R) : SMul (sectionRing R U) (openUnit R U ⟶ M) where
  smul r f := openRightMul R U r ≫ f

def homOpenUnitAddEquiv (M : Modules R) : (openUnit R U ⟶ M) ≃+ sections R M U where
  __ := homOpenUnit R U M
  map_add' := homOpenUnit_add R U

instance openUnitHomModule (M : Modules R) : Module (sectionRing R U) (openUnit R U ⟶ M) :=
  Function.Injective.module (sectionRing R U) (homOpenUnitAddEquiv R U M).toAddMonoidHom
    (homOpenUnitAddEquiv R U M).injective
    (fun r f ↦ homOpenUnit_smul R U M r f)

def homOpenUnitLinearEquiv (M : Modules R) : (openUnit R U ⟶ M) ≃ₗ[sectionRing R U] sections R M U where
  __ := homOpenUnitAddEquiv R U M
  map_smul' := fun r f ↦ homOpenUnit_smul R U M r f

lemma flasque_iff (M : SheafOfModules.{u} R) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M) ↔
      ∀ (V W : Opens X) (h : V ≤ W), Function.Surjective (M.val.map (homOfLE h).op) := by
  constructor
  · intro h V W i
    have : Epi (M.val.presheaf.map (homOfLE i).op) := h.epi _
    exact (AddCommGrpCat.epi_iff_surjective _).mp this
  · intro h
    constructor
    intro V W i
    exact (AddCommGrpCat.epi_iff_surjective _).mpr (h W.unop V.unop (leOfHom i.unop))

noncomputable def freeOnOpen : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))
noncomputable def freeOnOpenHom (M : SheafOfModules.{u} R) :
    (freeOnOpen R U ⟶ M) ≃ M.val.obj (op U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ M).trans
    PresheafOfModules.freeYonedaEquiv
noncomputable def freeOnOpenMap {V W : Opens X} (i : V ⟶ W) :
    freeOnOpen R V ⟶ freeOnOpen R W :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (yoneda.map i))
lemma freeOnOpenMap_mono {V W : Opens X} (i : V ⟶ W) :
    Mono (freeOnOpenMap R i) := by
  have : Mono ((PresheafOfModules.free R.obj).map (yoneda.map i)) := by
    apply PresheafOfModules.mono_of_injective
    intro Z
    exact Finsupp.mapDomain_injective (fun a b h ↦ (cancel_mono i).mp h)
  apply Functor.map_mono
lemma freeOnOpenHom_restrict {V W : Opens X} (i : V ⟶ W)
    (M : SheafOfModules.{u} R) (f : freeOnOpen R W ⟶ M) :
    freeOnOpenHom R V M (freeOnOpenMap R i ≫ f) =
      M.val.map i.op (freeOnOpenHom R W M f) := by
  unfold freeOnOpenHom freeOnOpenMap
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left]
  change PresheafOfModules.freeYonedaEquiv
    (((PresheafOfModules.free R.obj).map (yoneda.map i)) ≫ _) = _
  let g := ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ M) f
  change PresheafOfModules.freeYonedaEquiv
    (((PresheafOfModules.free R.obj).map (yoneda.map i)) ≫ g) =
      M.val.map i.op (PresheafOfModules.freeYonedaEquiv g)
  have e : PresheafOfModules.freeHomEquiv
      (((PresheafOfModules.free R.obj).map (yoneda.map i)) ≫ g) =
        yoneda.map i ≫ PresheafOfModules.freeHomEquiv g := by
    ext Z a
    change g.app Z ((ModuleCat.free (R.obj.obj Z)).map
      ((yoneda.map i).app Z) (ModuleCat.freeMk a)) = g.app Z (ModuleCat.freeMk (a ≫ i))
    rw [ModuleCat.free_map_apply]
    rfl
  change yonedaEquiv (PresheafOfModules.freeHomEquiv
      (((PresheafOfModules.free R.obj).map (yoneda.map i)) ≫ g)) = _
  rw [e]
  exact (yonedaEquiv_naturality (PresheafOfModules.freeHomEquiv g) i).symm

lemma freeOnOpenHom_naturality {M N : Modules R} (f : freeOnOpen R U ⟶ M)
    (g : M ⟶ N) :
    freeOnOpenHom R U N (f ≫ g) = g.val.app (op U) (freeOnOpenHom R U M f) := by
  unfold freeOnOpenHom
  simp only [Equiv.trans_apply]
  exact PresheafOfModules.freeYonedaEquiv_comp _ _

/-- The representing open unit agrees with the sheafification of the free
presheaf of modules generated by the represented open. -/
def openUnitFreeIso : openUnit R U ≅ freeOnOpen R U where
  hom := (homOpenUnit R U _).symm (freeOnOpenHom R U _ (𝟙 _))
  inv := (freeOnOpenHom R U _).symm (homOpenUnit R U _ (𝟙 _))
  hom_inv_id := by
    apply (homOpenUnit R U _).injective
    rw [homOpenUnit_naturality, Equiv.apply_symm_apply,
      ← freeOnOpenHom_naturality, Category.id_comp, Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (freeOnOpenHom R U _).injective
    rw [freeOnOpenHom_naturality, Equiv.apply_symm_apply,
      ← homOpenUnit_naturality, Category.id_comp, Equiv.apply_symm_apply]

lemma homOpenUnit_free {M : Modules R} (f : freeOnOpen R U ⟶ M) :
    homOpenUnit R U M ((openUnitFreeIso R U).hom ≫ f) = freeOnOpenHom R U M f := by
  rw [homOpenUnit_naturality]
  change f.val.app (op U)
      (homOpenUnit R U _ ((homOpenUnit R U _).symm (freeOnOpenHom R U _ (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply, ← freeOnOpenHom_naturality, Category.id_comp]

/-- The map of extended open units induced by an inclusion of opens. -/
def openUnitMap {V W : Opens X} (i : V ⟶ W) : openUnit R V ⟶ openUnit R W :=
  (openUnitFreeIso R V).hom ≫ freeOnOpenMap R i ≫ (openUnitFreeIso R W).inv

instance openUnitMap_mono {V W : Opens X} (i : V ⟶ W) : Mono (openUnitMap R i) := by
  have := freeOnOpenMap_mono R i
  unfold openUnitMap
  infer_instance

lemma homOpenUnit_restrict {V W : Opens X} (i : V ⟶ W) (M : Modules R)
    (f : openUnit R W ⟶ M) :
    homOpenUnit R V M (openUnitMap R i ≫ f) = M.val.map i.op (homOpenUnit R W M f) := by
  unfold openUnitMap
  rw [Category.assoc, Category.assoc, homOpenUnit_free, freeOnOpenHom_restrict,
    ← homOpenUnit_free, Iso.hom_inv_id_assoc]

lemma openUnitMap_generator {V W : Opens X} (i : V ⟶ W) :
    (openUnitMap R i).val.app (op V) (openUnitGenerator R V) =
      (openUnit R W).val.map i.op (openUnitGenerator R W) := by
  have h := homOpenUnit_restrict R i (openUnit R W) (𝟙 _)
  rw [Category.comp_id, homOpenUnit_eval, homOpenUnit_eval] at h
  exact h

lemma injective_restrictions_surjective (M : SheafOfModules.{u} R) [Injective M] :
    ∀ (V W : Opens X) (h : V ≤ W), Function.Surjective (M.val.map (homOfLE h).op) := by
  intro V W h s
  obtain ⟨g, hg⟩ := Injective.factors ((homOpenUnit R V M).symm s)
    (openUnitMap R (homOfLE h))
  refine ⟨homOpenUnit R W M g, ?_⟩
  rw [← homOpenUnit_restrict, hg, Equiv.apply_symm_apply]

namespace Expected
open Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction

theorem category_abelian : categoryAbelian.{u} := by
  intro X R
  exact ⟨inferInstance⟩

/-- Exact stalks and their skyscraper right adjoints provide enough injectives. -/
theorem enough_injectives : enoughInjectives.{u} := by
  intro X R
  exact enoughInjectivesByStalks R

theorem injective_embedding : injectiveEmbedding.{u} := by
  intro X R M
  exact ⟨∏ᶜ (injectiveSkyscrapers R M), stalkInjectiveEmbedding R M,
    injectiveSkyscraperProduct R M, inferInstance⟩

theorem products_injective : productsInjective.{u} := by
  intro X R ι I h
  let := h
  infer_instance

theorem sections_left_exact : sectionsLeftExact.{u} := by
  intro X R U
  infer_instance

theorem restrictions_semilinear : restrictionsSemilinear.{u} := by
  intro X R M V W h r s
  exact M.val.map_smul (homOfLE h).op r s

theorem restriction_exact : restrictionExact.{u} := by
  intro X R U
  exact ⟨inferInstance, inferInstance⟩

theorem extension_adjoint : extensionAdjoint.{u} := by
  intro X R U
  exact ⟨extensionAdjunction R U⟩

theorem extension_right_exact : extensionRightExact.{u} := by
  intro X R U
  let := (extensionAdjunction R U).isLeftAdjoint
  infer_instance

theorem open_unit_represents_sections : openUnitRepresentsSections.{u} := by
  intro X R U
  exact ⟨homOpenUnit R U,
    fun M N f g ↦ homOpenUnit_naturality R U f g,
    fun M f g ↦ homOpenUnit_add R U f g,
    homOpenUnit_smul R U, homOpenUnit_eval R U⟩

theorem open_unit_linear_representation : openUnitLinearRepresentation.{u} := by
  intro X R U M
  exact ⟨openUnitHomModule R U M, (fun _ _ ↦ rfl),
    ⟨homOpenUnitLinearEquiv R U M, homOpenUnit_eval R U M⟩⟩

theorem flasque_bridge : flasqueBridge.{u} := by
  intro X R M
  exact flasque_iff R M

/-- The inclusion of extended open units is monic, so injectivity extends
each section across it. -/
theorem injectives_flasque : injectivesFlasque.{u} := by
  intro X R M hM
  let := hM
  exact injective_restrictions_surjective R M

end Expected

end AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction

namespace AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
open AdvancedHomologicalAlgebra.SheafTheory
variable (X : TopCat.{u})
abbrev integerSite := Opens.grothendieckTopology X
abbrev liftedIntegerRing := RingCat.of (ULift.{u} ℤ)
abbrev integerRingPresheaf : (Opens X)ᵒᵖ ⥤ RingCat.{u} := (Functor.const _).obj (liftedIntegerRing : RingCat.{u})
abbrev integerRingSheaf : Sheaf (integerSite X) RingCat.{u} := constantIntegerRingSheaf X
def integerSheafificationMap : integerRingPresheaf X ⟶ (integerRingSheaf X).obj := toSheafify (integerSite X) (integerRingPresheaf X)

instance : Presheaf.IsLocallyInjective (integerSite X) (integerSheafificationMap X) := by dsimp [integerSheafificationMap]; infer_instance
instance : Presheaf.IsLocallySurjective (integerSite X) (integerSheafificationMap X) := by dsimp [integerSheafificationMap]; infer_instance

def integerModulePresheaf (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    PresheafOfModules.{u} (integerRingPresheaf X) := by
  letI (U : (Opens X)ᵒᵖ) : Module ((integerRingPresheaf X).obj U) (P.obj U) := ULift.module
  exact PresheafOfModules.ofPresheaf P (fun {_ _} f r m ↦ by
    change P.map f (r.down • m) = r.down • P.map f m
    exact map_zsmul (P.map f).hom r.down m)

lemma integerModulePresheaf_presheaf (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (integerModulePresheaf X P).presheaf = P := rfl

lemma integerPresheaf_additive_is_linear {M N : PresheafOfModules.{u} (integerRingPresheaf X)}
    (f : M.presheaf ⟶ N.presheaf) (U : (Opens X)ᵒᵖ) (r : (integerRingPresheaf X).obj U)
    (m : M.obj U) : f.app U (r • m) = r • f.app U m := by
  obtain ⟨n⟩ := r
  have h : (ULift.up n : ULift.{u} ℤ) = (n : ULift.{u} ℤ) := rfl
  rw [h]
  change f.app U ((n : (integerRingPresheaf X).obj U) • m) = (n : (integerRingPresheaf X).obj U) • f.app U m
  simp only [Int.cast_smul_eq_zsmul, map_zsmul]

instance : (PresheafOfModules.toPresheaf.{u} (integerRingPresheaf X)).Full where
  map_surjective f := ⟨PresheafOfModules.homMk f (integerPresheaf_additive_is_linear X f), rfl⟩

instance : (SheafOfModules.toSheaf.{u} (integerRingSheaf X)).Full where
  map_surjective {M N} f := by
    let g : (PresheafOfModules.restrictScalars (integerSheafificationMap X)).obj M.val ⟶
        (PresheafOfModules.restrictScalars (integerSheafificationMap X)).obj N.val :=
      (PresheafOfModules.toPresheaf (integerRingPresheaf X)).preimage f.hom
    let h : M.val ⟶ N.val :=
      (PresheafOfModules.restrictHomEquivOfIsLocallySurjective (integerSheafificationMap X) N.isSheaf).symm g
    refine ⟨⟨h⟩, ?_⟩
    ext U m
    have eqg := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (integerSheafificationMap X) N.isSheaf).apply_symm_apply g
    have heq : (PresheafOfModules.toPresheaf (integerRingPresheaf X)).map g = f.hom :=
      Functor.map_preimage _ _
    have hh : h.app U m = g.app U m := congr($(eqg).app U m)
    exact hh.trans congr($(heq).app U m)

instance : (SheafOfModules.toSheaf.{u} (integerRingSheaf X)).EssSurj where
  mem_essImage F := by
    refine ⟨(PresheafOfModules.sheafification (integerSheafificationMap X)).obj (integerModulePresheaf X F.obj), ?_⟩
    exact ⟨asIso ((sheafificationAdjunction (integerSite X) AddCommGrpCat).counit.app F)⟩

instance : (SheafOfModules.toSheaf.{u} (integerRingSheaf X)).IsEquivalence where

def integerModulesEquivalence : SheafOfModules.{u} (integerRingSheaf X) ≌ Sheaf (integerSite X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf.{u} (integerRingSheaf X)).asEquivalence

lemma integerEquivalence_sections (M : SheafOfModules.{u} (integerRingSheaf X)) (U : Opens X) :
    ((integerModulesEquivalence X).functor.obj M).obj.obj (op U) =
      AddCommGrpCat.of (M.val.obj (op U)) := rfl

lemma integerEquivalence_restriction (M : SheafOfModules.{u} (integerRingSheaf X)) {U V : Opens X} (h : U ≤ V)
    (s : M.val.obj (op V)) :
    ((integerModulesEquivalence X).functor.obj M).obj.map (homOfLE h).op s =
      M.val.map (homOfLE h).op s := rfl

def integerUnitIso :
    (integerModulesEquivalence X).functor.obj (SheafOfModules.unit (integerRingSheaf X)) ≅
      (constantSheaf (integerSite X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  letI : (integerSite X).PreservesSheafification (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
    GrothendieckTopology.instPreservesSheafification (integerSite X)
      (forget₂ RingCat.{u} AddCommGrpCat.{u})
  exact (constantCommuteCompose (integerSite X) (forget₂ RingCat.{u} AddCommGrpCat.{u})).app liftedIntegerRing

theorem abelian_injective_flasque
    (F : Sheaf (integerSite X) AddCommGrpCat.{u}) (hF : Injective F) : TopCat.Sheaf.IsFlasque F := by
  let e := integerModulesEquivalence X
  let M := e.inverse.obj F
  have : Injective M := (e.symm.map_injective_iff F).2 hF
  have hM := injective_restrictions_surjective (integerRingSheaf X) M
  let p := (sheafToPresheaf (integerSite X) AddCommGrpCat.{u}).mapIso (e.counitIso.app F)
  constructor
  intro U V i
  have : Epi (((sheafToPresheaf (integerSite X) AddCommGrpCat.{u}).obj
      ((e.inverse ⋙ e.functor).obj F)).map i) := by
    change Epi (M.val.presheaf.map i)
    exact (AddCommGrpCat.epi_iff_surjective _).2 (hM V.unop U.unop (leOfHom i.unop))
  exact epi_of_epi_fac (p.hom.naturality i).symm

namespace Expected
open Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction

theorem abelian_sheaves_as_integer_modules : abelianSheavesAsIntegerModules.{u} := by
  intro X
  exact ⟨integerModulesEquivalence X, rfl, ⟨integerUnitIso X⟩,
    fun M U ↦ rfl, fun M V W h s ↦ rfl⟩

theorem abelian_sheaf_preliminaries : abelianSheafPreliminaries.{u} := by
  intro X
  refine ⟨⟨inferInstance⟩, ?_, abelian_injective_flasque X⟩
  let := enoughInjectivesByStalks (integerRingSheaf X)
  exact EnoughInjectives.of_equivalence (integerModulesEquivalence X).inverse

end Expected
end AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction

/-
Parts of this file (lines 502–518) are adapted from Mathlib.
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean#L79-L96
The composite Hom equivalence and its naturality proof were adapted to extension by zero.
-/
