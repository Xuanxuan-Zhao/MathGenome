import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Topology.Sheaves.Module
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.Grp.Zero

/-!
Interfaces for the preliminaries in advanced-homological-algebra.tex, 3525–3556.
`R` is a sheaf of rings on an arbitrary topological space: no local ring,
separation, compactness, or commutativity hypothesis is imposed. Thus this also
applies to the commutative ringed spaces in `AlgebraicGeometry.RingedSpace`.
All objects are taken in a common arbitrary universe.

The canonical stalks and skyscrapers retain the actual germ maps of scalars.
The independent propositions below express the complete preliminary results,
including the specialization through the constant integer ring sheaf.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits

universe u r

namespace AdvancedHomologicalAlgebra.SheafTheory

abbrev RingSheaf (X : TopCat.{u}) := Sheaf (Opens.grothendieckTopology X) RingCat.{u}

variable {X : TopCat.{u}} (R : RingSheaf X)

/-- Sheaves of modules with their original, varying rings of scalars. -/
abbrev Modules := SheafOfModules.{u} R

/-- The ring of sections, not the ring of global sections of `X`. -/
abbrev sectionRing (R : X.Sheaf RingCat.{r}) (U : Opens X) := R.obj.obj (op U)

/-- Sections remain modules over `R(U)`. -/
abbrev sections (M : Modules R) (U : Opens X) : ModuleCat.{u} (sectionRing R U) :=
  M.val.obj (op U)

/-- Restriction is semilinear with respect to the actual restriction of rings. -/
def restrictionMap (M : Modules R) {V W : Opens X} (h : V ≤ W) :
    sections R M W →ₛₗ[(R.obj.map (homOfLE h).op).hom] sections R M V :=
  M.val.restrictₛₗ (homOfLE h).op

/-- Surjectivity is required between all pairs of comparable opens. -/
def IsFlasque (M : Modules R) : Prop :=
  ∀ (V W : Opens X) (h : V ≤ W), Function.Surjective (M.val.map (homOfLE h).op)

instance overRestrictionIsRightAdjoint (U : Opens X) :
    (SheafOfModules.overFunctor.{u} R U).IsRightAdjoint := by
  unfold SheafOfModules.overFunctor
  infer_instance

instance overRestrictionIsLeftAdjoint (U : Opens X) :
    (SheafOfModules.overFunctor.{u} R U).IsLeftAdjoint := by
  unfold SheafOfModules.overFunctor
  infer_instance

/-- Restriction lands on the actual open subspace with its restricted ring sheaf.
The existing equivalence with the over site is included in the definition. -/
def restriction (U : Opens X) :
    Modules R ⥤ SheafOfModules.{u} (U.sheafRestrict.obj R) :=
  SheafOfModules.overFunctor R U ⋙ (U.sheafOfModulesEquivOver R).functor

instance restrictionIsRightAdjoint (U : Opens X) : (restriction R U).IsRightAdjoint := by
  unfold restriction
  infer_instance

instance restrictionIsLeftAdjoint (U : Opens X) : (restriction R U).IsLeftAdjoint := by
  unfold restriction
  infer_instance

/-- The left adjoint of restriction in the over-site presentation. -/
abbrev extensionFromOver (U : Opens X) : SheafOfModules.{u} (R.over U) ⥤ Modules R :=
  (SheafOfModules.overFunctor R U).leftAdjoint

/-- Extension by zero is specified by its left-adjoint universal property.
The implementation identifies this with sheafified presheaf zero extension. -/
def extensionByZero (U : Opens X) :
    SheafOfModules.{u} (U.sheafRestrict.obj R) ⥤ Modules R :=
  (U.sheafOfModulesEquivOver R).inverse ⋙ extensionFromOver R U

abbrev openUnit (U : Opens X) : Modules R :=
  (extensionByZero R U).obj (SheafOfModules.unit (U.sheafRestrict.obj R))

variable (U : Opens X)

noncomputable def sectionsAtInitial {C : Type u} [SmallCategory C]
    {S : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} S)
    (i : Cᵒᵖ) (hi : IsInitial i) : M.sections ≃ M.obj i where
  toFun s := s.val i
  invFun x := M.sectionsMk (fun j ↦ M.map (hi.to j) x) (by
    intro j k f
    rw [← M.map_comp_apply, hi.hom_ext (hi.to j ≫ f) (hi.to k)])
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro j
    exact s.property (hi.to j)
  right_inv x := by
    have h : hi.to i = 𝟙 i := hi.hom_ext _ _
    change M.presheaf.map (hi.to i) x = x
    rw [h, M.presheaf.map_id]
    rfl
noncomputable def overSections (M : SheafOfModules.{u} R) :
    (M.over U).sections ≃ M.val.obj (op U) :=
  sectionsAtInitial (M.over U).val (op (Over.mk (𝟙 U)))
    ((Over.mkIdTerminal (X := U)).op _)
noncomputable def openUnitIso :
    (extensionByZero R U).obj (SheafOfModules.unit _) ≅
      (extensionFromOver R U).obj (SheafOfModules.unit (R.over U)) :=
  (extensionFromOver R U).mapIso (U.sheafOfModulesEquivOverInverseUnit R)

/-- The distinguished section of the extended open unit is the adjunction
unit applied to `1` on the open, transported from the over site. -/
def openUnitGenerator : (openUnit R U).val.obj (op U) :=
  let A := Adjunction.ofIsRightAdjoint (SheafOfModules.overFunctor.{u} R U)
  let W := op (Over.mk (𝟙 U))
  (openUnitIso R U).inv.val.app (op U)
    ((A.unit.app (SheafOfModules.unit (R.over U))).val.app W
      (1 : (R.over U).obj.obj W))

def overUnitRightMul (r : sectionRing R U) :
    SheafOfModules.unit (R.over U) ⟶ SheafOfModules.unit (R.over U) :=
  (SheafOfModules.unit (R.over U)).unitHomEquiv.symm
    ((sectionsAtInitial _ (op (Over.mk (𝟙 U)))
      ((Over.mkIdTerminal (X := U)).op _)).symm r)

def openRightMul (r : sectionRing R U) : openUnit R U ⟶ openUnit R U :=
  (openUnitIso R U).hom ≫ (extensionFromOver R U).map (overUnitRightMul R U r) ≫
    (openUnitIso R U).inv

variable (x : X)

abbrev stalkRing := TopCat.Presheaf.stalk R.obj x
abbrev stalkModule (M : Modules R) : ModuleCat.{u} (stalkRing R x) :=
  ModuleCat.of _ ↑(TopCat.Presheaf.stalk M.val.presheaf x)

lemma stalkGermsJoint (M : Modules R) (r : stalkRing R x) (m : stalkModule R x M) :
    ∃ (U : Opens X) (hx : x ∈ U) (a : R.obj.obj (op U)) (s : M.val.obj (op U)),
      TopCat.Presheaf.germ R.obj U x hx a = r ∧ TopCat.Presheaf.germ M.val.presheaf U x hx s = m := by
  obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq R.obj r
  obtain ⟨V, hVU, hV, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hU
  exact ⟨V, hV, R.obj.map (homOfLE hVU).op a, s,
    TopCat.Presheaf.germ_res_apply R.obj (homOfLE hVU) x hV a, rfl⟩

def stalkFunctor : Modules R ⥤ ModuleCat.{u} (stalkRing R x) where
  obj := stalkModule R x
  map {M N} f := ModuleCat.ofHom
    { toFun := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map f.val))
      map_add' := map_add _
      map_smul' r m := by
        obtain ⟨U, hx, a, s, rfl, rfl⟩ := stalkGermsJoint R x M r m
        rw [← M.val.germ_ringCat_smul]
        erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
        change TopCat.Presheaf.germ N.val.presheaf U x hx (f.val.app (op U) (a • s)) = _
        rw [(f.val.app (op U)).hom.map_smul, N.val.germ_ringCat_smul]
        erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
        rfl }
  map_id M := by
    ext m
    exact congr($( (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_id M.val.presheaf) m)
  map_comp f g := by
    ext m
    exact congr($( (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp
      ((PresheafOfModules.toPresheaf R.obj).map f.val)
      ((PresheafOfModules.toPresheaf R.obj).map g.val)) m)

def stalkForgetIso :
    stalkFunctor R x ⋙ forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf R ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

local instance (U : Opens X) : Decidable (x ∈ U) := Classical.propDecidable _

def skyscraperUnderlyingPresheaf (N : AddCommGrpCat.{u}) : X.Presheaf AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (PLift (x ∈ U.unop) → N)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun s hx ↦ s ⟨i.unop.le hx.down⟩
      map_zero' := rfl
      map_add' := by intros; rfl }
  map_id U := by ext s hx; rfl
  map_comp i j := by ext s hx; rfl

@[reducible] def skyscraperSectionModule (N : ModuleCat.{u} (stalkRing R x)) (U : (Opens X)ᵒᵖ)
    (hx : x ∈ U.unop) : Module (R.obj.obj U) N :=
  Module.compHom N (show R.obj.obj U ⟶ stalkRing R x from TopCat.Presheaf.germ R.obj U.unop x hx).hom

instance skyscraperSectionsModule (N : ModuleCat.{u} (stalkRing R x)) (U : (Opens X)ᵒᵖ) :
    Module (R.obj.obj U) ((skyscraperUnderlyingPresheaf x ((forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u}).obj N)).obj U) :=
  letI (hx : PLift (x ∈ U.unop)) : Module (R.obj.obj U) N := skyscraperSectionModule R x N U hx.down
  inferInstanceAs (Module (R.obj.obj U) (PLift (x ∈ U.unop) → N))

def skyscraperModulePresheaf (N : ModuleCat.{u} (stalkRing R x)) : PresheafOfModules.{u} R.obj :=
  PresheafOfModules.ofPresheaf (skyscraperUnderlyingPresheaf x ((forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u}).obj N)) (by
    intro U V i r m
    funext hx
    change (TopCat.Presheaf.germ R.obj U.unop x (i.unop.le hx.down)) r • (show N from m ⟨i.unop.le hx.down⟩) =
      (TopCat.Presheaf.germ R.obj V.unop x hx.down) (R.obj.map i r) • (show N from m ⟨i.unop.le hx.down⟩)
    rw [← TopCat.Presheaf.germ_res_apply R.obj i.unop x hx.down r]
    congr 2)

def skyscraperEvaluationIso (N : AddCommGrpCat.{u}) (U : (Opens X)ᵒᵖ) (hx : x ∈ U.unop) :
    (skyscraperUnderlyingPresheaf x N).obj U ≅ N :=
  (show (PLift (x ∈ U.unop) → N) ≃+ N from
    { toFun := fun s ↦ s ⟨hx⟩
      invFun := fun n _ ↦ n
      left_inv := by intro s; rfl
      right_inv := by intro n; rfl
      map_add' := by intros; rfl }).toAddCommGrpIso

def skyscraperEmptyIso (N : AddCommGrpCat.{u}) (U : (Opens X)ᵒᵖ) (hx : x ∉ U.unop) :
    (skyscraperUnderlyingPresheaf x N).obj U ≅ terminal AddCommGrpCat.{u} := by
  haveI : IsEmpty (PLift (x ∈ U.unop)) := ⟨fun h ↦ hx h.down⟩
  haveI : Subsingleton ((skyscraperUnderlyingPresheaf x N).obj U) :=
    inferInstanceAs (Subsingleton (PLift (x ∈ U.unop) → N))
  exact (AddCommGrpCat.isZero_of_subsingleton _).isTerminal.uniqueUpToIso terminalIsTerminal

def skyscraperUnderlyingIso (N : AddCommGrpCat.{u}) :
    skyscraperUnderlyingPresheaf x N ≅ skyscraperPresheaf x N := by
  classical
  refine NatIso.ofComponents (fun U ↦ ?_) ?_
  · by_cases hx : x ∈ U.unop
    · exact skyscraperEvaluationIso x N U hx ≪≫ (eqToIso (ite_eq_left hx)).symm
    · exact skyscraperEmptyIso x N U hx ≪≫ (eqToIso (ite_eq_right hx)).symm
  · intro U V i
    by_cases hxV : x ∈ V.unop
    · have hxU := i.unop.le hxV
      simp only [hxU, hxV, ↓reduceDIte, Iso.trans_hom, Iso.symm_hom, eqToIso.inv]
      simp only [skyscraperPresheaf_map, dite_eq_left hxV, Category.assoc,
        eqToHom_trans]
      rw [← Category.assoc]
      apply (cancel_mono (eqToHom (ite_eq_left hxV).symm)).mpr
      ext s
      rfl
    · exact ((ite_eq_right hxV).symm.ndrec terminalIsTerminal).hom_ext _ _

lemma skyscraperUnderlyingIsSheaf (N : AddCommGrpCat.{u}) : (skyscraperUnderlyingPresheaf x N).IsSheaf := by
  classical
  exact (TopCat.Presheaf.isSheaf_iso_iff (skyscraperUnderlyingIso x N)).mpr
    (skyscraperPresheaf_isSheaf x N)

def skyscraper (N : ModuleCat.{u} (stalkRing R x)) : Modules R :=
  ⟨skyscraperModulePresheaf R x N, skyscraperUnderlyingIsSheaf x ((forget₂ (ModuleCat.{u} (stalkRing R x)) AddCommGrpCat.{u}).obj N)⟩

def skyscraperMap {N P : ModuleCat.{u} (stalkRing R x)} (f : N ⟶ P) :
    skyscraper R x N ⟶ skyscraper R x P :=
  ⟨{
    app U := ModuleCat.ofHom
      { toFun := fun s hx ↦ f (s hx)
        map_add' := by intro s t; funext hx; exact f.hom.map_add _ _
        map_smul' := by
          intro r s
          funext hx
          exact f.hom.map_smul ((TopCat.Presheaf.germ R.obj U.unop x hx.down) r) (s hx) }
    naturality := by intros U V i; ext s; funext hx; rfl }⟩

def skyscraperFunctor : ModuleCat.{u} (stalkRing R x) ⥤ Modules R where
  obj := skyscraper R x
  map := skyscraperMap R x
  map_id N := by ext U s; rfl
  map_comp f g := by ext U s; rfl

end AdvancedHomologicalAlgebra.SheafTheory

namespace Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction

open AdvancedHomologicalAlgebra.SheafTheory

/-- The module category is abelian, over every ringed space. -/
def categoryAbelian : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X), Nonempty (Abelian (Modules R))

def enoughInjectives : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X), EnoughInjectives (Modules R)

def injectiveEmbedding : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (M : Modules R),
    ∃ (I : Modules R) (f : M ⟶ I), Injective I ∧ Mono f

def productsInjective : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (ι : Type u) (I : ι → Modules R),
    (∀ i, Injective (I i)) → Injective (∏ᶜ I)

def sectionsLeftExact : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
    PreservesFiniteLimits (SheafOfModules.evaluation.{u} R (op U))

def restrictionsSemilinear : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (M : Modules R) (V W : Opens X) (h : V ≤ W)
    (r : sectionRing R W) (s : sections R M W),
      restrictionMap R M h (r • s) = R.obj.map (homOfLE h).op r • restrictionMap R M h s

def restrictionExact : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
    PreservesFiniteLimits (restriction R U) ∧ PreservesFiniteColimits (restriction R U)

def extensionAdjoint : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
    Nonempty (extensionByZero R U ⊣ restriction R U)

def extensionRightExact : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
    PreservesFiniteColimits (extensionByZero R U)

/-- Natural additive bijections compatible with the section-ring action.
The action on Hom is precomposition with right multiplication on the open unit. -/
def openUnitRepresentsSections : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
    ∃ e : ∀ M : Modules R, (openUnit R U ⟶ M) ≃ sections R M U,
      (∀ (M N : Modules R) (f : openUnit R U ⟶ M) (g : M ⟶ N),
        e N (f ≫ g) = g.val.app (op U) (e M f)) ∧
      (∀ (M : Modules R) (f g : openUnit R U ⟶ M), e M (f + g) = e M f + e M g) ∧
      (∀ (M : Modules R) (r : sectionRing R U) (f : openUnit R U ⟶ M),
        e M (openRightMul R U r ≫ f) = r • e M f) ∧
      (∀ (M : Modules R) (f : openUnit R U ⟶ M),
        e M f = f.val.app (op U) (openUnitGenerator R U))

/-- The Hom identification is an isomorphism over the full section ring.
Its scalar multiplication is canonically induced by right multiplication on the unit. -/
def openUnitLinearRepresentation : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) (M : Modules R),
    ∃ h : Module (sectionRing R U) (openUnit R U ⟶ M),
      letI := h
      (∀ (r : sectionRing R U) (f : openUnit R U ⟶ M),
        r • f = openRightMul R U r ≫ f) ∧
      ∃ e : (openUnit R U ⟶ M) ≃ₗ[sectionRing R U] sections R M U,
        ∀ f, e f = f.val.app (op U) (openUnitGenerator R U)

def flasqueBridge : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (M : Modules R),
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M) ↔ IsFlasque R M

def injectivesFlasque : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (M : Modules R), Injective M → IsFlasque R M

/-- Exact extension by zero on an arbitrary open subspace. -/
def extensionExact : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X),
    PreservesFiniteLimits (extensionByZero R U) ∧ PreservesFiniteColimits (extensionByZero R U)

/-- Restricting an injective to an arbitrary open preserves injectivity. -/
def restrictionPreservesInjectives : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) (I : Modules R),
    Injective I → Injective ((restriction R U).obj I)

/-- Stalks are taken over the actual stalk ring and are exact. -/
def stalkExact : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (x : X),
    PreservesFiniteLimits (stalkFunctor R x) ∧
      PreservesFiniteColimits (stalkFunctor R x)

/-- The right adjoint uses the actual stalk ring. -/
def skyscraperAdjoint : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (x : X),
    Nonempty (stalkFunctor R x ⊣ skyscraperFunctor R x)

/-- Sections of the skyscraper are the given module, with scalars restricted
along the germ map, on opens containing the point; otherwise they are zero. -/
def skyscraperSections : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (x : X)
      (N : ModuleCat.{u} (stalkRing R x)) (U : Opens X),
    (∀ hx : x ∈ U,
      ∃ e : sections R (skyscraper R x N) U ≃+ N,
        ∀ (r : sectionRing R U) (s : sections R (skyscraper R x N) U),
          e (r • s) = TopCat.Presheaf.germ R.obj U x hx r • e s) ∧
    (x ∉ U → Subsingleton (sections R (skyscraper R x N) U))

def skyscraperInjective : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (x : X)
      (N : ModuleCat.{u} (stalkRing R x)),
    Injective N → Injective (skyscraper R x N)

end Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction

namespace AdvancedHomologicalAlgebra.SheafTheory

/-- The constant sheaf of integer rings is the sheafification of the constant
presheaf; the lift places its integer ring in the universe of the space. -/
def constantIntegerRingSheaf (X : TopCat.{u}) : RingSheaf X :=
  (constantSheaf (Opens.grothendieckTopology X) RingCat.{u}).obj
    (RingCat.of (ULift.{u} ℤ))

end AdvancedHomologicalAlgebra.SheafTheory

namespace Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
open AdvancedHomologicalAlgebra.SheafTheory

/-- Forgetting the module structure over the actual constant integer ring sheaf
is an equivalence. Since this is the canonical forgetful functor, it preserves
all section groups and their restriction homomorphisms. -/
def abelianSheavesAsIntegerModules : Prop :=
  ∀ (X : TopCat.{u}),
    ∃ e : Modules (constantIntegerRingSheaf X) ≌
        Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      e.functor = SheafOfModules.toSheaf (constantIntegerRingSheaf X) ∧
      Nonempty ((SheafOfModules.toSheaf (constantIntegerRingSheaf X)).obj
        (SheafOfModules.unit (constantIntegerRingSheaf X)) ≅
          (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} ℤ))) ∧
      (∀ (M : Modules (constantIntegerRingSheaf X)) (U : Opens X),
        ((SheafOfModules.toSheaf (constantIntegerRingSheaf X)).obj M).obj.obj (op U) =
          AddCommGrpCat.of (sections (constantIntegerRingSheaf X) M U)) ∧
      (∀ (M : Modules (constantIntegerRingSheaf X)) (V W : Opens X) (h : V ≤ W)
          (s : sections (constantIntegerRingSheaf X) M W),
        ((SheafOfModules.toSheaf (constantIntegerRingSheaf X)).obj M).obj.map
          (homOfLE h).op s = M.val.map (homOfLE h).op s)

/-- The usual category of abelian sheaves enjoys the same preliminary results. -/
def abelianSheafPreliminaries : Prop :=
  ∀ (X : TopCat.{u}),
    Nonempty (Abelian (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) ∧
    EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ∧
    ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      Injective F → TopCat.Sheaf.IsFlasque F

end Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
