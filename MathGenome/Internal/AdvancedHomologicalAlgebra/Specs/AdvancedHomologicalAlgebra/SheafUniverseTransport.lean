import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
import Mathlib.Topology.Category.TopCat.ULift
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.RingTheory.FreeRing
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-! Universe transport for the sheaf preliminaries in the source, §7.1. -/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe a u r m v

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The underlying space in the larger universe. -/
abbrev liftedSpace (X : TopCat.{u}) := TopCat.uliftFunctor.{a}.obj X

/-- The homeomorphism identifies an open of the lifted space with its original open. -/
def opensEquiv (X : TopCat.{u}) : Opens (liftedSpace.{a} X) ≃o Opens X :=
  (X.uliftFunctorObjHomeo.{a}).symm.opensCongr

@[simp] theorem mem_opensEquiv (X : TopCat.{u}) (U : Opens (liftedSpace.{a} X)) (x : X) :
    x ∈ opensEquiv X U ↔ ULift.up x ∈ U := Iff.rfl

/-- The scalar lift takes each original ring map to the same map on the lifted carriers. -/
abbrev ringLift : RingCat.{r} ⥤ RingCat.{max a r} where
  obj A := RingCat.of (ULift.{a} A)
  map {A B} f := RingCat.ofHom (R := ULift.{a} A) (S := ULift.{a} B)
    ((ULift.ringEquiv (R := B)).symm.toRingHom.comp
      (f.hom.comp (ULift.ringEquiv (R := A)).toRingHom))
  map_id A := by ext x; rfl
  map_comp f g := by ext x; rfl

section Scalars

variable {C : Type u} [Category C]
variable {R : Cᵒᵖ ⥤ RingCat.{r}}

/-- Change the scalar carrier of a presheaf of modules, retaining its section carriers. -/
def liftScalars : PresheafOfModules.{m} R ⥤
    PresheafOfModules.{m} (R ⋙ ringLift.{a}) where
  obj M :=
    letI (U : Cᵒᵖ) : Module ((R ⋙ ringLift.{a}).obj U) (M.presheaf.obj U) :=
      inferInstanceAs (Module (ULift.{a} (R.obj U)) (M.obj U))
    PresheafOfModules.ofPresheaf M.presheaf
      (fun {_ _} f s t ↦ M.map_smul f (ULift.down s) t)
  map f := PresheafOfModules.homMk ((PresheafOfModules.toPresheaf R).map f)
    (fun U r s ↦ (f.app U).hom.map_smul (ULift.down r) s)

/-- Recover the original scalar structure by restriction along ULift.up. -/
def lowerScalars : PresheafOfModules.{m} (R ⋙ ringLift.{a}) ⥤
    PresheafOfModules.{m} R where
  obj M :=
    letI (U : Cᵒᵖ) : Module (R.obj U) (M.presheaf.obj U) :=
      letI : Module (ULift.{a} (R.obj U)) (M.obj U) := (M.obj U).isModule
      Module.compHom (M.obj U) ((ULift.ringEquiv.{r,a} (R := R.obj U)).symm.toRingHom)
    PresheafOfModules.ofPresheaf M.presheaf (fun {_ _} f s t ↦ M.map_smul f (ULift.up.{a,r} s) t)
  map {M N} f := PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf (R ⋙ ringLift.{a})).map f)
    (fun U r s ↦ (f.app U).hom.map_smul (ULift.up.{a,r} r) s)

variable (R) in
/-- Raise section carriers over the original site and original rings. -/
def liftCoefficients : PresheafOfModules.{m} R ⥤ PresheafOfModules.{max a m} R where
  obj M :=
    letI (U : Cᵒᵖ) : Module (R.obj U) ((M.presheaf ⋙ AddCommGrpCat.uliftFunctor.{a}).obj U) :=
      inferInstanceAs (Module (R.obj U) (ULift.{a} (M.obj U)))
    PresheafOfModules.ofPresheaf (M.presheaf ⋙ AddCommGrpCat.uliftFunctor.{a})
      (fun {_ _} f s t ↦ congrArg ULift.up (M.map_smul f s (ULift.down t)))
  map f := PresheafOfModules.homMk
    (Functor.whiskerRight ((PresheafOfModules.toPresheaf R).map f)
      AddCommGrpCat.uliftFunctor.{a})
    (fun U r s ↦ congrArg ULift.up ((f.app U).hom.map_smul r s.down))

end Scalars

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

private def freeRingFunctor : Type r ⥤ RingCat.{r} where
  obj A := RingCat.of (FreeRing A)
  map f := RingCat.ofHom (FreeRing.map f)
  map_id A := by
    apply RingCat.hom_ext
    apply FreeRing.hom_ext
    simp
  map_comp f g := by
    apply RingCat.hom_ext
    apply FreeRing.hom_ext
    simp

private def freeRingAdjunction : freeRingFunctor.{r} ⊣ CategoryTheory.forget RingCat.{r} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A B ↦
        { toFun := fun f ↦ ↾(FreeRing.lift.symm f.hom)
          invFun := fun f ↦ RingCat.ofHom (FreeRing.lift f)
          left_inv := fun f ↦ RingCat.hom_ext (FreeRing.lift.apply_symm_apply f.hom)
          right_inv := fun f ↦ ConcreteCategory.hom_ext _ _
            (fun x ↦ congrFun (FreeRing.lift.symm_apply_apply f) x) }
      homEquiv_naturality_left_symm := fun f g ↦ by
        apply RingCat.hom_ext
        apply FreeRing.hom_ext
        intro x
        change FreeRing.lift (fun x ↦ g (f x)) (FreeRing.of x) =
          (FreeRing.lift (fun x ↦ g x)).comp (FreeRing.map (fun x ↦ f x)) (FreeRing.of x)
        simp
      homEquiv_naturality_right := fun f g ↦ rfl }

instance : (CategoryTheory.forget RingCat.{r}).IsRightAdjoint :=
  freeRingAdjunction.isRightAdjoint

instance [UnivLE.{u, max a r}] : PreservesLimitsOfSize.{u, u} ringLift.{a, r} where
  preservesLimitsOfShape {J} :=
    { preservesLimit := fun {K} ↦
      { preserves := fun h ↦ by
          let : ReflectsLimitsOfShape J (CategoryTheory.forget RingCat.{max a r}) :=
            reflectsLimitsOfShape_of_reflectsIsomorphisms
          exact ⟨isLimitOfReflects (CategoryTheory.forget RingCat)
            (isLimitOfPreserves
              (CategoryTheory.forget RingCat.{r} ⋙ CategoryTheory.uliftFunctor.{a}) h)⟩ } }

section Site

variable {X : TopCat.{u}} {Y : TopCat.{r}}

/-- The homeomorphism sends every covering sieve to a covering sieve. -/
theorem opensCongrCoverPreserving (e : X ≃ₜ Y) :
    CoverPreserving (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
      e.opensCongr.equivalence.functor := by
  let F := e.opensCongr.equivalence.functor
  constructor
  intro U S hS y hy
  have hx : e.symm y ∈ U := hy
  obtain ⟨V, f, hf, hV⟩ := hS (e.symm y) hx
  exact ⟨F.obj V, F.map f, ⟨_, _, 𝟙 _, hf, Subsingleton.elim _ _⟩, hV⟩

/-- Reindexing opens along a homeomorphism is continuous across universes. -/
instance opensCongrContinuous (e : X ≃ₜ Y) :
    Functor.IsContinuous e.opensCongr.equivalence.functor
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (opensCongrCoverPreserving e)

end Site

universe w

variable {X : TopCat.{u}}
variable (R : X.Sheaf RingCat.{r})

/-- The same ring sheaf with its ring carriers raised on the original site. -/
def liftRingOnSite {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (S : Sheaf J RingCat.{r}) : Sheaf J RingCat.{max a u r} :=
  ⟨S.obj ⋙ ringLift.{max a u}, Presheaf.isSheaf_comp_of_isSheaf J S.obj ringLift S.property⟩

abbrev liftRingSheaf := liftRingOnSite.{a} R

instance (X : TopCat.{u}) :
    (opensEquiv.{a} X).equivalence.functor.IsContinuous
      (Opens.grothendieckTopology (liftedSpace.{a} X)) (Opens.grothendieckTopology X) :=
  opensCongrContinuous _

instance (X : TopCat.{u}) :
    (opensEquiv.{a} X).equivalence.inverse.IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (liftedSpace.{a} X)) :=
  opensCongrContinuous (X.uliftFunctorObjHomeo.{a})

/-- The ring sheaf on the raised space, evaluated on the corresponding original open. -/
def liftedRing : SheafTheory.RingSheaf (liftedSpace.{max a r u} X) :=
  ((opensEquiv.{max a r u} X).equivalence.functor.sheafPushforwardContinuous
    _ _ _).obj (liftRingSheaf.{a} R)

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe w

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- Sheaf-level change of scalar carriers over a fixed site. -/
def liftScalarsOnSite {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (S : Sheaf J RingCat.{r}) :
    SheafOfModules.{m} S ⥤ SheafOfModules.{m} (liftRingOnSite.{a} S) where
  obj M := ⟨liftScalars.{max a u}.obj M.val, M.isSheaf⟩
  map f := ⟨liftScalars.{max a u}.map f.val⟩

/-- Restriction of scalar carriers along the pointwise inverse ring transport. -/
def lowerScalarsOnSite {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (S : Sheaf J RingCat.{r}) :
    SheafOfModules.{m} (liftRingOnSite.{a} S) ⥤ SheafOfModules.{m} S where
  obj M := ⟨lowerScalars.{max a u}.obj M.val, M.isSheaf⟩
  map f := ⟨lowerScalars.{max a u}.map f.val⟩

abbrev liftSheafScalars := liftScalarsOnSite.{a} R
abbrev lowerSheafScalars := lowerScalarsOnSite.{a} R

/-- The actual objectwise coefficient carrier embedding on sheaves. -/
def liftSheafCoefficients : SheafOfModules.{m} R ⥤ SheafOfModules.{max a m} R where
  obj M := ⟨(liftCoefficients.{a} R.obj).obj M.val, Presheaf.isSheaf_comp_of_isSheaf
    (Opens.grothendieckTopology X) _ AddCommGrpCat.uliftFunctor.{a} M.isSheaf⟩
  map f := ⟨(liftCoefficients.{a} R.obj).map f.val⟩

/-- Presheaves over an original site and ring, with carriers in the adequate universe. -/
abbrev AmbientPresheaves := PresheafOfModules.{max a u r} R.obj

/-- Sheaves over an original site and ring, with carriers in the adequate universe. -/
abbrev AmbientSheaves := SheafOfModules.{max a u r} R

/-- Reindex an ambient presheaf, changing its scalar carriers in the same step. -/
def transportPresheaf : AmbientPresheaves.{a} R ⥤
    PresheafOfModules.{max a u r} (liftedRing.{a} R).obj :=
  liftScalars.{max a u} ⋙ PresheafOfModules.pushforward₀
    (opensEquiv.{max a r u} X).equivalence.functor (liftRingSheaf.{a} R).obj

/-- Reindex an ambient sheaf, changing its scalar carriers in the same step. -/
def transport : AmbientSheaves.{a} R ⥤ SheafTheory.Modules (liftedRing.{a} R) :=
  liftSheafScalars.{a} R ⋙ SheafOfModules.pushforward
    (F := (opensEquiv.{max a r u} X).equivalence.functor)
    (𝟙 (liftedRing.{a} R))

/-- Pointwise scalar map in ambient coordinates. -/
def sectionRingEquiv (U : Opens (liftedSpace.{max a r u} X)) :
    R.obj.obj (op (opensEquiv X U)) ≃+* (liftedRing.{a} R).obj.obj (op U) :=
  (ULift.ringEquiv.{r,max a u} (R := R.obj.obj (op (opensEquiv X U)))).symm

/-- The section comparison retains the ambient coefficient carrier. -/
def sectionEquiv (M : AmbientSheaves.{a} R) (U : Opens (liftedSpace.{max a r u} X)) :
    M.val.obj (op (opensEquiv X U)) ≃+ ((transport.{a} R).obj M).val.obj (op U) :=
  AddEquiv.refl _

/-- Surjectivity between every pair of comparable original opens. -/
def IsFlasque (M : SheafOfModules.{m} R) : Prop :=
  ∀ (U V : Opens X) (i : U ⟶ V), Function.Surjective (M.val.map i.op)

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

def ambientEquivalence : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}), (transport.{a} R).IsEquivalence

def ambientExact : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}),
    PreservesFiniteLimits (transport.{a} R) ∧ PreservesFiniteColimits (transport.{a} R)

def ambientMonoInjective : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r})
    (M N : AmbientSheaves.{a} R) (f : M ⟶ N),
    (Mono ((transport.{a} R).map f) ↔ Mono f) ∧
      (Injective ((transport.{a} R).obj M) ↔ Injective M)

def ambientFlasque : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (M : AmbientSheaves.{a} R),
    _root_.AdvancedHomologicalAlgebra.SheafTheory.IsFlasque (liftedRing.{a} R) ((transport.{a} R).obj M) ↔ IsFlasque R M

def ambientEnoughInjectives : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}), EnoughInjectives (AmbientSheaves.{a} R)

def ambientSections : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (M N : AmbientSheaves.{a} R)
    (f : M ⟶ N) (U V : Opens (liftedSpace.{max a r u} X)) (i : U ⟶ V)
    (s : M.val.obj (op (opensEquiv X V))) (c : R.obj.obj (op (opensEquiv X V))),
    let e := (opensEquiv.{max a r u} X).equivalence.functor
    sectionRingEquiv.{a} R U (R.obj.map (e.map i).op c) =
      (liftedRing.{a} R).obj.map i.op (sectionRingEquiv.{a} R V c) ∧
    sectionEquiv.{a} R M V (c • s) = sectionRingEquiv.{a} R V c • sectionEquiv.{a} R M V s ∧
    sectionEquiv.{a} R M U (M.val.map (e.map i).op s) =
      ((transport.{a} R).obj M).val.map i.op (sectionEquiv.{a} R M V s) ∧
    sectionEquiv.{a} R N V (f.val.app (op (opensEquiv X V)) s) =
      ((transport.{a} R).map f).val.app (op V) (sectionEquiv.{a} R M V s)

def coefficientLiftFlasque : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (M : SheafOfModules.{m} R),
    IsFlasque R ((liftSheafCoefficients.{a} R).obj M) ↔ IsFlasque R M

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- The neighborhood equivalence for the same point of the original space. -/
def neighborhoodsEquiv (x : X) :
    OpenNhds (X.uliftFunctorObjHomeo.{a} x) ≃o OpenNhds x where
  toFun U := ⟨opensEquiv X U.1, U.2⟩
  invFun U := ⟨(opensEquiv X).symm U.1, U.2⟩
  left_inv U := Subtype.ext ((opensEquiv X).symm_apply_apply U.1)
  right_inv U := Subtype.ext ((opensEquiv X).apply_symm_apply U.1)
  map_rel_iff' := (opensEquiv X).le_iff_le

/-- Diagram of germs on the original site with the original scalar restrictions.
Its rings are placed in a universe in which this colimit exists. -/
abbrev ringNeighborhoods (x : X) :=
  (OpenNhds.inclusion x).op ⋙ (liftRingSheaf.{a} R).obj

/-- Diagram of sections on the original neighborhoods of the point. -/
abbrev moduleNeighborhoods (x : X) (M : AmbientPresheaves.{a} R) :=
  (OpenNhds.inclusion x).op ⋙ M.presheaf

instance (x : X) : HasColimit (ringNeighborhoods.{a} R x) :=
  HasColimit.mk ⟨_, RingCat.FilteredColimits.colimitCoconeIsColimit.{u, max a r} _⟩

abbrev originalStalkRing (x : X) :=
  colimit (ringNeighborhoods.{a} R x)

abbrev originalStalkGroup (x : X) (M : AmbientPresheaves.{a} R) :=
  colimit (moduleNeighborhoods.{a} R x M)

/-- Original scalar germs are induced by the actual restriction diagram. -/
def originalRingGerm (x : X) (U : Opens X) (hx : x ∈ U) :
    R.obj.obj (op U) →+* originalStalkRing.{a} R x :=
  (colimit.ι (ringNeighborhoods.{a} R x) (op ⟨U, hx⟩)).hom.comp
    (ULift.ringEquiv.{r,max a u} (R := R.obj.obj (op U))).symm.toRingHom

def originalModuleGerm (x : X) (M : AmbientPresheaves.{a} R) (U : Opens X) (hx : x ∈ U) :
    M.obj (op U) →+ originalStalkGroup.{a} R x M :=
  (colimit.ι (moduleNeighborhoods.{a} R x M) (op ⟨U, hx⟩)).hom

/-- The action on the original module stalk is induced by simultaneous germs. -/
noncomputable instance originalStalkModule (x : X) (M : AmbientPresheaves.{a} R) :
    Module (originalStalkRing.{a} R x) (originalStalkGroup.{a} R x M) :=
  letI (i : (OpenNhds x)ᵒᵖ) : Module ((ringNeighborhoods.{a} R x).obj i)
      ((moduleNeighborhoods.{a} R x M).obj i) :=
    inferInstanceAs (Module (ULift.{max a u} (R.obj.obj (op i.unop.1))) (M.obj (op i.unop.1)))
  IsColimit.module (ringNeighborhoods.{a} R x) (moduleNeighborhoods.{a} R x M)
    (fun f c s ↦ M.map_smul ((OpenNhds.inclusion x).op.map f) (ULift.down c) s)
    (colimit.isColimit _) (colimit.isColimit _)

theorem original_germ_smul (x : X) (M : AmbientPresheaves.{a} R) (U : Opens X) (hx : x ∈ U)
    (c : R.obj.obj (op U)) (s : M.obj (op U)) :
    originalModuleGerm.{a} R x M U hx (c • s) =
      originalRingGerm.{a} R x U hx c • originalModuleGerm.{a} R x M U hx s :=
  letI (i : (OpenNhds x)ᵒᵖ) : Module ((ringNeighborhoods.{a} R x).obj i)
      ((moduleNeighborhoods.{a} R x M).obj i) :=
    inferInstanceAs (Module (ULift.{max a u} (R.obj.obj (op i.unop.1))) (M.obj (op i.unop.1)))
  IsColimit.ι_smul (ringNeighborhoods.{a} R x) (moduleNeighborhoods.{a} R x M)
    (fun f c s ↦ M.map_smul ((OpenNhds.inclusion x).op.map f) (ULift.down c) s)
    (colimit.isColimit _) (colimit.isColimit _) (op ⟨U, hx⟩) (ULift.up c) s

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- The actual original map on additive stalks is induced on the neighborhood diagrams. -/
def originalModuleStalkMap (x : X) {M N : AmbientPresheaves.{a} R} (f : M ⟶ N) :
    originalStalkGroup.{a} R x M ⟶ originalStalkGroup.{a} R x N :=
  colimMap (Functor.whiskerLeft (OpenNhds.inclusion x).op
    ((PresheafOfModules.toPresheaf R.obj).map f))

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Both neighborhood colimits and their comparison are required on the actual
scalar and coefficient germs. -/
def stalkComparison : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (x : X),
    let y := X.uliftFunctorObjHomeo.{max a r u} x
    let F := transportPresheaf.{a} R
    ∃ eR : (TopCat.Presheaf.stalk (C := RingCat.{max a r u}) (X := liftedSpace.{max a r u} X) (liftedRing.{a} R).obj y) ≃+*
        originalStalkRing.{a} R x,
      ∃ eM : ∀ M : AmbientPresheaves.{a} R,
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{max a r u}) (X := liftedSpace.{max a r u} X) (F.obj M).presheaf y) ≃+ originalStalkGroup.{a} R x M,
        (∀ (U : Opens (liftedSpace.{max a r u} X)) (hy : y ∈ U)
          (c : R.obj.obj (op (opensEquiv X U))),
          eR (TopCat.Presheaf.germ (C := RingCat.{max a r u}) (liftedRing.{a} R).obj U y hy
            (sectionRingEquiv.{a} R U c)) =
            originalRingGerm.{a} R x (opensEquiv X U) hy c) ∧
        (∀ (M : AmbientPresheaves.{a} R) (U : Opens (liftedSpace.{max a r u} X))
          (hy : y ∈ U) (s : M.obj (op (opensEquiv X U))),
          eM M (TopCat.Presheaf.germ (C := AddCommGrpCat.{max a r u}) (F.obj M).presheaf U y hy s) =
            originalModuleGerm.{a} R x M (opensEquiv X U) hy s) ∧
        (∀ (M : AmbientPresheaves.{a} R) (c : TopCat.Presheaf.stalk (C := RingCat.{max a r u}) (X := liftedSpace.{max a r u} X) (liftedRing.{a} R).obj y)
          (s : TopCat.Presheaf.stalk (C := AddCommGrpCat.{max a r u}) (X := liftedSpace.{max a r u} X) (F.obj M).presheaf y),
          eM M (c • s) = eR c • eM M s) ∧
        (∀ (M N : AmbientPresheaves.{a} R) (f : M ⟶ N)
          (s : TopCat.Presheaf.stalk (C := AddCommGrpCat.{max a r u}) (X := liftedSpace.{max a r u} X) (F.obj M).presheaf y),
          eM N ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{max a r u} y).map
            ((PresheafOfModules.toPresheaf _).map (F.map f)) s) =
            originalModuleStalkMap.{a} R x f (eM M s))

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Presheaf RingCat.{r})

/-- Germ-local short exactness is described on the original opens, so this
formulation applies even when small coefficient carriers do not suffice for
forming all site-indexed colimits. -/
def GermLocallyShortExact (S : ShortComplex (PresheafOfModules.{m} R)) : Prop :=
  (∀ (U : Opens X) (x : X) (_ : x ∈ U) (s : S.X₁.obj (op U)),
    S.f.app (op U) s = 0 →
      ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧ S.X₁.map i.op s = 0) ∧
  (∀ (U : Opens X) (x : X) (_ : x ∈ U) (s : S.X₂.obj (op U)),
    S.g.app (op U) s = 0 →
      ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧
        ∃ t : S.X₁.obj (op V), S.f.app (op V) t = S.X₂.map i.op s) ∧
  (∀ (U : Opens X) (x : X) (_ : x ∈ U) (s : S.X₃.obj (op U)),
      ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧
        ∃ t : S.X₂.obj (op V), S.g.app (op V) t = S.X₃.map i.op s)

instance {C : Type u} [Category C] (S : Cᵒᵖ ⥤ RingCat.{r}) :
    (liftCoefficients.{a,u,r,m} S).Additive where

instance (S : X.Sheaf RingCat.{r}) : (liftSheafCoefficients.{a,u,r,m} S).Additive where

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

def coefficientLiftPresheafExact : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Presheaf RingCat.{r}),
    PreservesFiniteLimits (liftCoefficients.{a,u,r,m} R) ∧
      PreservesFiniteColimits (liftCoefficients.{a,u,r,m} R)

def coefficientLiftGermLocal : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Presheaf RingCat.{r})
    (S : ShortComplex (PresheafOfModules.{m} R)),
    GermLocallyShortExact R (S.map (liftCoefficients.{a,u,r,m} R)) ↔ GermLocallyShortExact R S

def coefficientLiftSheafGermLocal : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r})
    (S : ShortComplex (SheafOfModules.{m} R)),
    GermLocallyShortExact R.obj
      ((S.map (liftSheafCoefficients.{a,u,r,m} R)).map (SheafOfModules.forget R)) ↔
      GermLocallyShortExact R.obj (S.map (SheafOfModules.forget R))

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

def coefficientLiftEmbedding : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}),
    ((liftCoefficients.{a,u,r,m} R.obj).Full ∧ (liftCoefficients.{a,u,r,m} R.obj).Faithful) ∧
    ((liftSheafCoefficients.{a,u,r,m} R).Full ∧
      (liftSheafCoefficients.{a,u,r,m} R).Faithful)

/-- The coefficient embeddings commute with all the original section and
restriction maps, retaining the original scalar actions. -/
def coefficientLiftSections : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Presheaf RingCat.{r})
      (M N : PresheafOfModules.{m} R) (f : M ⟶ N)
      (U V : Opens X) (i : U ⟶ V)
      (c : R.obj (op V)) (s : M.obj (op V)),
    let L := liftCoefficients.{a,u,r,m} R
    let e (P : PresheafOfModules.{m} R) (W : Opens X) :
        P.obj (op W) ≃ₗ[R.obj (op W)] (L.obj P).obj (op W) :=
      ULift.moduleEquiv.symm
    e M V (c • s) = c • e M V s ∧
      e M U (M.map i.op s) = (L.obj M).map i.op (e M V s) ∧
      e N V (f.app (op V) s) = (L.map f).app (op V) (e M V s)

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (U : Opens X)

/-- Restriction to the open subspace equipped with its original restricted ring. -/
def originalRestriction :
    AmbientSheaves.{a} R ⥤ SheafOfModules.{max a u r} (U.sheafRestrict.obj R) :=
  SheafOfModules.overFunctor R U ⋙ (U.sheafOfModulesEquivOver R).functor

instance originalOverRestrictionIsLeftAdjoint :
    (SheafOfModules.overFunctor.{max a u r} R U).IsLeftAdjoint := by
  unfold SheafOfModules.overFunctor
  infer_instance

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

def originalRestrictionExact : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens X),
    PreservesFiniteLimits (originalRestriction.{a} R U) ∧
    PreservesFiniteColimits (originalRestriction.{a} R U)

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable (U : Opens (liftedSpace.{max a r u} X))

abbrev overOpensEquiv :
    Over U ≌ Over (opensEquiv X U) :=
  Over.postEquiv U (opensEquiv.{max a r u} X).equivalence

instance overOpensEquivContinuous :
    (overOpensEquiv.{a,u,r} U).functor.IsContinuous
      ((Opens.grothendieckTopology _).over U)
      ((Opens.grothendieckTopology _).over (opensEquiv X U)) := by
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
  exact (opensCongrCoverPreserving (X.uliftFunctorObjHomeo.{max a r u}).symm).overPost U

/-- Transport a sheaf on the original open in over-site coordinates. -/
def transportOver :
    SheafOfModules.{max a u r} (R.over (opensEquiv X U)) ⥤
      SheafOfModules.{max a u r} ((liftedRing.{a} R).over U) :=
  liftScalarsOnSite.{a} (R.over (opensEquiv X U)) ⋙
    SheafOfModules.pushforward (F := (overOpensEquiv.{a,u,r} U).functor) (𝟙 _)

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

def transportOverRestrictionType :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens (liftedSpace.{max a r u} X)),
    SheafOfModules.overFunctor.{max a u r} R (opensEquiv X U) ⋙ transportOver.{a} R U ≅
      transport.{a} R ⋙ SheafOfModules.overFunctor (liftedRing.{a} R) U

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Exact extension and preservation of injectives on the actual original open subspace. -/
def originalOpenExtension : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (V : Opens X),
    ∃ L : SheafOfModules.{max a u r} (V.sheafRestrict.obj R) ⥤ AmbientSheaves.{a} R,
      Nonempty (L ⊣ originalRestriction.{a} R V) ∧
        PreservesFiniteLimits L ∧ PreservesFiniteColimits L ∧
        ∀ M : AmbientSheaves.{a} R,
          Injective M → Injective ((originalRestriction.{a} R V).obj M)

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V : Opens X)

/-- The unit module on the original over site, with its section ring placed in
the adequate carrier universe. -/
def originalOverUnit : SheafOfModules.{max a u r} (R.over V) :=
  ⟨(liftCoefficients.{max a u,u,r,r} (R.over V).obj).obj
    (SheafOfModules.unit (R.over V)).val,
    Presheaf.isSheaf_comp_of_isSheaf _ _ AddCommGrpCat.uliftFunctor
      (SheafOfModules.unit (R.over V)).isSheaf⟩

/-- The element one of the original open unit in its chosen carrier. -/
def originalOverOne (W : (Over V)ᵒᵖ) : (originalOverUnit.{a} R V).val.obj W :=
  ULift.up (1 : (R.over V).obj.obj W)

/-- The distinguished section of an original extended unit is obtained from
the actual adjunction unit at the terminal over-open. -/
def originalOverGenerator
    (L : SheafOfModules.{max a u r} (R.over V) ⥤ AmbientSheaves.{a} R)
    (A : L ⊣ SheafOfModules.overFunctor R V) :
    ((L.obj (originalOverUnit.{a} R V)).val.obj (op V) : Type (max a u r)) :=
  (A.unit.app (originalOverUnit.{a} R V)).val.app (op (Over.mk (𝟙 V)))
    (originalOverOne.{a} R V (op (Over.mk (𝟙 V))))

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

def originalOverUnitRepresentation : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (V : Opens X)
    (L : SheafOfModules.{max a u r} (R.over V) ⥤ AmbientSheaves.{a} R)
    (A : L ⊣ SheafOfModules.overFunctor R V) (M : AmbientSheaves.{a} R),
    ∃ e : (L.obj (originalOverUnit.{a} R V) ⟶ M) ≃+ M.val.obj (op V),
      ∀ f, e f = f.val.app (op V) (originalOverGenerator.{a} R V L A)

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Forgetting module scalars commutes with the site transport and with raising
coefficient carriers. -/
def forgetAbelianComparison :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}),
    (transport.{a} R ⋙ SheafOfModules.toSheaf (liftedRing.{a} R) ≅
      SheafOfModules.toSheaf R ⋙
        (opensEquiv.{max a u r} X).equivalence.functor.sheafPushforwardContinuous
          AddCommGrpCat.{max a u r} _ _) ×
    (liftSheafCoefficients.{a,u,r,m} R ⋙ SheafOfModules.toSheaf R ≅
      SheafOfModules.toSheaf R ⋙ sheafCompose (Opens.grothendieckTopology X)
        AddCommGrpCat.uliftFunctor.{a,m})

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

def coefficientEvaluationComparison :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (V : Opens X),
    (liftSheafCoefficients.{a,u,r,m} R ⋙ SheafOfModules.evaluation R (op V)) ≅
      SheafOfModules.evaluation.{m} R (op V) ⋙
        ModuleCat.uliftFunctor.{a,m} (R.obj.obj (op V))

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open SheafTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The constant presheaf that gives the original constant integer ring sheaf. -/
abbrev constantIntegerPresheaf (X : TopCat.{u}) : X.Presheaf RingCat.{u} :=
  (Functor.const _).obj (RingCat.of (ULift.{u} ℤ))

/-- The two successive carrier lifts of the integer ring give the usual integer ring
in the target universe. -/
def doubleLiftIntegerIso :
    (ringLift.{max a u}).obj (RingCat.of (ULift.{u} ℤ)) ≅
      RingCat.of (ULift.{max a u} ℤ) :=
  (ULift.ringEquiv.trans (ULift.ringEquiv.trans ULift.ringEquiv.symm)).toRingCatIso

/-- A constant integer on a lifted open comes from the same integer on the
corresponding original open. -/
def transportedIntegerSheafificationMap (X : TopCat.{u}) :
    constantIntegerPresheaf (liftedSpace.{max a u} X) ⟶
      (liftedRing.{a} (constantIntegerRingSheaf X)).obj :=
  ((Functor.const _).mapIso doubleLiftIntegerIso.{a,u}).inv ≫
    Functor.whiskerLeft (opensEquiv.{max a u} X).equivalence.functor.op
      (Functor.whiskerRight (toSheafify (Opens.grothendieckTopology X)
        (constantIntegerPresheaf X)) ringLift.{max a u})

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport
open _root_.AdvancedHomologicalAlgebra.SheafTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The ring comparison intertwines the two sheafification maps on constants. -/
def constantIntegerTransportType :=
  ∀ (X : TopCat.{u}),
    {e : constantIntegerRingSheaf (liftedSpace.{max a u} X) ≅
        liftedRing.{a} (constantIntegerRingSheaf X) //
      toSheafify (Opens.grothendieckTopology (liftedSpace.{max a u} X))
        (constantIntegerPresheaf (liftedSpace.{max a u} X)) ≫ e.hom.hom =
          transportedIntegerSheafificationMap.{a} X}

/-- The equivalence with original abelian sheaves uses their actual underlying
groups and restriction maps, because its functor is the forgetful functor. -/
def originalIntegerForgetEquivalence : Prop :=
  ∀ (X : TopCat.{u}),
    (SheafOfModules.toSheaf.{max a u} (constantIntegerRingSheaf X)).IsEquivalence

def ambientAbelian : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}),
    Nonempty (Abelian (AmbientSheaves.{a} R))

def originalInjectivesFlasque : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (M : AmbientSheaves.{a} R),
    Injective M → IsFlasque R M

def originalSectionsLeftExact : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (V : Opens X),
    PreservesFiniteLimits (SheafOfModules.evaluation.{max a u r} R (op V))

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

variable {X : TopCat.{u}} (R : X.Presheaf RingCat.{r}) (x : X)

/-- The additive stalk on the original space, formed from its actual neighborhood diagram.
The coefficient universe may be larger than the site universe. -/
def originalAdditiveStalkFunctor :
    PresheafOfModules.{max u m} R ⥤ AddCommGrpCat.{max u m} :=
  PresheafOfModules.toPresheaf R ⋙
    (Functor.whiskeringLeft _ _ _).obj (OpenNhds.inclusion x).op ⋙ colim

instance : (originalAdditiveStalkFunctor.{u,r,m} R x).Additive := by
  unfold originalAdditiveStalkFunctor
  infer_instance

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

/-- The local conditions describe short exactness of the actual additive stalk complexes. -/
def germLocalShortExactStalks : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Presheaf RingCat.{r})
    (S : ShortComplex (PresheafOfModules.{max u m} R)),
    GermLocallyShortExact R S ↔
      ∀ x : X, (S.map (originalAdditiveStalkFunctor.{u,r,m} R x)).ShortExact

/-- For an arbitrary original coefficient size, the ambient additive stalks
formed after placing each original section carrier in the ambient universe
test exactly the original germ-local conditions. -/
def coefficientLiftStalkExact : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Presheaf RingCat.{r})
    (S : ShortComplex (PresheafOfModules.{m} R)),
    GermLocallyShortExact R S ↔
      ∀ x : X, ((S.map (liftCoefficients.{max a u} R)).map
        (originalAdditiveStalkFunctor.{u,r,max a m} R x)).ShortExact

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The short exact structure of the original ambient category is tested on
its actual neighborhood colimits. -/
def ambientSheafShortExactStalks : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (S : ShortComplex (AmbientSheaves.{a} R)),
    S.ShortExact ↔ ∀ x : X,
      (S.map (SheafOfModules.forget R ⋙ originalAdditiveStalkFunctor.{u,r,max a r} R.obj x)).ShortExact

/-- The original ambient sheaf category has precisely the germ-local short exact sequences. -/
def ambientSheafGermLocalShortExact : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (S : ShortComplex (AmbientSheaves.{a} R)),
    S.ShortExact ↔ GermLocallyShortExact R.obj (S.map (SheafOfModules.forget R))

/-- The objectwise lift on ambient sheaves preserves the finite limit and
colimit exact structure between the ambient categories. -/
def coefficientLiftAmbientSheafExact : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}),
    PreservesFiniteLimits (liftSheafCoefficients.{a,u,r,max m u r} R) ∧
      PreservesFiniteColimits (liftSheafCoefficients.{a,u,r,max m u r} R)

/-- Germ-locally short exact sequences of every original coefficient size are
precisely the sequences mapped to categorical short exact sequences in the
ambient sheaf category. -/
def coefficientLiftOriginalSheafShortExact : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (S : ShortComplex (SheafOfModules.{m} R)),
    GermLocallyShortExact R.obj (S.map (SheafOfModules.forget R)) ↔
      (S.map (liftSheafCoefficients.{max a u r,u,r,m} R)).ShortExact

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport
open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport
open CategoryTheory.Functor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable (U : Opens (liftedSpace.{max a r u} X))

/-- The actual unit sheaf of the original restricted ring, in the ambient universe. -/
def originalRestrictedUnit (V : Opens X) :
    SheafOfModules.{max a u r} (V.sheafRestrict.obj R) :=
  ⟨(liftCoefficients.{max a u,u,r,r} (V.sheafRestrict.obj R).obj).obj
      (SheafOfModules.unit (V.sheafRestrict.obj R)).val,
    Presheaf.isSheaf_comp_of_isSheaf _ _ AddCommGrpCat.uliftFunctor
      (SheafOfModules.unit (V.sheafRestrict.obj R)).isSheaf⟩

private def originalOverUnitToRestricted (V : Opens X) :
    (V.sheafOfModulesEquivOver R).functor.obj (originalOverUnit.{a} R V) ≅
      originalRestrictedUnit.{a} R V :=
  Iso.refl _

/-- The canonical comparison of the actual open unit with its over-site model. -/
def originalRestrictedUnitOverIso (V : Opens X) :
    (V.sheafOfModulesEquivOver R).inverse.obj (originalRestrictedUnit.{a} R V) ≅
      originalOverUnit.{a} R V :=
  (V.sheafOfModulesEquivOver R).inverse.mapIso (originalOverUnitToRestricted.{a} R V).symm ≪≫
    ((V.sheafOfModulesEquivOver R).unitIso.app _).symm

/-- Transport on the open subspaces via their canonical over-site equivalences. -/
def transportOnOpen :
    SheafOfModules.{max a u r} ((opensEquiv X U).sheafRestrict.obj R) ⥤
      SheafOfModules.{max a u r} (U.sheafRestrict.obj (liftedRing.{a} R)) :=
  ((opensEquiv X U).sheafOfModulesEquivOver R).inverse ⋙ transportOver.{a} R U ⋙
    (U.sheafOfModulesEquivOver (liftedRing.{a} R)).functor

/-- Extension from the actual open, given extension from its canonical over-site model. -/
abbrev originalExtensionOf
    (L : SheafOfModules.{max a u r} (R.over (opensEquiv X U)) ⥤ AmbientSheaves.{a} R) :
    SheafOfModules.{max a u r} ((opensEquiv X U).sheafRestrict.obj R) ⥤ AmbientSheaves.{a} R :=
  ((opensEquiv X U).sheafOfModulesEquivOver R).inverse ⋙ L

/-- The original extension applied to the module of the restricted structure sheaf. -/
abbrev originalExtendedUnitOf
    (L : SheafOfModules.{max a u r} (R.over (opensEquiv X U)) ⥤ AmbientSheaves.{a} R) :
    AmbientSheaves.{a} R :=
  (originalExtensionOf.{a} R U L).obj (originalRestrictedUnit.{a} R (opensEquiv X U))

/-- The extension of the unit has the original generator given by the
adjunction on the terminal over-open, expressed on the actual open. -/
def originalExtendedGeneratorOf
    (L : SheafOfModules.{max a u r} (R.over (opensEquiv X U)) ⥤ AmbientSheaves.{a} R)
    (A : L ⊣ SheafOfModules.overFunctor R (opensEquiv X U)) :
    (originalExtendedUnitOf.{a} R U L).val.obj (op (opensEquiv X U)) :=
  (L.mapIso (originalRestrictedUnitOverIso.{a} R (opensEquiv X U))).inv.val.app
    (op (opensEquiv X U)) (originalOverGenerator.{a} R (opensEquiv X U) L A)

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable (U : Opens (liftedSpace.{max a r u} X))

/-- Transport and the two open inclusion operations, with the normalization
of the section representation on the actual original extended unit. -/
structure OpenTransportData where
  overExtension : SheafOfModules.{max a u r} (R.over (opensEquiv X U)) ⥤ AmbientSheaves.{a} R
  overAdjunction : overExtension ⊣ SheafOfModules.overFunctor R (opensEquiv X U)
  overExtensionComparison : overExtension ⋙ transport.{a} R ≅
    transportOver.{a} R U ⋙ _root_.AdvancedHomologicalAlgebra.SheafTheory.extensionFromOver (liftedRing.{a} R) U
  originalOpenAdjunction : originalExtensionOf.{a} R U overExtension ⊣
    originalRestriction.{a} R (opensEquiv X U)
  transportOnOpenIsEquivalence : (transportOnOpen.{a} R U).IsEquivalence
  restrictionComparison : originalRestriction.{a} R (opensEquiv X U) ⋙ transportOnOpen.{a} R U ≅
    transport.{a} R ⋙ _root_.AdvancedHomologicalAlgebra.SheafTheory.restriction (liftedRing.{a} R) U
  extensionComparison : originalExtensionOf.{a} R U overExtension ⋙ transport.{a} R ≅
    transportOnOpen.{a} R U ⋙ _root_.AdvancedHomologicalAlgebra.SheafTheory.extensionByZero (liftedRing.{a} R) U
  preservesFiniteLimits : PreservesFiniteLimits (originalExtensionOf.{a} R U overExtension)
  preservesFiniteColimits : PreservesFiniteColimits (originalExtensionOf.{a} R U overExtension)
  extensionStalkOnOpen
      (M : SheafOfModules.{max a u r} ((opensEquiv X U).sheafRestrict.obj R))
      (x : (opensEquiv X U : Opens X)) :
    originalStalkGroup.{a} (X := TopCat.of (opensEquiv X U : Opens X))
      ((opensEquiv X U).sheafRestrict.obj R) x M.val ≅
    originalStalkGroup.{a} R x.1 ((originalExtensionOf.{a} R U overExtension).obj M).val
  extensionStalkRing (x : (opensEquiv X U : Opens X)) :
    originalStalkRing.{a} (X := TopCat.of (opensEquiv X U : Opens X))
      ((opensEquiv X U).sheafRestrict.obj R) x ≅ originalStalkRing.{a} R x.1
  extensionStalkRingGerm
      (x : (opensEquiv X U : Opens X)) (T : Opens (opensEquiv X U : Opens X)) (hx : x ∈ T)
      (c : ((opensEquiv X U).sheafRestrict.obj R).obj.obj (op T)) :
    (extensionStalkRing x).hom
      (originalRingGerm.{a} (X := TopCat.of (opensEquiv X U : Opens X))
        ((opensEquiv X U).sheafRestrict.obj R) x T hx c) =
    originalRingGerm.{a} R x.1 ((opensEquiv X U).isOpenEmbedding.isOpenMap.functor.obj T)
      ⟨x, hx, rfl⟩ c
  extensionStalkGerm
      (M : SheafOfModules.{max a u r} ((opensEquiv X U).sheafRestrict.obj R))
      (x : (opensEquiv X U : Opens X)) (T : Opens (opensEquiv X U : Opens X)) (hx : x ∈ T)
      (s : M.val.obj (op T)) :
    (extensionStalkOnOpen M x).hom
      (originalModuleGerm.{a} (X := TopCat.of (opensEquiv X U : Opens X))
        ((opensEquiv X U).sheafRestrict.obj R) x M.val T hx s) =
    originalModuleGerm.{a} R x.1 ((originalExtensionOf.{a} R U overExtension).obj M).val
      ((opensEquiv X U).isOpenEmbedding.isOpenMap.functor.obj T) ⟨x, hx, rfl⟩
      ((originalOpenAdjunction.unit.app M).val.app (op T) s)
  extensionStalkSmul
      (M : SheafOfModules.{max a u r} ((opensEquiv X U).sheafRestrict.obj R))
      (x : (opensEquiv X U : Opens X))
      (c : originalStalkRing.{a} (X := TopCat.of (opensEquiv X U : Opens X))
        ((opensEquiv X U).sheafRestrict.obj R) x)
      (s : originalStalkGroup.{a} (X := TopCat.of (opensEquiv X U : Opens X))
        ((opensEquiv X U).sheafRestrict.obj R) x M.val) :
    letI := originalStalkModule.{a} (X := TopCat.of (opensEquiv X U : Opens X))
      ((opensEquiv X U).sheafRestrict.obj R) x M.val
    (extensionStalkOnOpen M x).hom (c • s) =
      (extensionStalkRing x).hom c • (extensionStalkOnOpen M x).hom s
  extensionZeroOffOpen
      (M : SheafOfModules.{max a u r} ((opensEquiv X U).sheafRestrict.obj R))
      (x : X) (hx : x ∉ opensEquiv X U) :
    IsZero (originalStalkGroup.{a} R x ((originalExtensionOf.{a} R U overExtension).obj M).val)
  unitComparison : (transport.{a} R).obj (originalExtendedUnitOf.{a} R U overExtension) ≅
    _root_.AdvancedHomologicalAlgebra.SheafTheory.openUnit (liftedRing.{a} R) U
  generatorComparison : unitComparison.hom.val.app (op U)
      (sectionEquiv.{a} R _ U (originalExtendedGeneratorOf.{a} R U overExtension overAdjunction)) =
    _root_.AdvancedHomologicalAlgebra.SheafTheory.openUnitGenerator (liftedRing.{a} R) U
  sectionRepresentation (M : AmbientSheaves.{a} R) :
    (originalExtendedUnitOf.{a} R U overExtension ⟶ M) ≃+ M.val.obj (op (opensEquiv X U))
  sectionRepresentation_apply (M : AmbientSheaves.{a} R)
      (f : originalExtendedUnitOf.{a} R U overExtension ⟶ M) :
    sectionRepresentation M f = f.val.app (op (opensEquiv X U))
      (originalExtendedGeneratorOf.{a} R U overExtension overAdjunction)
  sectionRepresentation_transport (M : AmbientSheaves.{a} R)
      (f : originalExtendedUnitOf.{a} R U overExtension ⟶ M) :
    sectionEquiv.{a} R M U (sectionRepresentation M f) =
      (unitComparison.inv ≫ (transport.{a} R).map f).val.app (op U)
        (_root_.AdvancedHomologicalAlgebra.SheafTheory.openUnitGenerator (liftedRing.{a} R) U)

def openTransportDataType :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (U : Opens (liftedSpace.{max a r u} X)),
    OpenTransportData.{a} R U

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

variable {X : TopCat.{u}} {R : X.Presheaf RingCat.{r}} (x : X)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The additive germ induced by the original neighborhood diagram. -/
def originalAdditiveGerm (M : PresheafOfModules.{max u m} R) (U : Opens X) (hx : x ∈ U) :
    M.obj (op U) →+ (originalAdditiveStalkFunctor.{u,r,m} R x).obj M :=
  (colimit.ι ((OpenNhds.inclusion x).op ⋙ M.presheaf) (op ⟨U, hx⟩)).hom

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Raising already adequate coefficient universes commutes with the
original neighborhood colimits and their germ maps. -/
def coefficientLiftStalkComparison : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Presheaf RingCat.{r}) (x : X),
    let L := liftCoefficients.{a,u,r,max u m} R
    let F := originalAdditiveStalkFunctor.{u,r,m} R x
    let G := originalAdditiveStalkFunctor.{u,r,max a m} R x
    ∃ e : F ⋙ AddCommGrpCat.uliftFunctor.{a} ≅ L ⋙ G,
      ∀ (M : PresheafOfModules.{max u m} R) (U : Opens X) (hx : x ∈ U) (s : M.obj (op U)),
        (e.hom.app M) (ULift.up (originalAdditiveGerm x M U hx s)) =
          originalAdditiveGerm x (L.obj M) U hx (ULift.up s)

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport
open _root_.AdvancedHomologicalAlgebra.SheafTheory (sectionRing)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{r}}
variable {U : Opens (liftedSpace.{max a r u} X)}
variable (D : OpenTransportData.{a} R U)

/-- Right multiplication on the extended unit, characterized by its value
on the distinguished section. -/
def originalExtendedUnitRightMul (c : sectionRing R (opensEquiv X U)) :
    originalExtendedUnitOf.{a} R U D.overExtension ⟶
      originalExtendedUnitOf.{a} R U D.overExtension :=
  (D.sectionRepresentation _).symm
    (c • originalExtendedGeneratorOf.{a} R U D.overExtension D.overAdjunction)

/-- In the original section ring, the natural Hom representation is linear for
the action by precomposition with right multiplication. Transport intertwines
that action with the common-universe action. -/
def openTransportLinear : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r})
    (U : Opens (liftedSpace.{max a r u} X)) (D : OpenTransportData.{a} R U)
    (M : AmbientSheaves.{a} R),
    let V := opensEquiv X U
    letI := (D.sectionRepresentation M).module (sectionRing R V)
    (∀ (c : sectionRing R V) (f : originalExtendedUnitOf.{a} R U D.overExtension ⟶ M),
      c • f = originalExtendedUnitRightMul D c ≫ f) ∧
    (∃ e : (originalExtendedUnitOf.{a} R U D.overExtension ⟶ M) ≃ₗ[sectionRing R V]
        M.val.obj (op V),
      ∀ f, e f = f.val.app (op V)
        (originalExtendedGeneratorOf.{a} R U D.overExtension D.overAdjunction)) ∧
    (∀ (c : sectionRing R V) (f : originalExtendedUnitOf.{a} R U D.overExtension ⟶ M),
      D.unitComparison.inv ≫ (transport.{a} R).map (c • f) =
        _root_.AdvancedHomologicalAlgebra.SheafTheory.openRightMul (liftedRing.{a} R) U
          (sectionRingEquiv.{a} R U c) ≫ D.unitComparison.inv ≫ (transport.{a} R).map f) ∧
    (∀ (N : AmbientSheaves.{a} R)
      (f : originalExtendedUnitOf.{a} R U D.overExtension ⟶ M) (g : M ⟶ N),
      D.sectionRepresentation N (f ≫ g) = g.val.app (op V) (D.sectionRepresentation M f))

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (x : X)

/-- The stalk of an ambient module sheaf over the original opening diagram. -/
abbrev originalStalkModuleCat (M : AmbientSheaves.{a} R) :
    ModuleCat.{max a u r} (originalStalkRing.{a} R x) :=
  ModuleCat.of _ (originalStalkGroup.{a} R x M.val)

/-- The underlying additive skyscraper on the original site. -/
def originalSkyscraperGroups (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)) :
    X.Presheaf AddCommGrpCat.{max a u r} where
  obj U := AddCommGrpCat.of (PLift (x ∈ U.unop) → N)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun s hx ↦ s ⟨i.unop.le hx.down⟩
      map_zero' := rfl
      map_add' := by intros; rfl }
  map_id U := by ext s hx; rfl
  map_comp i j := by ext s hx; rfl

/-- Each nonzero section module uses restriction of scalars along the original germ. -/
instance originalSkyscraperSectionModule
    (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)) (U : (Opens X)ᵒᵖ) :
    Module (R.obj.obj U) ((originalSkyscraperGroups.{a} R x N).obj U) :=
  letI (hx : PLift (x ∈ U.unop)) : Module (R.obj.obj U) N :=
    Module.compHom N (originalRingGerm.{a} R x U.unop hx.down)
  inferInstanceAs (Module (R.obj.obj U) (PLift (x ∈ U.unop) → N))

lemma originalRingGerm_restrict {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (hx : x ∈ V.unop) (c : R.obj.obj U) :
    originalRingGerm.{a} R x V.unop hx (R.obj.map i c) =
      originalRingGerm.{a} R x U.unop (i.unop.le hx) c := by
  let j : (op (⟨U.unop, i.unop.le hx⟩ : OpenNhds x)) ⟶ op (⟨V.unop, hx⟩ : OpenNhds x) :=
    (homOfLE i.unop.le).op
  exact congr($(colimit.w (ringNeighborhoods.{a} R x) j) (ULift.up c))

/-- The skyscraper presheaf with its original semilinear restrictions. -/
def originalSkyscraperPresheaf (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)) :
    AmbientPresheaves.{a} R :=
  PresheafOfModules.ofPresheaf (originalSkyscraperGroups.{a} R x N) (by
    intro U V i c s
    funext hx
    change originalRingGerm.{a} R x U.unop (i.unop.le hx.down) c • (s ⟨i.unop.le hx.down⟩ : N) =
      originalRingGerm.{a} R x V.unop hx.down (R.obj.map i c) • (s ⟨i.unop.le hx.down⟩ : N)
    rw [originalRingGerm_restrict])

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (x : X)

lemma originalModuleStalkMap_germ {M N : AmbientPresheaves.{a} R} (f : M ⟶ N)
    (U : Opens X) (hx : x ∈ U) (s : M.obj (op U)) :
    originalModuleStalkMap.{a} R x f (originalModuleGerm.{a} R x M U hx s) =
      originalModuleGerm.{a} R x N U hx (f.app (op U) s) :=
  congr($(ι_colimMap (Functor.whiskerLeft (OpenNhds.inclusion x).op
      ((PresheafOfModules.toPresheaf R.obj).map f)) (op ⟨U, hx⟩)) s)

lemma originalModuleGerm_restrict (M : AmbientPresheaves.{a} R) {U V : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (hx : x ∈ V.unop) (s : M.obj U) :
    originalModuleGerm.{a} R x M V.unop hx (M.map i s) =
      originalModuleGerm.{a} R x M U.unop (i.unop.le hx) s := by
  let j : (op (⟨U.unop, i.unop.le hx⟩ : OpenNhds x)) ⟶ op (⟨V.unop, hx⟩ : OpenNhds x) :=
    (homOfLE i.unop.le).op
  exact congr($(colimit.w (moduleNeighborhoods.{a} R x M) j) s)

lemma originalModuleGerm_exists (M : AmbientPresheaves.{a} R)
    (s : originalStalkGroup.{a} R x M) :
    ∃ (U : Opens X) (hx : x ∈ U) (t : M.obj (op U)),
      originalModuleGerm.{a} R x M U hx t = s := by
  let D := moduleNeighborhoods.{a} R x M
  have : PreservesFilteredColimitsOfSize.{u,u} (CategoryTheory.forget AddCommGrpCat.{max a u r}) :=
    preservesFilteredColimitsOfSize_shrink.{u,max a u r,u,max a u r} _
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective (D ⋙ CategoryTheory.forget _)
    (isColimitOfPreserves (CategoryTheory.forget _) (colimit.isColimit D)) s
  exact ⟨j.unop.1, j.unop.2, t, ht⟩

lemma originalStalkGermsJoint (M : AmbientSheaves.{a} R) (c : originalStalkRing.{a} R x)
    (s : originalStalkModuleCat.{a} R x M) :
    ∃ (U : Opens X) (hx : x ∈ U) (d : R.obj.obj (op U)) (t : M.val.obj (op U)),
      originalRingGerm.{a} R x U hx d = c ∧ originalModuleGerm.{a} R x M.val U hx t = s := by
  let D := ringNeighborhoods.{a} R x
  have : PreservesFilteredColimitsOfSize.{u,u} (CategoryTheory.forget RingCat.{max a u r}) :=
    preservesFilteredColimitsOfSize_shrink.{u,max a u r,u,max a u r} _
  obtain ⟨j, d, hd⟩ := Types.jointly_surjective (D ⋙ CategoryTheory.forget _)
    (isColimitOfPreserves (CategoryTheory.forget _) (colimit.isColimit D)) c
  obtain ⟨V, hV, t, ht⟩ := originalModuleGerm_exists.{a} R x M.val s
  let W : Opens X := j.unop.1 ⊓ V
  have hx : x ∈ W := ⟨j.unop.2, hV⟩
  refine ⟨W, hx, R.obj.map (homOfLE inf_le_left).op d.down,
    M.val.map (homOfLE inf_le_right).op t, ?_, ?_⟩
  · rw [originalRingGerm_restrict]
    exact hd
  · rw [originalModuleGerm_restrict]
    exact ht

/-- The stalk functor maps morphisms by the actual map of original diagrams. -/
def originalStalkFunctor : AmbientSheaves.{a} R ⥤ ModuleCat.{max a u r} (originalStalkRing.{a} R x) where
  obj := originalStalkModuleCat.{a} R x
  map {M N} f := ModuleCat.ofHom
    { toFun := originalModuleStalkMap.{a} R x f.val
      map_add' := map_add _
      map_smul' := by
        intro c s
        obtain ⟨U, hx, d, t, rfl, rfl⟩ := originalStalkGermsJoint.{a} R x M c s
        change originalModuleStalkMap.{a} R x f.val
            (originalRingGerm.{a} R x U hx d • originalModuleGerm.{a} R x M.val U hx t) =
          originalRingGerm.{a} R x U hx d •
            originalModuleStalkMap.{a} R x f.val (originalModuleGerm.{a} R x M.val U hx t)
        rw [← original_germ_smul, originalModuleStalkMap_germ, originalModuleStalkMap_germ,
          (f.val.app (op U)).hom.map_smul, original_germ_smul] }
  map_id M := by
    ext s
    obtain ⟨U, hx, t, rfl⟩ := originalModuleGerm_exists.{a} R x M.val s
    exact originalModuleStalkMap_germ.{a} R x (𝟙 M.val) U hx t
  map_comp {M N P} f g := by
    ext s
    obtain ⟨U, hx, t, rfl⟩ := originalModuleGerm_exists.{a} R x M.val s
    change originalModuleStalkMap.{a} R x (f.val ≫ g.val) (originalModuleGerm.{a} R x M.val U hx t) =
      originalModuleStalkMap.{a} R x g.val
        (originalModuleStalkMap.{a} R x f.val (originalModuleGerm.{a} R x M.val U hx t))
    rw [originalModuleStalkMap_germ, originalModuleStalkMap_germ, originalModuleStalkMap_germ]
    rfl

/-- The direct skyscraper construction on the original space, including the
induced pointwise map on section groups. -/
def originalSkyscraperPresheafFunctor :
    ModuleCat.{max a u r} (originalStalkRing.{a} R x) ⥤ AmbientPresheaves.{a} R where
  obj := originalSkyscraperPresheaf.{a} R x
  map {N P} f :=
    { app U := ModuleCat.ofHom
        { toFun := fun s hx ↦ f (s hx)
          map_add' := by intro s t; funext hx; exact f.hom.map_add _ _
          map_smul' := by
            intro c s
            funext hx
            exact f.hom.map_smul (originalRingGerm.{a} R x U.unop hx.down c) (s hx) }
      naturality := by intros U V i; ext s; funext hx; rfl }
  map_id N := by ext U s; rfl
  map_comp f g := by ext U s; rfl

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport
open _root_.AdvancedHomologicalAlgebra.SheafTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (x : X)

set_option hygiene false in
local notation "Y" => liftedSpace.{max a u r} X
set_option hygiene false in
local notation "y" => X.uliftFunctorObjHomeo.{max a u r} x

/-- The common and original skyscraper models share the same scalar germs,
coefficient germs, sections, and adjunction on those sections. -/
structure OriginalStalkSkyscraperComparison where
  ring : stalkRing (liftedRing.{a} R) y ≃+* originalStalkRing.{a} R x
  ringGerm : ∀ (U : Opens Y) (hy : y ∈ U) (c : R.obj.obj (op (opensEquiv X U))),
    ring (TopCat.Presheaf.germ (liftedRing.{a} R).obj U y hy (sectionRingEquiv.{a} R U c)) =
      originalRingGerm.{a} R x (opensEquiv X U) hy c
  stalkIso : transport.{a} R ⋙ stalkFunctor (liftedRing.{a} R) y ≅
    originalStalkFunctor.{a} R x ⋙ ModuleCat.restrictScalars ring.toRingHom
  stalkGerm : ∀ (M : AmbientSheaves.{a} R) (U : Opens Y) (hy : y ∈ U)
    (s : M.val.obj (op (opensEquiv X U))),
      (stalkIso.hom.app M)
        (TopCat.Presheaf.germ (((transport.{a} R).obj M).val.presheaf) U y hy s) =
          originalModuleGerm.{a} R x M.val (opensEquiv X U) hy s
  exactLimits : PreservesFiniteLimits (originalStalkFunctor.{a} R x)
  exactColimits : PreservesFiniteColimits (originalStalkFunctor.{a} R x)
  skyscraper : ModuleCat.{max a u r} (originalStalkRing.{a} R x) ⥤ AmbientSheaves.{a} R
  skyscraperPresheafIso : skyscraper ⋙ SheafOfModules.forget R ≅
    originalSkyscraperPresheafFunctor.{a} R x
  skyscraperIso : skyscraper ⋙ transport.{a} R ≅
    ModuleCat.restrictScalars ring.toRingHom ⋙ skyscraperFunctor (liftedRing.{a} R) y
  skyscraperIsoOnSection : ∀ (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x))
    (U : Opens Y) (hy : y ∈ U) (s : (skyscraper.obj N).val.obj (op (opensEquiv X U))),
      ((skyscraperIso.hom.app N).val.app (op U) s) ⟨hy⟩ =
        ((skyscraperPresheafIso.hom.app N).app (op (opensEquiv X U)) s) ⟨hy⟩
  sections : ∀ (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)) (U : Opens X),
    (∀ (hx : x ∈ U), ∃ e : (skyscraper.obj N).val.obj (op U) ≃+ N,
      ∀ (c : R.obj.obj (op U)) (s : (skyscraper.obj N).val.obj (op U)),
        e (c • s) = originalRingGerm.{a} R x U hx c • e s) ∧
    (x ∉ U → Subsingleton ((skyscraper.obj N).val.obj (op U)))
  adjunction : originalStalkFunctor.{a} R x ⊣ skyscraper
  adjunctionOnGerm : ∀ (M : AmbientSheaves.{a} R) (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x))
    (f : (originalStalkFunctor.{a} R x).obj M ⟶ N) (U : Opens X) (hx : x ∈ U) (s : M.val.obj (op U)),
      (((adjunction.homEquiv M N f).val ≫ skyscraperPresheafIso.hom.app N).app (op U) s) ⟨hx⟩ =
        f (originalModuleGerm.{a} R x M.val U hx s)

/-- The skyscraper comparisons hold simultaneously for all points and original coefficients. -/
def originalStalkSkyscraperComparison : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (x : X),
    Nonempty (OriginalStalkSkyscraperComparison.{a} R x)

/-- In the same original skyscraper model there are monic maps into products
formed from arbitrary monic maps of stalks, and products of injective factors
are injective. -/
def originalStalkProductEmbedding : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}),
    ∃ D : ∀ x : X, OriginalStalkSkyscraperComparison.{a} R x,
      ∀ (M : AmbientSheaves.{a} R) (N : ∀ x : X, ModuleCat.{max a u r} (originalStalkRing.{a} R x))
        (i : ∀ x : X, (originalStalkFunctor.{a} R x).obj M ⟶ N x),
        let P := fun x ↦ (D x).skyscraper.obj (N x)
        let Q := fun x ↦ (skyscraperFunctor (liftedRing.{a} R)
          (X.uliftFunctorObjHomeo.{max a u r} x)).obj
            ((ModuleCat.restrictScalars (D x).ring.toRingHom).obj (N x))
        let f : M ⟶ ∏ᶜ P := Pi.lift (fun x ↦ (D x).adjunction.homEquiv M (N x) (i x))
        ((∀ x, Mono (i x)) → Mono f) ∧
          ((∀ x, Injective (N x)) → Injective (∏ᶜ P)) ∧
          ∃ e : (transport.{a} R).obj (∏ᶜ P) ≅ ∏ᶜ Q,
            (∀ x, e.hom ≫ Pi.π Q x =
              (transport.{a} R).map (Pi.π P x) ≫ (D x).skyscraperIso.hom.app (N x)) ∧
            (transport.{a} R).map f ≫ e.hom = Pi.lift (fun x ↦
              (transport.{a} R).map ((D x).adjunction.homEquiv M (N x) (i x)) ≫
                (D x).skyscraperIso.hom.app (N x))

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Coefficient lifts apply the original differentials and cochain maps on sections. -/
def coefficientLiftCochains : Prop :=
  (∀ (X : TopCat.{u}) (R : X.Presheaf RingCat.{r}) (ι : Type v) (c : ComplexShape ι)
    (K L : HomologicalComplex (PresheafOfModules.{m} R) c) (f : K ⟶ L)
    (i j : ι) (U : Opens X) (s : (K.X i).obj (op U)),
    let F := (liftCoefficients.{a,u,r,m} R).mapHomologicalComplex c
    ((F.obj K).d i j).app (op U) (ULift.up s) = ULift.up ((K.d i j).app (op U) s) ∧
      ((F.map f).f i).app (op U) (ULift.up s) = ULift.up ((f.f i).app (op U) s)) ∧
  (∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (ι : Type v) (c : ComplexShape ι)
    (K L : HomologicalComplex (SheafOfModules.{m} R) c) (f : K ⟶ L)
    (i j : ι) (U : Opens X) (s : (K.X i).val.obj (op U)),
    let F := (liftSheafCoefficients.{a,u,r,m} R).mapHomologicalComplex c
    ((F.obj K).d i j).val.app (op U) (ULift.up s) = ULift.up ((K.d i j).val.app (op U) s) ∧
      ((F.map f).f i).val.app (op U) (ULift.up s) = ULift.up ((f.f i).val.app (op U) s))

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport
open _root_.AdvancedHomologicalAlgebra.SheafTheory (openUnit openUnitGenerator)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{r}}
variable {U W : Opens (liftedSpace.{max a r u} X)}

/-- The arrow of extended units for an inclusion is the one that restricts
the target's canonical generator to the source open. -/
def originalOpenUnitMap (D : OpenTransportData.{a} R U) (E : OpenTransportData.{a} R W)
    (i : U ⟶ W) :
    originalExtendedUnitOf.{a} R U D.overExtension ⟶
      originalExtendedUnitOf.{a} R W E.overExtension :=
  (D.sectionRepresentation _).symm
    ((originalExtendedUnitOf.{a} R W E.overExtension).val.map
      (((opensEquiv.{max a u r} X).equivalence.functor).map i).op
      (originalExtendedGeneratorOf.{a} R W E.overExtension E.overAdjunction))

/-- The extension of unit modules for nested opens is monic, and the
transported arrow has the same characterization by its generator. -/
def openUnitMapTransport : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r})
    (U W : Opens (liftedSpace.{max a r u} X))
    (D : OpenTransportData.{a} R U) (E : OpenTransportData.{a} R W) (i : U ⟶ W),
    Mono (originalOpenUnitMap D E i) ∧
      (D.unitComparison.inv ≫ (transport.{a} R).map (originalOpenUnitMap D E i) ≫
        E.unitComparison.hom).val.app (op U) (openUnitGenerator (liftedRing.{a} R) U) =
        (openUnit (liftedRing.{a} R) W).val.map i.op (openUnitGenerator (liftedRing.{a} R) W)

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The restriction square retains the identical section and restriction maps. -/
def transportOverRestrictionValue : transportOverRestrictionType.{a,u,r} :=
  fun _ _ _ ↦ Iso.refl _

def forgetAbelianComparisonValue : forgetAbelianComparison.{a,u,r,m} :=
  fun _ _ ↦ ⟨Iso.refl _, Iso.refl _⟩

def coefficientEvaluationComparisonValue : coefficientEvaluationComparison.{a,u,r,m} :=
  fun _ _ _ ↦ Iso.refl _

def constantIntegerTransportExists : Prop := Nonempty constantIntegerTransportType.{a,u}

def openTransportExists : Prop := Nonempty openTransportDataType.{a,u,r}

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- The section comparison for an ambient presheaf retains its coefficient carrier. -/
def presheafSectionEquiv (M : AmbientPresheaves.{a} R)
    (U : Opens (liftedSpace.{max a r u} X)) :
    M.obj (op (opensEquiv X U)) ≃+ ((transportPresheaf.{a} R).obj M).obj (op U) :=
  AddEquiv.refl _

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The exact equivalence on ambient module presheaves is the stated pointwise transport. -/
def ambientPresheafExactEquivalence : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}),
    (transportPresheaf.{a} R).IsEquivalence ∧
      PreservesFiniteLimits (transportPresheaf.{a} R) ∧
      PreservesFiniteColimits (transportPresheaf.{a} R)

/-- Ambient presheaf comparisons retain the original restrictions, scalar actions and maps. -/
def ambientPresheafSections : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (M N : AmbientPresheaves.{a} R)
    (f : M ⟶ N) (U V : Opens (liftedSpace.{max a r u} X)) (i : U ⟶ V)
    (s : M.obj (op (opensEquiv X V))) (c : R.obj.obj (op (opensEquiv X V))),
    let e := (opensEquiv.{max a r u} X).equivalence.functor
    sectionRingEquiv.{a} R U (R.obj.map (e.map i).op c) =
      (liftedRing.{a} R).obj.map i.op (sectionRingEquiv.{a} R V c) ∧
    presheafSectionEquiv.{a} R M V (c • s) =
      sectionRingEquiv.{a} R V c • presheafSectionEquiv.{a} R M V s ∧
    presheafSectionEquiv.{a} R M U (M.map (e.map i).op s) =
      ((transportPresheaf.{a} R).obj M).map i.op (presheafSectionEquiv.{a} R M V s) ∧
    presheafSectionEquiv.{a} R N V (f.app (op (opensEquiv X V)) s) =
      ((transportPresheaf.{a} R).map f).app (op V) (presheafSectionEquiv.{a} R M V s)

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

universe b c d e f g

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{r}}

/-- A morphism of the given module sheaves, with independently sized section carriers. -/
structure SectionwiseHom (M : SheafOfModules.{b} R) (N : SheafOfModules.{c} R) where
  app (V : (Opens X)ᵒᵖ) : M.val.obj V →ₗ[R.obj.obj V] N.val.obj V
  naturality {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (s : M.val.obj V) :
    app W (M.val.map i s) = N.val.map i (app V s)

/-- Place a sectionwise morphism in a common category by conjugating its actual section maps. -/
def SectionwiseHom.lift {M : SheafOfModules.{b} R} {N : SheafOfModules.{c} R}
    (h : SectionwiseHom M N) :
    (liftSheafCoefficients.{max a b c} R).obj M ⟶
      (liftSheafCoefficients.{max a b c} R).obj N where
  val := PresheafOfModules.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ ULift.up (h.app V s.down)
          map_zero' := congrArg ULift.up (map_zero (h.app V))
          map_add' := fun s t ↦ congrArg ULift.up (map_add (h.app V) s.down t.down) }
      naturality := fun {_ _} i ↦ by
        ext s
        exact congrArg ULift.up (h.naturality i s.down) }
    (fun V k s ↦ congrArg ULift.up (map_smul (h.app V) k s.down))

/-- Three original coefficients with given maps whose composite is zero. -/
structure SectionwiseShortComplex (R : X.Sheaf RingCat.{r}) where
  first : SheafOfModules.{b} R
  middle : SheafOfModules.{c} R
  last : SheafOfModules.{d} R
  f : SectionwiseHom first middle
  g : SectionwiseHom middle last
  zero (V : (Opens X)ᵒᵖ) (s : first.val.obj V) : g.app V (f.app V s) = 0

/-- The ambient short complex has the lifts of the two actual maps on sections. -/
def SectionwiseShortComplex.lift (S : SectionwiseShortComplex.{u,r,b,c,d} R) :
    ShortComplex (AmbientSheaves.{max a b c d} R) :=
  ShortComplex.mk (S.f.lift.{max a u r d}) (S.g.lift.{max a u r b}) (by
    apply SheafOfModules.hom_ext
    ext V s
    exact congrArg ULift.up (S.zero V s.down))

/-- Exactness on the original germs, using local sections over the original opens. -/
def SectionwiseShortComplex.GermLocallyShortExact (S : SectionwiseShortComplex.{u,r,b,c,d} R) :
    Prop :=
  (∀ (V : Opens X) (x : X) (_ : x ∈ V) (s : S.first.val.obj (op V)),
    S.f.app (op V) s = 0 →
      ∃ (W : Opens X) (i : W ⟶ V), x ∈ W ∧ S.first.val.map i.op s = 0) ∧
  (∀ (V : Opens X) (x : X) (_ : x ∈ V) (s : S.middle.val.obj (op V)),
    S.g.app (op V) s = 0 →
      ∃ (W : Opens X) (i : W ⟶ V), x ∈ W ∧
        ∃ t : S.first.val.obj (op W), S.f.app (op W) t = S.middle.val.map i.op s) ∧
  (∀ (V : Opens X) (x : X) (_ : x ∈ V) (s : S.last.val.obj (op V)),
    ∃ (W : Opens X) (i : W ⟶ V), x ∈ W ∧
      ∃ t : S.middle.val.obj (op W), S.g.app (op W) t = S.last.val.map i.op s)

/-- A commuting diagram between two original short complexes of sheaves. -/
structure SectionwiseShortComplex.Hom (S : SectionwiseShortComplex.{u,r,b,c,d} R)
    (T : SectionwiseShortComplex.{u,r,e,f,g} R) where
  τ₁ : SectionwiseHom S.first T.first
  τ₂ : SectionwiseHom S.middle T.middle
  τ₃ : SectionwiseHom S.last T.last
  comm₁ (V : (Opens X)ᵒᵖ) (s : S.first.val.obj V) :
    τ₂.app V (S.f.app V s) = T.f.app V (τ₁.app V s)
  comm₂ (V : (Opens X)ᵒᵖ) (s : S.middle.val.obj V) :
    τ₃.app V (S.g.app V s) = T.g.app V (τ₂.app V s)

/-- Put a diagram on the given six sheaves in one adequate category. -/
def SectionwiseShortComplex.Hom.lift {S : SectionwiseShortComplex.{u,r,b,c,d} R}
    {T : SectionwiseShortComplex.{u,r,e,f,g} R} (h : S.Hom T) :
    S.lift.{max a e f g} ⟶ T.lift.{max a b c d} where
  τ₁ := h.τ₁.lift.{max a u r c d f g}
  τ₂ := h.τ₂.lift.{max a u r b d e g}
  τ₃ := h.τ₃.lift.{max a u r b c e f}
  comm₁₂ := by
    apply SheafOfModules.hom_ext
    ext V s
    exact congrArg ULift.up (h.comm₁ V s.down).symm
  comm₂₃ := by
    apply SheafOfModules.hom_ext
    ext V s
    exact congrArg ULift.up (h.comm₂ V s.down).symm

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

open _root_.AdvancedHomologicalAlgebra.SheafUniverseTransport

universe b c d

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Exactness of a common lift is equivalent to exactness on the original germs. -/
def sectionwiseShortExactType : Prop :=
  ∀ (X : TopCat.{u}) (R : X.Sheaf RingCat.{r}) (S : SectionwiseShortComplex.{u,r,b,c,d} R),
    S.GermLocallyShortExact ↔
      let T : ShortComplex (AmbientSheaves.{max a b c d} R) := S.lift.{a}
      T.ShortExact

end Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport
