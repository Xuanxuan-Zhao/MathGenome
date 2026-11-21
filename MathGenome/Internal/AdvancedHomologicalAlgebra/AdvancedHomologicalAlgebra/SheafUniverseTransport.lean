import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.Topology.Sheaves.LocallySurjective

/-! Transport of the sheaf preliminaries to the original ringed space. -/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe a u r m v

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section Scalars

variable {C : Type u} [Category C] {R : Cᵒᵖ ⥤ RingCat.{r}}

private def scalarUnit (M : PresheafOfModules.{m} R) :
    M ≅ (lowerScalars.{a}.obj (liftScalars.{a}.obj M)) :=
  PresheafOfModules.isoMk (fun U ↦
    ModuleCat.isoMk (Iso.refl _) (by intro r; ext s; rfl)) (by intros; rfl)

private def scalarCounit (M : PresheafOfModules.{m} (R ⋙ ringLift.{a})) :
    liftScalars.{a}.obj (lowerScalars.{a}.obj M) ≅ M :=
  PresheafOfModules.isoMk (fun U ↦
    ModuleCat.isoMk (Iso.refl _) (by intro r; ext s; rfl)) (by intros; rfl)

/-- Raising only the ring carriers is an equivalence of module presheaves. -/
def scalarEquivalence (R : Cᵒᵖ ⥤ RingCat.{r}) :
    PresheafOfModules.{m} R ≌ PresheafOfModules.{m} (R ⋙ ringLift.{a}) where
  functor := liftScalars
  inverse := lowerScalars
  unitIso := NatIso.ofComponents scalarUnit (by intros; rfl)
  counitIso := NatIso.ofComponents scalarCounit (by intros; rfl)
  functor_unitIso_comp M := by rfl

end Scalars

section Sites

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- Raising the ring carriers preserves and recovers the original sheaves. -/
def sheafScalarEquivalence (S : Sheaf J RingCat.{r}) :
    SheafOfModules.{m} S ≌ SheafOfModules.{m} (liftRingOnSite.{a} S) where
  functor := liftScalarsOnSite.{a} S
  inverse := lowerScalarsOnSite.{a} S
  unitIso := NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget S).preimageIso (scalarUnit M.val)) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget (liftRingOnSite.{a} S)).preimageIso
      (scalarCounit M.val)) (by intros; rfl)
  functor_unitIso_comp M := by rfl

variable {D : Type a} [SmallCategory D] {K : GrothendieckTopology D}

/-- Reindexing module sheaves along a continuous equivalence with continuous inverse. -/
def reindexSheafEquivalence (e : C ≌ D) (S : Sheaf K RingCat.{r})
    [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J] :
    SheafOfModules.{m} S ≌
      SheafOfModules.{m} ((e.functor.sheafPushforwardContinuous _ J K).obj S) :=
  let S' := (e.functor.sheafPushforwardContinuous _ J K).obj S
  let ψ : S ⟶ (e.inverse.sheafPushforwardContinuous _ _ _).obj S' :=
    ⟨Functor.whiskerRight (NatTrans.op e.counit) S.obj⟩
  SheafOfModules.pushforwardPushforwardEquivalence e (𝟙 S') ψ
    (by exact (Category.comp_id _).symm)
    (by
      ext1
      funext U
      change 𝟙 _ ≫ S.obj.map (e.counit.app (e.functor.obj U.unop)).op ≫
        S.obj.map (e.functor.map (e.unit.app U.unop)).op = 𝟙 _
      rw [Category.id_comp, ← Functor.map_comp, ← op_comp]
      exact (congrArg (fun f ↦ S.obj.map f.op) (e.functor_unit_comp U.unop)).trans
        (S.obj.map_id _))

end Sites

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- Reindexing an ambient sheaf along the homeomorphism is a site equivalence. -/
def siteEquivalence :
    SheafOfModules.{max a u r} (liftRingSheaf.{a} R) ≌ SheafTheory.Modules (liftedRing.{a} R) :=
  reindexSheafEquivalence (opensEquiv.{max a r u} X).equivalence (liftRingSheaf.{a} R)

/-- The functor with the specified section maps is an exact equivalence. -/
def transportEquivalence :
    AmbientSheaves.{a} R ≌ SheafTheory.Modules (liftedRing.{a} R) :=
  (sheafScalarEquivalence.{a} R).trans (siteEquivalence.{a} R)

instance transportIsEquivalence : (transport.{a} R).IsEquivalence :=
  inferInstanceAs (transportEquivalence.{a} R).functor.IsEquivalence

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

theorem ambient_equivalence : ambientEquivalence.{a,u,r} := by
  intro X R
  infer_instance

theorem ambient_exact : ambientExact.{a,u,r} := by
  intro X R
  constructor <;> infer_instance

theorem ambient_mono_injective : ambientMonoInjective.{a,u,r} := by
  intro X R M N f
  exact ⟨⟨fun h ↦ Functor.mono_of_mono_map (transport.{a} R) h, fun _ ↦ inferInstance⟩,
    (transportEquivalence.{a} R).map_injective_iff M⟩

theorem ambient_flasque : ambientFlasque.{a,u,r} := by
  intro X R M
  let e := opensEquiv.{max a r u} X
  constructor
  · intro h U V i
    obtain ⟨U, rfl⟩ := e.surjective U
    obtain ⟨V, rfl⟩ := e.surjective V
    exact h U V (e.le_iff_le.mp i.le)
  · intro h U V i
    exact h (e U) (e V) (e.equivalence.functor.map (homOfLE i))

theorem ambient_enough_injectives : ambientEnoughInjectives.{a,u,r} := by
  intro X R
  have := SheafInjectivesAndRestriction.enoughInjectivesByStalks (liftedRing.{a} R)
  exact EnoughInjectives.of_equivalence (transport.{a} R)

theorem ambient_sections : ambientSections.{a,u,r} := by
  intro X R M N f U V i s c
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem coefficient_lift_flasque : coefficientLiftFlasque.{a,u,r,m} := by
  intro X R M
  constructor
  · intro h U V i s
    obtain ⟨t, ht⟩ := h U V i (ULift.up s)
    exact ⟨t.down, congrArg ULift.down ht⟩
  · intro h U V i s
    obtain ⟨t, ht⟩ := h U V i s.down
    exact ⟨ULift.up t, congrArg ULift.up ht⟩

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (x : X)

open CategoryTheory.Functor

/-- The stalk ring comparison is induced by the equivalence of neighborhoods. -/
def stalkRingIso :
    TopCat.Presheaf.stalk (C := RingCat.{max a r u}) (X := liftedSpace.{max a r u} X) (liftedRing.{a} R).obj (X.uliftFunctorObjHomeo.{max a r u} x) ≅
      originalStalkRing.{a} R x :=
  Final.colimitIso (neighborhoodsEquiv.{max a r u} x).equivalence.functor.op
    (ringNeighborhoods.{a} R x)

/-- The additive stalk comparison is induced by the same neighborhood equivalence. -/
def stalkGroupIso (M : AmbientPresheaves.{a} R) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{max a r u}) (X := liftedSpace.{max a r u} X) ((transportPresheaf.{a} R).obj M).presheaf
      (X.uliftFunctorObjHomeo.{max a r u} x) ≅ originalStalkGroup.{a} R x M :=
  Final.colimitIso (neighborhoodsEquiv.{max a r u} x).equivalence.functor.op
    (moduleNeighborhoods.{a} R x M)

theorem stalk_ring_germ (U : Opens (liftedSpace.{max a r u} X))
    (hy : X.uliftFunctorObjHomeo.{max a r u} x ∈ U) (c : R.obj.obj (op (opensEquiv X U))) :
    (stalkRingIso.{a} R x).hom
      (TopCat.Presheaf.germ (C := RingCat.{max a r u}) (liftedRing.{a} R).obj U _ hy (sectionRingEquiv.{a} R U c)) =
        originalRingGerm.{a} R x (opensEquiv X U) hy c := by
  exact congr($(Final.ι_colimitIso_hom
    (neighborhoodsEquiv.{max a r u} x).equivalence.functor.op (ringNeighborhoods.{a} R x)
      (op ⟨U, hy⟩)) (ULift.up c))

theorem stalk_group_germ (M : AmbientPresheaves.{a} R)
    (U : Opens (liftedSpace.{max a r u} X))
    (hy : X.uliftFunctorObjHomeo.{max a r u} x ∈ U) (s : M.obj (op (opensEquiv X U))) :
    (stalkGroupIso.{a} R x M).hom
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{max a r u}) ((transportPresheaf.{a} R).obj M).presheaf U _ hy s) =
        originalModuleGerm.{a} R x M (opensEquiv X U) hy s := by
  exact congr($(Final.ι_colimitIso_hom
    (neighborhoodsEquiv.{max a r u} x).equivalence.functor.op (moduleNeighborhoods.{a} R x M)
      (op ⟨U, hy⟩)) s)

lemma stalk_group_smul (M : AmbientPresheaves.{a} R)
    (c : TopCat.Presheaf.stalk (C := RingCat.{max a r u}) (X := liftedSpace.{max a r u} X)
      (liftedRing.{a} R).obj (X.uliftFunctorObjHomeo.{max a r u} x))
    (s : TopCat.Presheaf.stalk (C := AddCommGrpCat.{max a r u}) (X := liftedSpace.{max a r u} X)
      ((transportPresheaf.{a} R).obj M).presheaf (X.uliftFunctorObjHomeo.{max a r u} x)) :
    (stalkGroupIso.{a} R x M).hom (c • s) =
      (stalkRingIso.{a} R x).hom c • (stalkGroupIso.{a} R x M).hom s := by
  let y := X.uliftFunctorObjHomeo.{max a r u} x
  let F := transportPresheaf.{a} R
  let P := (F.obj M)
  obtain ⟨U, hy, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq (liftedRing.{a} R).obj c
  obtain ⟨V, hVU, hz, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq P.presheaf s hy
  rw [← TopCat.Presheaf.germ_res_apply (liftedRing.{a} R).obj (homOfLE hVU) y hz c]
  let d := (liftedRing.{a} R).obj.map (homOfLE hVU).op c
  change (stalkGroupIso.{a} R x M).hom
      (TopCat.Presheaf.germ (liftedRing.{a} R).obj V y hz d • TopCat.Presheaf.germ P.presheaf V y hz s) =
    (stalkRingIso.{a} R x).hom (TopCat.Presheaf.germ (liftedRing.{a} R).obj V y hz d) •
      (stalkGroupIso.{a} R x M).hom (TopCat.Presheaf.germ P.presheaf V y hz s)
  rw [← P.germ_ringCat_smul]
  have e : sectionRingEquiv.{a} R V (ULift.down d) = d := rfl
  rw [← e]
  rw [stalk_group_germ, stalk_ring_germ, stalk_group_germ]
  exact original_germ_smul.{a} R x M _ hz _ s

lemma stalk_group_map {M N : AmbientPresheaves.{a} R} (f : M ⟶ N)
    (s : TopCat.Presheaf.stalk (C := AddCommGrpCat.{max a r u}) (X := liftedSpace.{max a r u} X)
      ((transportPresheaf.{a} R).obj M).presheaf (X.uliftFunctorObjHomeo.{max a r u} x)) :
    let y := X.uliftFunctorObjHomeo.{max a r u} x
    let F := transportPresheaf.{a} R
    (stalkGroupIso.{a} R x N).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{max a r u} y).map
      ((PresheafOfModules.toPresheaf _).map (F.map f)) s) =
    originalModuleStalkMap.{a} R x f ((stalkGroupIso.{a} R x M).hom s) := by
  let y := X.uliftFunctorObjHomeo.{max a r u} x
  let F := transportPresheaf.{a} R
  obtain ⟨U, hy, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (F.obj M).presheaf s
  change (stalkGroupIso.{a} R x N).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{max a r u} y).map
    ((PresheafOfModules.toPresheaf _).map (F.map f))
    (TopCat.Presheaf.germ (F.obj M).presheaf U y hy s)) =
    originalModuleStalkMap.{a} R x f
      ((stalkGroupIso.{a} R x M).hom (TopCat.Presheaf.germ (F.obj M).presheaf U y hy s))
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy
    ((PresheafOfModules.toPresheaf _).map (F.map f)) s]
  change (stalkGroupIso.{a} R x N).hom
      (TopCat.Presheaf.germ ((F.obj N).presheaf) U y hy (f.app (op (opensEquiv X U)) s)) =
    originalModuleStalkMap.{a} R x f
      ((stalkGroupIso.{a} R x M).hom (TopCat.Presheaf.germ ((F.obj M).presheaf) U y hy s))
  rw [stalk_group_germ R x N U hy, stalk_group_germ R x M U hy]
  exact (congr($(ι_colimMap (Functor.whiskerLeft (OpenNhds.inclusion x).op
    ((PresheafOfModules.toPresheaf R.obj).map f)) (op ⟨opensEquiv X U, hy⟩)) s)).symm

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

theorem stalk_comparison : stalkComparison.{a,u,r} := by
  intro X R x
  exact ⟨(stalkRingIso.{a} R x).ringCatIsoToRingEquiv,
    fun M ↦ (stalkGroupIso.{a} R x M).addCommGroupIsoToAddEquiv,
    stalk_ring_germ R x, stalk_group_germ R x, stalk_group_smul R x,
    fun _ _ ↦ stalk_group_map R x⟩

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

instance {C : Type u} [Category C] (R : Cᵒᵖ ⥤ RingCat.{r}) :
    PreservesFiniteLimits (liftCoefficients.{a,u,r,m} R) where
  preservesFiniteLimits _ :=
    { preservesLimit := fun {K} ↦
        { preserves := fun h ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits
            (K ⋙ liftCoefficients.{a,u,r,m} R) _ (fun U ↦
              isLimitOfPreserves (ModuleCat.uliftFunctor.{a,m} (R.obj U))
                (isLimitOfPreserves (PresheafOfModules.evaluation R U) h))⟩ } }

instance {C : Type u} [Category C] (R : Cᵒᵖ ⥤ RingCat.{r}) :
    PreservesFiniteColimits (liftCoefficients.{a,u,r,m} R) where
  preservesFiniteColimits _ :=
    { preservesColimit := fun {K} ↦
        { preserves := fun h ↦ ⟨PresheafOfModules.evaluationJointlyReflectsColimits
            (K ⋙ liftCoefficients.{a,u,r,m} R) _ (fun U ↦
              isColimitOfPreserves (ModuleCat.uliftFunctor.{a,m} (R.obj U))
                (isColimitOfPreserves (PresheafOfModules.evaluation R U) h))⟩ } }

theorem coefficient_lift_presheaf_exact : coefficientLiftPresheafExact.{a,u,r,m} := by
  intro X R
  constructor <;> infer_instance

theorem coefficient_lift_germ_local : coefficientLiftGermLocal.{a,u,r,m} := by
  intro X R S
  constructor <;> rintro ⟨hf, he, hg⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro U x hx s hs
      obtain ⟨V, i, hxV, hv⟩ := hf U x hx (ULift.up s) (congrArg ULift.up hs)
      exact ⟨V, i, hxV, congrArg ULift.down hv⟩
    · intro U x hx s hs
      obtain ⟨V, i, hxV, t, ht⟩ := he U x hx (ULift.up s) (congrArg ULift.up hs)
      exact ⟨V, i, hxV, t.down, congrArg ULift.down ht⟩
    · intro U x hx s
      obtain ⟨V, i, hxV, t, ht⟩ := hg U x hx (ULift.up s)
      exact ⟨V, i, hxV, t.down, congrArg ULift.down ht⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro U x hx s hs
      obtain ⟨V, i, hxV, hv⟩ := hf U x hx s.down (congrArg ULift.down hs)
      exact ⟨V, i, hxV, congrArg ULift.up hv⟩
    · intro U x hx s hs
      obtain ⟨V, i, hxV, t, ht⟩ := he U x hx s.down (congrArg ULift.down hs)
      exact ⟨V, i, hxV, ULift.up t, congrArg ULift.up ht⟩
    · intro U x hx s
      obtain ⟨V, i, hxV, t, ht⟩ := hg U x hx s.down
      exact ⟨V, i, hxV, ULift.up t, congrArg ULift.up ht⟩

theorem coefficient_lift_sheaf_germ_local : coefficientLiftSheafGermLocal.{a,u,r,m} := by
  intro X R S
  exact coefficient_lift_germ_local X R.obj (S.map (SheafOfModules.forget R))

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

/-- Morphisms between coefficient lifts are determined by the original linear maps. -/
def liftCoefficientsFullyFaithful {C : Type u} [Category C] (R : Cᵒᵖ ⥤ RingCat.{r}) :
    (liftCoefficients.{a,u,r,m} R).FullyFaithful where
  preimage {M N} f :=
    { app := fun U ↦ (ModuleCat.fullyFaithfulUliftFunctor.{r,m,a} (R.obj U)).preimage (f.app U)
      naturality := by
        intro U V i
        ext s
        exact congrArg ULift.down (PresheafOfModules.naturality_apply f i (ULift.up s)) }
  map_preimage f := by ext U s; rfl
  preimage_map f := by ext U s; rfl

/-- The same Hom comparison applies to morphisms of sheaves. -/
def liftSheafCoefficientsFullyFaithful {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) :
    (liftSheafCoefficients.{a,u,r,m} R).FullyFaithful where
  preimage f := ⟨(liftCoefficientsFullyFaithful.{a,u,r,m} R.obj).preimage f.val⟩
  map_preimage f := by ext U s; rfl
  preimage_map f := by ext U s; rfl

theorem coefficient_lift_embedding : coefficientLiftEmbedding.{a,u,r,m} := by
  intro X R
  let h := liftCoefficientsFullyFaithful.{a,u,r,m} R.obj
  let h' := liftSheafCoefficientsFullyFaithful.{a,u,r,m} R
  exact ⟨⟨h.full, h.faithful⟩, ⟨h'.full, h'.faithful⟩⟩

theorem coefficient_lift_sections : coefficientLiftSections.{a,u,r,m} := by
  intro X R M N f U V i c s
  exact ⟨rfl, rfl, rfl⟩

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Restricting before or after transport uses the same opens and same ring maps. -/
def transportOverRestriction : transportOverRestrictionType.{a,u,r} :=
  fun _ _ _ ↦ Iso.refl _

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable (U : Opens (liftedSpace.{max a r u} X))

instance overOpensEquivInverseContinuous :
    (overOpensEquiv.{a,u,r} U).inverse.IsContinuous
      ((Opens.grothendieckTopology _).over (opensEquiv X U))
      ((Opens.grothendieckTopology _).over U) := by
  let e := (opensEquiv.{max a r u} X).equivalence
  have h : (Over.post (X := e.functor.obj U) e.inverse).IsContinuous
      ((Opens.grothendieckTopology X).over (e.functor.obj U))
      ((Opens.grothendieckTopology (liftedSpace.{max a r u} X)).over _) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((opensCongrCoverPreserving (X.uliftFunctorObjHomeo.{max a r u})).overPost _)
  let G := Over.post (X := e.functor.obj U) e.inverse
  let H := Over.map (e.unitIso.inv.app U)
  have hH : H.IsContinuous
      ((Opens.grothendieckTopology (liftedSpace.{max a r u} X)).over
        (e.inverse.obj (e.functor.obj U)))
      ((Opens.grothendieckTopology (liftedSpace.{max a r u} X)).over U) := by
    dsimp [H]
    infer_instance
  change (G ⋙ H).IsContinuous _ _
  exact Functor.isContinuous_comp G H
    ((Opens.grothendieckTopology X).over (e.functor.obj U))
    ((Opens.grothendieckTopology (liftedSpace.{max a r u} X)).over
      (e.inverse.obj (e.functor.obj U)))
    ((Opens.grothendieckTopology (liftedSpace.{max a r u} X)).over U)

/-- The ambient equivalence on the restrictions to an open. -/
def transportOverEquivalence :
    SheafOfModules.{max a u r} (R.over (opensEquiv X U)) ≌
      SheafOfModules.{max a u r} ((liftedRing.{a} R).over U) :=
  (sheafScalarEquivalence.{a} (R.over (opensEquiv X U))).trans
    (reindexSheafEquivalence (overOpensEquiv.{a,u,r} U) _)

instance (U : Opens (liftedSpace.{max a r u} X)) : (transportOver.{a} R U).IsEquivalence :=
  inferInstanceAs (transportOverEquivalence.{a} R U).functor.IsEquivalence

/-- On the original over site, extension is the conjugate of extension along
the lifted open inclusion. -/
def originalExtensionFromOver :
    SheafOfModules.{max a u r} (R.over (opensEquiv X U)) ⥤ AmbientSheaves.{a} R :=
  transportOver.{a} R U ⋙ SheafTheory.extensionFromOver (liftedRing.{a} R) U ⋙
    (transportEquivalence.{a} R).inverse

/-- Conjugation and the restriction square give the actual adjunction on the original site. -/
def originalOverExtensionAdjunction :
    originalExtensionFromOver.{a} R U ⊣ SheafOfModules.overFunctor R (opensEquiv X U) := by
  let T := transportOverEquivalence.{a} R U
  let E := transportEquivalence.{a} R
  let G := SheafOfModules.overFunctor (liftedRing.{a} R) U
  let Q := SheafOfModules.overFunctor.{max a u r} R (opensEquiv X U)
  let α : Q ⋙ T.functor ≅ E.functor ⋙ G := transportOverRestriction X R U
  let β : E.functor ⋙ G ⋙ T.inverse ≅ Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight α.symm T.inverse ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft Q T.unitIso.symm ≪≫ Functor.rightUnitor _
  let A := Adjunction.ofIsRightAdjoint G
  exact ((T.toAdjunction.comp A).comp E.symm.toAdjunction).ofNatIsoRight β

instance (U : Opens (liftedSpace.{max a r u} X)) :
    PreservesFiniteLimits (originalExtensionFromOver.{a} R U) := by
  let L := SheafTheory.extensionFromOver (liftedRing.{a} R) U
  have hmono : L.PreservesMonomorphisms :=
    SheafInjectivesAndRestriction.extensionFromOverPreservesMonomorphisms _ _
  have hprod : PreservesBinaryBiproducts L :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have hadd : L.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have hhom : L.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  have hlim : PreservesFiniteLimits L := Functor.preservesFiniteLimits_of_preservesHomology _
  change PreservesFiniteLimits (transportOver.{a} R U ⋙ L ⋙ (transportEquivalence.{a} R).inverse)
  infer_instance

instance (U : Opens (liftedSpace.{max a r u} X)) :
    PreservesFiniteColimits (originalExtensionFromOver.{a} R U) := by
  unfold originalExtensionFromOver
  infer_instance

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable (U : Opens (liftedSpace.{max a r u} X))

/-- Extension from the actual open subspace using the over-site equivalence. -/
def originalOpenExtensionFunctor :
    SheafOfModules.{max a u r} ((opensEquiv X U).sheafRestrict.obj R) ⥤ AmbientSheaves.{a} R :=
  ((opensEquiv X U).sheafOfModulesEquivOver R).inverse ⋙ originalExtensionFromOver.{a} R U

/-- The extension–restriction adjunction on the actual open subspace. -/
def originalOpenExtensionAdjunction :
    originalOpenExtensionFunctor.{a} R U ⊣ originalRestriction.{a} R (opensEquiv X U) :=
  ((opensEquiv X U).sheafOfModulesEquivOver R).symm.toAdjunction.comp
    (originalOverExtensionAdjunction.{a} R U)

theorem original_restriction_exact : originalRestrictionExact.{a,u,r} := by
  intro X R V
  obtain ⟨U, rfl⟩ := (opensEquiv.{max a r u} X).surjective V
  have : (originalRestriction.{a} R (opensEquiv X U)).IsRightAdjoint :=
    (originalOpenExtensionAdjunction.{a} R U).isRightAdjoint
  have : (originalRestriction.{a} R (opensEquiv X U)).IsLeftAdjoint := by
    have h : (SheafOfModules.overFunctor.{max a u r} R (opensEquiv X U)).IsLeftAdjoint :=
      originalOverRestrictionIsLeftAdjoint.{a,u,r} R _
    change (SheafOfModules.overFunctor.{max a u r} R _ ⋙
      ((opensEquiv X U).sheafOfModulesEquivOver R).functor).IsLeftAdjoint
    infer_instance
  exact ⟨inferInstance, inferInstance⟩

theorem original_open_extension : originalOpenExtension.{a,u,r} := by
  intro X R V
  obtain ⟨U, rfl⟩ := (opensEquiv.{max a r u} X).surjective V
  let L := originalOpenExtensionFunctor.{a} R U
  let A := originalOpenExtensionAdjunction.{a} R U
  have hlim : PreservesFiniteLimits L := by
    dsimp [L, originalOpenExtensionFunctor]
    infer_instance
  have hcolim : PreservesFiniteColimits L := by
    dsimp [L, originalOpenExtensionFunctor]
    infer_instance
  exact ⟨L, ⟨A⟩, hlim, hcolim, fun M hM ↦ A.map_injective M hM⟩

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V : Opens X)

private abbrev overInitial : (Over V)ᵒᵖ := op (Over.mk (𝟙 V))

private def overInitialIsInitial : IsInitial (overInitial V) :=
  (Over.mkIdTerminal (X := V)).op _

private def overUnitDown (W : (Over V)ᵒᵖ) (c : (originalOverUnit.{a} R V).val.obj W) :
    (R.over V).obj.obj W :=
  ULift.down (show ULift.{max a u} ((R.over V).obj.obj W) from c)

/-- A map from the original unit on the over site is determined by its value
at the terminal over-open. -/
def originalOverUnitHomEquiv (M : SheafOfModules.{max a u r} (R.over V)) :
    (originalOverUnit.{a} R V ⟶ M) ≃ M.val.obj (overInitial V) where
  toFun f := f.val.app (overInitial V) (originalOverOne.{a} R V (overInitial V))
  invFun t :=
    { val :=
      { app W := ModuleCat.ofHom (X := (originalOverUnit.{a} R V).val.obj W)
          (Y := M.val.obj W)
          { toFun := fun c ↦ overUnitDown.{a} R V W c •
              (M.val.map ((overInitialIsInitial V).to W) t : M.val.obj W)
            map_add' := fun c d ↦ add_smul (overUnitDown.{a} R V W c) (overUnitDown.{a} R V W d) _
            map_smul' := fun c d ↦ mul_smul c (overUnitDown.{a} R V W d) _ }
        naturality := by
          intro W Z i
          ext c
          symm
          change M.val.map i (overUnitDown.{a} R V W c •
              (M.val.map ((overInitialIsInitial V).to W) t : M.val.obj W)) =
            ((R.over V).obj.map i (overUnitDown.{a} R V W c)) • M.val.map ((overInitialIsInitial V).to Z) t
          rw [M.val.map_smul, ← M.val.map_comp_apply]
          rw [(overInitialIsInitial V).hom_ext (((overInitialIsInitial V).to W) ≫ i)
            ((overInitialIsInitial V).to Z)] } }
  left_inv f := by
    ext W c
    let i := (overInitialIsInitial V).to W
    have h := PresheafOfModules.naturality_apply f.val i (originalOverOne.{a} R V (overInitial V))
    have hmap : (originalOverUnit.{a} R V).val.map i (originalOverOne.{a} R V (overInitial V)) =
        originalOverOne.{a} R V W := by
      change ULift.up ((R.over V).obj.map i (1 : (R.over V).obj.obj (overInitial V))) =
        ULift.up (1 : (R.over V).obj.obj W)
      rw [map_one]
    have h' : f.val.app W (originalOverOne.{a} R V W) =
        M.val.map i (f.val.app (overInitial V) (originalOverOne.{a} R V (overInitial V))) :=
      (congrArg (fun c ↦ f.val.app W c) hmap.symm).trans h
    change overUnitDown.{a} R V W c •
      (M.val.map i (f.val.app (overInitial V) (originalOverOne.{a} R V (overInitial V))) :
        M.val.obj W) = f.val.app W c
    rw [← h', ← (f.val.app W).hom.map_smul]
    congr 1
    apply ULift.ext
    exact mul_one (overUnitDown.{a} R V W c)
  right_inv t := by
    dsimp only
    rw [ModuleCat.ofHom_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    let hi := overInitialIsInitial V
    have hone : overUnitDown.{a} R V (overInitial V)
        (originalOverOne.{a} R V (overInitial V)) = 1 := rfl
    rw [hone, hi.hom_ext (hi.to (overInitial V)) (𝟙 _), one_smul]
    change M.val.presheaf.map (𝟙 _) t = t
    exact congrArg (fun f : M.val.presheaf.obj (overInitial V) ⟶
      M.val.presheaf.obj (overInitial V) ↦ f t) (M.val.presheaf.map_id _)

theorem original_over_unit_representation : originalOverUnitRepresentation.{a,u,r} := by
  intro X R V L A M
  let e := (A.homEquiv (originalOverUnit.{a} R V) M).trans
    (originalOverUnitHomEquiv.{a} R V ((SheafOfModules.overFunctor R V).obj M))
  have he (f : L.obj (originalOverUnit.{a} R V) ⟶ M) :
      e f = f.val.app (op V) (originalOverGenerator.{a} R V L A) := by
    change (A.homEquiv _ _ f).val.app (overInitial V) (originalOverOne.{a} R V (overInitial V)) = _
    rw [A.homEquiv_unit]
    rfl
  refine ⟨{ toEquiv := e, map_add' := ?_ }, he⟩
  intro f g
  change e (f + g) = e f + e g
  calc
    _ = (f + g).val.app (op V) (originalOverGenerator.{a} R V L A) := he _
    _ = f.val.app (op V) (originalOverGenerator.{a} R V L A) +
        g.val.app (op V) (originalOverGenerator.{a} R V L A) := rfl
    _ = _ := congrArg₂ (· + ·) (he f).symm (he g).symm

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The forgetful comparison uses the same section groups and maps. -/
def forgetAbelianTransport :
    forgetAbelianComparison.{a,u,r,m} :=
  fun _ _ ↦ ⟨Iso.refl _, Iso.refl _⟩

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Evaluation on any open commutes with lifting the coefficients. -/
def coefficientEvaluationIso : coefficientEvaluationComparison.{a,u,r,m} :=
  fun _ _ _ ↦ Iso.refl _

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem ringLift_locallyInjective {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ RingCat.{r}} (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J f] :
    Presheaf.IsLocallyInjective J (Functor.whiskerRight f ringLift.{a}) where
  equalizerSieve_mem x y h := by
    have h' := Presheaf.equalizerSieve_mem J f (ULift.down x) (ULift.down y)
      (congrArg ULift.down h)
    convert h' using 1
    ext V i
    exact ⟨congrArg ULift.down, congrArg ULift.up⟩

private theorem ringLift_locallySurjective {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ RingCat.{r}} (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J (Functor.whiskerRight f ringLift.{a}) where
  imageSieve_mem s := by
    have h := Presheaf.imageSieve_mem J f (ULift.down s)
    convert h using 1
    ext V i
    exact ⟨fun ⟨t, ht⟩ ↦ ⟨t.down, congrArg ULift.down ht⟩,
      fun ⟨t, ht⟩ ↦ ⟨ULift.up t, congrArg ULift.up ht⟩⟩

open CategoryTheory.Functor SheafTheory SheafInjectivesAndRestriction

private theorem W_transportInteger (X : TopCat.{u}) :
    (Opens.grothendieckTopology (liftedSpace.{max a u} X)).W
      (transportedIntegerSheafificationMap.{a} X) := by
  let F := (opensEquiv.{max a u} X).equivalence.functor
  let J := Opens.grothendieckTopology X
  let K := Opens.grothendieckTopology (liftedSpace.{max a u} X)
  let f := Functor.whiskerRight (integerSheafificationMap X) ringLift.{max a u}
  have h₁ : Presheaf.IsLocallyInjective J f := ringLift_locallyInjective J _
  have h₂ : Presheaf.IsLocallySurjective J f := ringLift_locallySurjective J _
  let g := Functor.whiskerLeft F.op f
  have h₃ : Presheaf.IsLocallyInjective K g := by
    constructor
    intro U c d h
    have hcov := Presheaf.equalizerSieve_mem J f (X := F.op.obj U) c d h
    intro y hy
    obtain ⟨V, i, hi, hyV⟩ := hcov y.down hy
    obtain ⟨W, rfl⟩ := (opensEquiv.{max a u} X).surjective V
    let j : W ⟶ _ := homOfLE ((opensEquiv.{max a u} X).le_iff_le.mp i.le)
    have hj : F.map j = i := Subsingleton.elim _ _
    refine ⟨W, j, ?_, hyV⟩
    rw [← hj] at hi
    exact hi
  have h₄ : Presheaf.IsLocallySurjective K g := by
    constructor
    intro U c
    have hcov := Presheaf.imageSieve_mem J f (U := F.op.obj (op U)) c
    intro y hy
    obtain ⟨V, i, hi, hyV⟩ := hcov y.down hy
    obtain ⟨W, rfl⟩ := (opensEquiv.{max a u} X).surjective V
    let j : W ⟶ _ := homOfLE ((opensEquiv.{max a u} X).le_iff_le.mp i.le)
    have hj : F.map j = i := Subsingleton.elim _ _
    refine ⟨W, j, ?_, hyV⟩
    rw [← hj] at hi
    exact hi
  have hg : K.W g := K.W_of_isLocallyBijective g
  unfold transportedIntegerSheafificationMap
  exact (K.W.precomp_iff _ _ (Iso.isIso_inv _)).2 hg

/-- Transport of the original constant integer ring is the constant integer ring
on the lifted space. The isomorphism extends the identification on integer constants. -/
def constantIntegerTransportIso (X : TopCat.{u}) :
    constantIntegerRingSheaf (liftedSpace.{max a u} X) ≅ liftedRing.{a} (constantIntegerRingSheaf X) := by
  let K := Opens.grothendieckTopology (liftedSpace.{max a u} X)
  let f := transportedIntegerSheafificationMap.{a} X
  let Q := liftedRing.{a} (constantIntegerRingSheaf X)
  have : IsIso ((presheafToSheaf K _).map f) := (K.W_iff _).1 (W_transportInteger.{a} X)
  let g : (presheafToSheaf K _).obj ((constantIntegerPresheaf (liftedSpace.{max a u} X))) ⟶ Q :=
    ⟨sheafifyLift K f Q.property⟩
  have hg : g = (presheafToSheaf K _).map f ≫ (sheafificationIso Q).inv := by
    apply Sheaf.hom_ext
    change sheafifyLift K f Q.property =
      sheafifyMap K f ≫ (isoSheafify K Q.property).inv
    rw [isoSheafify_inv, sheafifyMap_sheafifyLift, Category.comp_id]
  have : IsIso g := hg ▸ inferInstanceAs
    (IsIso ((presheafToSheaf K _).map f ≫ (sheafificationIso Q).inv))
  exact asIso g

theorem constantIntegerTransportIso_comp (X : TopCat.{u}) :
    integerSheafificationMap (liftedSpace.{max a u} X) ≫
      (constantIntegerTransportIso.{a} X).hom.hom = transportedIntegerSheafificationMap.{a} X := by
  let K := Opens.grothendieckTopology (liftedSpace.{max a u} X)
  let f := transportedIntegerSheafificationMap.{a} X
  let Q := liftedRing.{a} (constantIntegerRingSheaf X)
  exact toSheafify_sheafifyLift K f Q.property

private def reindexOrdinarySheaves {C : Type u} [SmallCategory C] {D : Type a} [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} (e : C ≌ D)
    [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    (A : Type m) [Category A] :
    Sheaf K A ≌ Sheaf J A where
  functor := e.functor.sheafPushforwardContinuous A J K
  inverse := e.inverse.sheafPushforwardContinuous A K J
  unitIso := NatIso.ofComponents (fun F ↦
    ObjectProperty.isoMk _ (Functor.isoWhiskerRight e.op.counitIso.symm F.obj))
  counitIso := NatIso.ofComponents (fun F ↦
    ObjectProperty.isoMk _ (Functor.isoWhiskerRight e.op.unitIso.symm F.obj))
  functor_unitIso_comp F := by
    ext1
    ext U
    change F.obj.map (e.counit.app (e.functor.obj U.unop)).op ≫
      F.obj.map (e.functor.map (e.unit.app U.unop)).op = 𝟙 _
    rw [← Functor.map_comp, ← op_comp]
    exact (congrArg (fun f ↦ F.obj.map f.op) (e.functor_unit_comp U.unop)).trans
      (F.obj.map_id _)

private def changeIsomorphicRings {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}} (e : R ≅ S) :
    SheafOfModules.{m} S ≌ SheafOfModules.{m} R := by
  let q : C ≌ C := CategoryTheory.Equivalence.refl
  have h₁ : q.functor.IsContinuous J J := by
    change (𝟭 C).IsContinuous J J
    infer_instance
  have h₂ : q.inverse.IsContinuous J J := by
    change (𝟭 C).IsContinuous J J
    infer_instance
  refine SheafOfModules.pushforwardPushforwardEquivalence q e.hom e.inv ?_ ?_
  · ext1
    funext U
    dsimp [q, CategoryTheory.Equivalence.refl]
    exact (S.obj.map_id U).trans (congr($(e.inv_hom_id).hom.app U).symm)
  · ext1
    funext U
    dsimp [q, CategoryTheory.Equivalence.refl]
    have h : e.hom.hom.app U ≫ e.inv.hom.app U = 𝟙 (R.obj.obj U) :=
      congr($(e.hom_inv_id).hom.app U)
    calc
      _ = e.hom.hom.app U ≫ e.inv.hom.app U ≫ 𝟙 _ :=
        congrArg (fun f ↦ e.hom.hom.app U ≫ e.inv.hom.app U ≫ f) (R.obj.map_id U)
      _ = _ := (congrArg (fun f ↦ e.hom.hom.app U ≫ f) (Category.comp_id _)).trans h

theorem originalIntegerForgetIsEquivalence (X : TopCat.{u}) :
    (SheafOfModules.toSheaf.{max a u} (constantIntegerRingSheaf X)).IsEquivalence := by
  let R := constantIntegerRingSheaf X
  let S := liftedRing.{a} R
  let L := constantIntegerRingSheaf (liftedSpace.{max a u} X)
  let T := transport.{a} R
  let E := changeIsomorphicRings.{max a u,max a u,max a u}
    (constantIntegerTransportIso.{a} X)
  let G := SheafOfModules.toSheaf.{max a u} L
  let P := (reindexOrdinarySheaves
    (J := Opens.grothendieckTopology (liftedSpace.{max a u} X))
    (K := Opens.grothendieckTopology X) (opensEquiv.{max a u} X).equivalence
    AddCommGrpCat.{max a u}).functor
  have h : (T ⋙ E.functor ⋙ G).IsEquivalence := by
    dsimp [T, G, L]
    infer_instance
  let i : T ⋙ E.functor ⋙ G ≅ SheafOfModules.toSheaf.{max a u} R ⋙ P := by
    have e : E.functor ⋙ G ≅ SheafOfModules.toSheaf.{max a u} S := Iso.refl _
    exact isoWhiskerLeft T e ≪≫ (forgetAbelianTransport.{a,u,u,u} X R).1
  have h' : (SheafOfModules.toSheaf.{max a u} R ⋙ P).IsEquivalence :=
    Functor.isEquivalence_of_iso i
  exact Functor.isEquivalence_of_comp_right _ P

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

def constant_integer_transport : constantIntegerTransportType.{a,u} :=
  fun X ↦ ⟨constantIntegerTransportIso.{a} X, constantIntegerTransportIso_comp.{a} X⟩

theorem original_integer_forget_equivalence : originalIntegerForgetEquivalence.{a,u} :=
  originalIntegerForgetIsEquivalence.{a,u}

theorem ambient_abelian : ambientAbelian.{a,u,r} := by
  intro X R
  exact ⟨abelianOfEquivalence (transport.{a} R)⟩

theorem original_injectives_flasque : originalInjectivesFlasque.{a,u,r} := by
  intro X R M hM
  let : Injective ((transport.{a} R).obj M) := (transportEquivalence.{a} R).map_injective_iff M |>.2 hM
  exact (ambient_flasque X R M).1
    (SheafInjectivesAndRestriction.injective_restrictions_surjective _ _)

theorem original_sections_left_exact : originalSectionsLeftExact.{a,u,r} := by
  intro X R V
  infer_instance

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section StalkExactness

variable {X : TopCat.{u}} {R : X.Presheaf RingCat.{r}}

private abbrev germDiagram (x : X) (M : PresheafOfModules.{max u m} R) :=
  (OpenNhds.inclusion x).op ⋙ M.presheaf

private abbrev moduleGerm (x : X) (M : PresheafOfModules.{max u m} R) (U : Opens X) (hx : x ∈ U) :
    M.obj (op U) →+ (originalAdditiveStalkFunctor.{u,r,m} R x).obj M :=
  (colimit.ι (germDiagram x M) (op ⟨U, hx⟩)).hom

local instance : PreservesFilteredColimitsOfSize.{u,u}
    (CategoryTheory.forget AddCommGrpCat.{max u m}) :=
  preservesFilteredColimitsOfSize_of_univLE.{max u m,max u m,u,u} _

private lemma moduleGerm_exists (x : X) (M : PresheafOfModules.{max u m} R)
    (s : (originalAdditiveStalkFunctor.{u,r,m} R x).obj M) :
    ∃ (U : Opens X) (hx : x ∈ U) (t : M.obj (op U)), moduleGerm x M U hx t = s := by
  obtain ⟨U, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat)
      (colimit.isColimit (germDiagram x M))) s
  exact ⟨U.unop.1, U.unop.2, t, ht⟩

private lemma moduleGerm_eq (x : X) (M : PresheafOfModules.{max u m} R)
    {U V : Opens X} (hx : x ∈ U) (hy : x ∈ V) (s : M.obj (op U)) (t : M.obj (op V))
    (hst : moduleGerm x M U hx s = moduleGerm x M V hy t) :
    ∃ (W : Opens X) (_ : x ∈ W) (i : W ⟶ U) (j : W ⟶ V), M.map i.op s = M.map j.op t := by
  let H := isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat)
    (colimit.isColimit (germDiagram x M))
  obtain ⟨W, i, j, e⟩ := (Types.FilteredColimit.isColimit_eq_iff _ H).1 hst
  exact ⟨W.unop.1, W.unop.2, i.unop, j.unop, e⟩

private lemma moduleGerm_res (x : X) (M : PresheafOfModules.{max u m} R)
    {U V : Opens X} (hx : x ∈ V) (i : V ⟶ U) (s : M.obj (op U)) :
    moduleGerm x M V hx (M.map i.op s) = moduleGerm x M U (i.le hx) s := by
  let j : (⟨V, hx⟩ : OpenNhds x) ⟶ ⟨U, i.le hx⟩ := i
  exact congr($(colimit.w (germDiagram x M) j.op) s)

private lemma moduleGerm_map (x : X) {M N : PresheafOfModules.{max u m} R}
    (f : M ⟶ N) (U : Opens X) (hx : x ∈ U) (s : M.obj (op U)) :
    (originalAdditiveStalkFunctor.{u,r,m} R x).map f (moduleGerm x M U hx s) =
      moduleGerm x N U hx (f.app (op U) s) := by
  exact congr($(ι_colimMap (Functor.whiskerLeft (OpenNhds.inclusion x).op
      ((PresheafOfModules.toPresheaf R).map f)) (op ⟨U, hx⟩)) s)

private lemma moduleGerm_eq_zero (x : X) (M : PresheafOfModules.{max u m} R)
    (U : Opens X) (hx : x ∈ U) (s : M.obj (op U)) :
    moduleGerm x M U hx s = 0 ↔
      ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧ M.map i.op s = 0 := by
  constructor
  · intro h
    have hs : moduleGerm x M U hx s = moduleGerm x M U hx 0 := h.trans (map_zero _).symm
    obtain ⟨V, hxV, i, j, hV⟩ := moduleGerm_eq x M hx hx s 0 hs
    exact ⟨V, i, hxV, hV.trans (map_zero _)⟩
  · rintro ⟨V, i, hxV, hs⟩
    rw [← moduleGerm_res x M hxV i s, hs, map_zero]

private lemma moduleGerm_mem_range (x : X) {M N : PresheafOfModules.{max u m} R}
    (f : M ⟶ N) (U : Opens X) (hx : x ∈ U) (s : N.obj (op U)) :
    (∃ z, (originalAdditiveStalkFunctor.{u,r,m} R x).map f z = moduleGerm x N U hx s) ↔
      ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧
        ∃ t : M.obj (op V), f.app (op V) t = N.map i.op s := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨V, hxV, t, rfl⟩ := moduleGerm_exists x M z
    rw [moduleGerm_map] at hz
    obtain ⟨W, hxW, i, j, hW⟩ := moduleGerm_eq x N hxV hx _ _ hz
    exact ⟨W, j, hxW, M.map i.op t, (PresheafOfModules.naturality_apply f i.op t).trans hW⟩
  · rintro ⟨V, i, hxV, t, ht⟩
    refine ⟨moduleGerm x M V hxV t, ?_⟩
    rw [moduleGerm_map, ht, moduleGerm_res]

theorem germ_local_short_exact_stalks : germLocalShortExactStalks.{u,r,m} := by
  intro X R S
  constructor
  · rintro ⟨hf, he, hg⟩ x
    let T := S.map (originalAdditiveStalkFunctor.{u,r,m} R x)
    change T.ShortExact
    refine ShortComplex.ShortExact.mk' (T.ab_exact_iff.2 ?_)
      ((AddCommGrpCat.mono_iff_injective T.f).2 ?_)
      ((AddCommGrpCat.epi_iff_surjective T.g).2 ?_)
    · intro z hz
      obtain ⟨U, hx, s, rfl⟩ := moduleGerm_exists x S.X₂ z
      change (originalAdditiveStalkFunctor R x).map S.g (moduleGerm x S.X₂ U hx s) = 0 at hz
      rw [moduleGerm_map] at hz
      obtain ⟨V, i, hxV, hV⟩ := (moduleGerm_eq_zero x S.X₃ U hx _).1 hz
      have hs := (PresheafOfModules.naturality_apply S.g i.op s).trans hV
      rw [← moduleGerm_res x S.X₂ hxV i s]
      exact (moduleGerm_mem_range x S.f V hxV _).2 (he V x hxV _ hs)
    · change Function.Injective T.f.hom
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨U, hx, s, rfl⟩ := moduleGerm_exists x S.X₁ z
      change (originalAdditiveStalkFunctor R x).map S.f (moduleGerm x S.X₁ U hx s) = 0 at hz
      rw [moduleGerm_map] at hz
      obtain ⟨V, i, hxV, hV⟩ := (moduleGerm_eq_zero x S.X₂ U hx _).1 hz
      have hs := (PresheafOfModules.naturality_apply S.f i.op s).trans hV
      rw [← moduleGerm_res x S.X₁ hxV i s]
      exact (moduleGerm_eq_zero x S.X₁ V hxV _).2 (hf V x hxV _ hs)
    · intro z
      obtain ⟨U, hx, s, rfl⟩ := moduleGerm_exists x S.X₃ z
      exact (moduleGerm_mem_range x S.g U hx s).2 (hg U x hx s)
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro U x hx s hs
      have hi := (AddCommGrpCat.mono_iff_injective _).1 (h x).mono_f
      apply (moduleGerm_eq_zero x S.X₁ U hx s).1
      apply hi
      change (originalAdditiveStalkFunctor R x).map S.f (moduleGerm x S.X₁ U hx s) =
        (originalAdditiveStalkFunctor R x).map S.f 0
      rw [moduleGerm_map, hs, map_zero, map_zero]
    · intro U x hx s hs
      apply (moduleGerm_mem_range x S.f U hx s).1
      apply (ShortComplex.ab_exact_iff _).1 (h x).exact
      change (originalAdditiveStalkFunctor R x).map S.g (moduleGerm x S.X₂ U hx s) = 0
      rw [moduleGerm_map, hs, map_zero]
    · intro U x hx s
      apply (moduleGerm_mem_range x S.g U hx s).1
      exact (AddCommGrpCat.epi_iff_surjective _).1 (h x).epi_g _

theorem coefficient_lift_stalk_exact : coefficientLiftStalkExact.{a,u,r,m} := by
  intro X R S
  exact (coefficient_lift_germ_local.{max a u,u,r,m} X R S).symm.trans
    (germ_local_short_exact_stalks.{u,r,max a m} X R _)

end StalkExactness

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open ZeroObject
open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private lemma shortExact_map_iff_of_faithful
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (S : ShortComplex C) (F : C ⥤ D) [F.Faithful] [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (S.map F).ShortExact ↔ S.ShortExact := by
  constructor
  · intro h
    exact .mk' ((S.exact_map_iff_of_faithful F).1 h.exact)
      (F.mono_of_mono_map h.mono_f) (F.epi_of_epi_map h.epi_g)
  · intro h
    have := h.mono_f
    have := h.epi_g
    exact h.map F

private lemma commonSheafShortExactStalks {X : TopCat.{u}} {R : SheafTheory.RingSheaf X}
    (S : ShortComplex (SheafTheory.Modules R)) :
    S.ShortExact ↔ ∀ x, (S.map (SheafTheory.stalkFunctor R x)).ShortExact := by
  have zero_of_stalks (M : SheafTheory.Modules R)
      (h : ∀ x, IsZero ((SheafTheory.stalkFunctor R x).obj M)) : IsZero M := by
    let f : M ⟶ 0 := 0
    have (x : X) : Mono ((SheafTheory.stalkFunctor R x).map f) := (h x).mono _
    have : Mono f := SheafInjectivesAndRestriction.mono_of_stalk_map_mono R f
    exact IsZero.of_mono f (isZero_zero _)
  constructor
  · intro h x
    have := h.mono_f
    have := h.epi_g
    exact h.map (SheafTheory.stalkFunctor R x)
  · intro h
    have (x : X) : Mono ((SheafTheory.stalkFunctor R x).map S.f) := (h x).mono_f
    refine .mk' ?_ (SheafInjectivesAndRestriction.mono_of_stalk_map_mono R S.f) ?_
    · rw [ShortComplex.exact_iff_isZero_homology]
      apply zero_of_stalks
      intro x
      exact (((S.map (SheafTheory.stalkFunctor R x)).exact_iff_isZero_homology).1
        (h x).exact).of_iso (S.mapHomologyIso _).symm
    · rw [Preadditive.epi_iff_isZero_cokernel]
      apply zero_of_stalks
      intro x
      exact ((Preadditive.epi_iff_isZero_cokernel _).1 (h x).epi_g).of_iso
        (PreservesCokernel.iso (SheafTheory.stalkFunctor R x) S.g)

section

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (x : X)

private def transportedStalkGroupIso :
    (transport.{a} R ⋙
      (SheafTheory.stalkFunctor (liftedRing.{a} R) (X.uliftFunctorObjHomeo.{max a r u} x) ⋙
        forget₂ (ModuleCat.{max a u r} (SheafTheory.stalkRing (liftedRing.{a} R)
          (X.uliftFunctorObjHomeo.{max a r u} x))) AddCommGrpCat.{max a u r})) ≅
      (SheafOfModules.forget R ⋙ originalAdditiveStalkFunctor.{u,r,max a r} R.obj x) :=
  NatIso.ofComponents (fun M ↦ stalkGroupIso.{a} R x M.val) (by
    intro M N f
    ext s
    exact stalk_group_map R x f.val s)

end

theorem ambient_sheaf_short_exact_stalks : ambientSheafShortExactStalks.{a,u,r} := by
  intro X R S
  let : (transport.{a} R).Additive := ⟨fun {_ _} _ _ ↦ rfl⟩
  let : Abelian (AmbientSheaves.{a} R) := abelianOfEquivalence (transport.{a} R)
  rw [← shortExact_map_iff_of_faithful S (transport.{a} R), commonSheafShortExactStalks]
  constructor
  · intro h x
    let y := X.uliftFunctorObjHomeo.{max a r u} x
    let T := SheafTheory.stalkFunctor (liftedRing.{a} R) y
    let G := forget₂ (ModuleCat.{max a u r} (SheafTheory.stalkRing (liftedRing.{a} R) y)) AddCommGrpCat.{max a u r}
    apply ShortComplex.shortExact_of_iso (S.mapNatIso (transportedStalkGroupIso.{a} R x))
    rw [ShortComplex.map_comp, ShortComplex.map_comp]
    exact (shortExact_map_iff_of_faithful _ G).2 (h y)
  · intro h y
    obtain ⟨x, rfl⟩ := (X.uliftFunctorObjHomeo.{max a r u}).surjective y
    let G := forget₂ (ModuleCat.{max a u r}
      (SheafTheory.stalkRing (liftedRing.{a} R) (X.uliftFunctorObjHomeo.{max a r u} x))) AddCommGrpCat.{max a u r}
    apply (shortExact_map_iff_of_faithful _ G).1
    rw [← ShortComplex.map_comp, ← ShortComplex.map_comp]
    exact ShortComplex.shortExact_of_iso (S.mapNatIso (transportedStalkGroupIso.{a} R x)).symm (h x)

theorem ambient_sheaf_germ_local_short_exact : ambientSheafGermLocalShortExact.{a,u,r} := by
  intro X R S
  rw [ambient_sheaf_short_exact_stalks.{a,u,r} X R S,
    germ_local_short_exact_stalks.{u,r,max a r} X R.obj]
  simp only [ShortComplex.map_comp]

universe b c d

/-- The common lift tests short exactness of the given independently sized sheaves. -/
theorem sectionwise_short_exact : sectionwiseShortExactType.{a,u,r,b,c,d} := by
  intro X R S
  change S.GermLocallyShortExact ↔ (S.lift.{a}).ShortExact
  rw [ambient_sheaf_germ_local_short_exact.{max a b c d,u,r} X R]
  constructor <;> rintro ⟨hf, he, hg⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro V x hx s hs
      obtain ⟨W, i, hxW, hW⟩ := hf V x hx s.down (congrArg ULift.down hs)
      exact ⟨W, i, hxW, congrArg ULift.up hW⟩
    · intro V x hx s hs
      obtain ⟨W, i, hxW, t, ht⟩ := he V x hx s.down (congrArg ULift.down hs)
      exact ⟨W, i, hxW, ULift.up t, congrArg ULift.up ht⟩
    · intro V x hx s
      obtain ⟨W, i, hxW, t, ht⟩ := hg V x hx s.down
      exact ⟨W, i, hxW, ULift.up t, congrArg ULift.up ht⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro V x hx s hs
      obtain ⟨W, i, hxW, hW⟩ := hf V x hx (ULift.up s) (congrArg ULift.up hs)
      exact ⟨W, i, hxW, congrArg ULift.down hW⟩
    · intro V x hx s hs
      obtain ⟨W, i, hxW, t, ht⟩ := he V x hx (ULift.up s) (congrArg ULift.up hs)
      exact ⟨W, i, hxW, t.down, congrArg ULift.down ht⟩
    · intro V x hx s
      obtain ⟨W, i, hxW, t, ht⟩ := hg V x hx (ULift.up s)
      exact ⟨W, i, hxW, t.down, congrArg ULift.down ht⟩

theorem coefficient_lift_ambient_sheaf_exact : coefficientLiftAmbientSheafExact.{a,u,r,m} := by
  intro X R
  let F := liftSheafCoefficients.{a,u,r,max m u r} R
  let : Abelian (AmbientSheaves.{m} R) := abelianOfEquivalence (transport.{m} R)
  let : Abelian (AmbientSheaves.{max a m} R) := abelianOfEquivalence (transport.{max a m} R)
  apply (F.exact_tfae.out 1 4).1
  intro S h
  rw [ambient_sheaf_germ_local_short_exact.{max a m,u,r} X R]
  exact (coefficient_lift_sheaf_germ_local.{a,u,r,max m u r} X R S).2
    ((ambient_sheaf_germ_local_short_exact.{m,u,r} X R S).1 h)

theorem coefficient_lift_original_sheaf_short_exact :
    coefficientLiftOriginalSheafShortExact.{a,u,r,m} := by
  intro X R S
  rw [ambient_sheaf_germ_local_short_exact.{max a m,u,r} X R]
  exact (coefficient_lift_sheaf_germ_local.{max a u r,u,r,m} X R S).symm

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport
open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport
open CategoryTheory.Functor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable (U : Opens (liftedSpace.{max a r u} X))

/-- Extension followed by ambient transport is extension of the transported module. -/
def transportOverExtension :
    originalExtensionFromOver.{a} R U ⋙ transport.{a} R ≅
      transportOver.{a} R U ⋙ SheafTheory.extensionFromOver (liftedRing.{a} R) U :=
  NatIso.ofComponents (fun M ↦ (transportEquivalence.{a} R).counitIso.app
    ((SheafTheory.extensionFromOver (liftedRing.{a} R) U).obj ((transportOver.{a} R U).obj M)))
    (by
      intro M N f
      exact (transportEquivalence.{a} R).counitIso.hom.naturality
        ((SheafTheory.extensionFromOver (liftedRing.{a} R) U).map ((transportOver.{a} R U).map f)))

private def originalUnitToLiftedUnitLinear (W : (Over U)ᵒᵖ) :
    ((transportOver.{a} R U).obj (originalOverUnit.{a} R (opensEquiv X U))).val.obj W ≃ₗ[
        ((liftedRing.{a} R).over U).obj.obj W]
      (SheafOfModules.unit ((liftedRing.{a} R).over U)).val.obj W where
  toFun s := ULift.up (ULift.down s)
  invFun s := ULift.up (ULift.down s)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Transport preserves the section-ring unit object, with the ring unit preserved pointwise. -/
def transportOverUnit :
    (transportOver.{a} R U).obj (originalOverUnit.{a} R (opensEquiv X U)) ≅
      SheafOfModules.unit ((liftedRing.{a} R).over U) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W ↦ LinearEquiv.toModuleIso (originalUnitToLiftedUnitLinear R U W))
      (by intros; rfl))

private lemma conjugatedUnit_comparison
    {C D P Q : Type*} [Category* C] [Category* D] [Category* P] [Category* Q]
    (E : C ≌ D) (T : P ≌ Q) {L : Q ⥤ D} {G : D ⥤ Q} {F : C ⥤ P}
    (A : L ⊣ G) (α : F ⋙ T.functor ≅ E.functor ⋙ G)
    (M : P) :
    T.functor.map ((T.unit.app M ≫ T.inverse.map (A.unit.app (T.functor.obj M))) ≫
      T.inverse.map (G.map (E.counitInv.app (L.obj (T.functor.obj M)))) ≫
      T.inverse.map (α.inv.app (E.inverse.obj (L.obj (T.functor.obj M)))) ≫
      T.unitInv.app (F.obj (E.inverse.obj (L.obj (T.functor.obj M))))) ≫
      α.hom.app (E.inverse.obj (L.obj (T.functor.obj M))) ≫
      G.map (E.counit.app (L.obj (T.functor.obj M))) = A.unit.app (T.functor.obj M) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← T.counit_app_functor]
  erw [T.counit_naturality_assoc, T.counit_naturality_assoc, T.counit_naturality_assoc,
    T.functor_unit_comp_assoc]
  rw [α.inv_hom_id_app_assoc]
  rw [← G.map_comp, E.counitIso.inv_hom_id_app]
  simp only [Functor.id_obj, G.map_id]
  exact Category.comp_id _

private lemma transportedOverUnit_eq
    (M : SheafOfModules.{max a u r} (R.over (opensEquiv X U))) :
    (transportOver.{a} R U).map ((originalOverExtensionAdjunction.{a} R U).unit.app M) ≫
      (transportOverRestriction X R U).hom.app ((originalExtensionFromOver.{a} R U).obj M) ≫
      (SheafOfModules.overFunctor (liftedRing.{a} R) U).map
        ((transportEquivalence.{a} R).counitIso.hom.app
          ((SheafTheory.extensionFromOver (liftedRing.{a} R) U).obj ((transportOver.{a} R U).obj M))) =
    (Adjunction.ofIsRightAdjoint (SheafOfModules.overFunctor (liftedRing.{a} R) U)).unit.app
      ((transportOver.{a} R U).obj M) := by
  let T := transportOverEquivalence.{a} R U
  let E := transportEquivalence.{a} R
  let G := SheafOfModules.overFunctor (liftedRing.{a} R) U
  let Q := SheafOfModules.overFunctor.{max a u r} R (opensEquiv X U)
  let α : Q ⋙ T.functor ≅ E.functor ⋙ G := transportOverRestriction X R U
  let A := Adjunction.ofIsRightAdjoint G
  let Y := G.leftAdjoint.obj (T.functor.obj M)
  change T.functor.map ((((T.toAdjunction.comp A).comp E.symm.toAdjunction).unit.app M) ≫
    (T.inverse.map (α.inv.app (E.inverse.obj Y)) ≫ T.unitInv.app (Q.obj (E.inverse.obj Y)))) ≫
    α.hom.app (E.inverse.obj Y) ≫ G.map (E.counit.app Y) = A.unit.app (T.functor.obj M)
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  change T.functor.map ((T.unit.app M ≫ T.inverse.map (A.unit.app (T.functor.obj M))) ≫
    T.inverse.map (G.map (E.counitInv.app Y)) ≫
    T.inverse.map (α.inv.app (E.inverse.obj Y)) ≫ T.unitInv.app (Q.obj (E.inverse.obj Y))) ≫
    α.hom.app (E.inverse.obj Y) ≫ G.map (E.counit.app Y) = A.unit.app (T.functor.obj M)
  exact conjugatedUnit_comparison E T A α M

/-- The comparison for the extension of the over-site unit. -/
def extendedOverUnitIso :
    (transport.{a} R).obj
      ((originalExtensionFromOver.{a} R U).obj (originalOverUnit.{a} R (opensEquiv X U))) ≅
       (SheafTheory.extensionFromOver (liftedRing.{a} R) U).obj
         (SheafOfModules.unit ((liftedRing.{a} R).over U)) :=
  (transportOverExtension.{a} R U).app _ ≪≫
    (SheafTheory.extensionFromOver (liftedRing.{a} R) U).mapIso (transportOverUnit.{a} R U)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
private lemma extendedOverUnitIso_generator :
    (extendedOverUnitIso.{a} R U).hom.val.app (op U)
      (sectionEquiv.{a} R _ U (originalOverGenerator.{a} R (opensEquiv X U) _
        (originalOverExtensionAdjunction.{a} R U))) =
      let A := Adjunction.ofIsRightAdjoint (SheafOfModules.overFunctor (liftedRing.{a} R) U)
      let W := op (Over.mk (𝟙 U))
      (A.unit.app (SheafOfModules.unit ((liftedRing.{a} R).over U))).val.app W
        (1 : ((liftedRing.{a} R).over U).obj.obj W) := by
  let W := op (Over.mk (𝟙 U))
  let P := originalOverUnit.{a} R (opensEquiv X U)
  let ν := transportOverUnit.{a} R U
  let G := SheafOfModules.overFunctor (liftedRing.{a} R) U
  let A := Adjunction.ofIsRightAdjoint G
  let s : ((transportOver.{a} R U).obj P).val.obj W :=
    originalOverOne.{a} R (opensEquiv X U) (op (Over.mk (𝟙 (opensEquiv X U))))
  have h := congrArg (fun f ↦ f.val.app W s) (transportedOverUnit_eq.{a} R U P)
  have hn := congrArg (fun f ↦ f.val.app W s) (A.unit.naturality ν.hom)
  let k := A.unit.app (SheafOfModules.unit ((liftedRing.{a} R).over U))
  have h' := congrArg (fun t ↦ (G.map (G.leftAdjoint.map ν.hom)).val.app W t) h
  change _ = k.val.app W ((ν.hom.val.app W) s)
  exact h'.trans hn.symm

/-- The actual extended unit and the extended unit from the original over site agree. -/
def originalOpenUnitOverIso :
    (originalOpenExtensionFunctor.{a} R U).obj
      (originalRestrictedUnit.{a} R (opensEquiv X U)) ≅
    (originalExtensionFromOver.{a} R U).obj (originalOverUnit.{a} R (opensEquiv X U)) :=
  (originalExtensionFromOver.{a} R U).mapIso (originalRestrictedUnitOverIso.{a} R (opensEquiv X U))

/-- The distinguished section is the adjunction unit applied to one, carried
back from the original over site to the actual extended unit. -/
def originalOpenGenerator :
    ((originalOpenExtensionFunctor.{a} R U).obj
      (originalRestrictedUnit.{a} R (opensEquiv X U))).val.obj (op (opensEquiv X U)) :=
  (originalOpenUnitOverIso.{a} R U).inv.val.app (op (opensEquiv X U))
    (originalOverGenerator.{a} R (opensEquiv X U) _ (originalOverExtensionAdjunction.{a} R U))

/-- Transport identifies the original extended open unit with HA-H00's extended unit. -/
def transportOpenUnit :
    (transport.{a} R).obj ((originalOpenExtensionFunctor.{a} R U).obj
      (originalRestrictedUnit.{a} R (opensEquiv X U))) ≅
      SheafTheory.openUnit (liftedRing.{a} R) U :=
  (transport.{a} R).mapIso (originalOpenUnitOverIso.{a} R U) ≪≫
    extendedOverUnitIso.{a} R U ≪≫ (SheafTheory.openUnitIso (liftedRing.{a} R) U).symm

theorem transport_open_unit_generator :
    (transportOpenUnit.{a} R U).hom.val.app (op U) (sectionEquiv.{a} R _ U (originalOpenGenerator.{a} R U)) =
      SheafTheory.openUnitGenerator (liftedRing.{a} R) U := by
  let i := originalOpenUnitOverIso.{a} R U
  let t := originalOverGenerator.{a} R (opensEquiv X U) _ (originalOverExtensionAdjunction.{a} R U)
  have h : i.hom.val.app (op (opensEquiv X U)) (i.inv.val.app (op (opensEquiv X U)) t) = t :=
    ModuleCat.hom_inv_apply
      ((PresheafOfModules.evaluation _ _).mapIso ((SheafOfModules.forget _).mapIso i)) t
  change _ = _
  unfold transportOpenUnit originalOpenGenerator SheafTheory.openUnitGenerator
  simp only [Iso.trans_hom, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change (SheafTheory.openUnitIso (liftedRing.{a} R) U).inv.val.app (op U)
    ((extendedOverUnitIso.{a} R U).hom.val.app (op U)
      (i.hom.val.app (op (opensEquiv X U)) (i.inv.val.app (op (opensEquiv X U)) t))) = _
  erw [h]
  exact congrArg (fun s ↦ (SheafTheory.openUnitIso (liftedRing.{a} R) U).inv.val.app (op U) s)
    (extendedOverUnitIso_generator.{a} R U)

/-- The original section identification is induced by the original adjunction
and evaluation on one in the unit sheaf. -/
def originalOpenUnitHomEquiv (M : AmbientSheaves.{a} R) :
    ((originalOpenExtensionFunctor.{a} R U).obj
      (originalRestrictedUnit.{a} R (opensEquiv X U)) ⟶ M) ≃
      M.val.obj (op (opensEquiv X U)) :=
  (Iso.homCongr (originalOpenUnitOverIso.{a} R U) (Iso.refl M)).trans
    (((originalOverExtensionAdjunction.{a} R U).homEquiv _ M).trans
      (originalOverUnitHomEquiv.{a} R (opensEquiv X U) _))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem original_open_unit_hom_eval (M : AmbientSheaves.{a} R)
    (f : (originalOpenExtensionFunctor.{a} R U).obj
      (originalRestrictedUnit.{a} R (opensEquiv X U)) ⟶ M) :
    originalOpenUnitHomEquiv.{a} R U M f =
      f.val.app (op (opensEquiv X U)) (originalOpenGenerator.{a} R U) := by
  change ((originalOverExtensionAdjunction.{a} R U).homEquiv _ M
    ((originalOpenUnitOverIso.{a} R U).inv ≫ f)).val.app (op (Over.mk (𝟙 (opensEquiv X U))))
      (originalOverOne.{a} R (opensEquiv X U) _) = _
  rw [Adjunction.homEquiv_unit]
  rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem transport_open_unit_hom (M : AmbientSheaves.{a} R)
    (f : (originalOpenExtensionFunctor.{a} R U).obj
      (originalRestrictedUnit.{a} R (opensEquiv X U)) ⟶ M) :
    sectionEquiv.{a} R M U (originalOpenUnitHomEquiv.{a} R U M f) =
      SheafInjectivesAndRestriction.homOpenUnit (liftedRing.{a} R) U ((transport.{a} R).obj M)
        ((transportOpenUnit.{a} R U).inv ≫ (transport.{a} R).map f) := by
  rw [original_open_unit_hom_eval, SheafInjectivesAndRestriction.homOpenUnit_eval]
  rw [← transport_open_unit_generator.{a} R U]
  let i := transportOpenUnit.{a} R U
  have h : i.inv.val.app (op U)
      (i.hom.val.app (op U) (sectionEquiv.{a} R _ U (originalOpenGenerator.{a} R U))) =
      sectionEquiv.{a} R _ U (originalOpenGenerator.{a} R U) :=
    ModuleCat.inv_hom_apply
      ((PresheafOfModules.evaluation _ _).mapIso ((SheafOfModules.forget _).mapIso i)) _
  change ((transport.{a} R).map f).val.app (op U)
    (sectionEquiv.{a} R _ U (originalOpenGenerator.{a} R U)) =
    ((transport.{a} R).map f).val.app (op U)
      (i.inv.val.app (op U) (i.hom.val.app (op U)
        (sectionEquiv.{a} R _ U (originalOpenGenerator.{a} R U))))
  rw [h]

instance : (transportOnOpen.{a} R U).IsEquivalence := by
  unfold transportOnOpen
  infer_instance

/-- Restriction to the actual open commutes with transport. -/
def transportRestriction :
    originalRestriction.{a} R (opensEquiv X U) ⋙ transportOnOpen.{a} R U ≅
      transport.{a} R ⋙ SheafTheory.restriction (liftedRing.{a} R) U := by
  let A := (opensEquiv X U).sheafOfModulesEquivOver.{max a u r} R
  let B := U.sheafOfModulesEquivOver.{max a u r} (liftedRing.{a} R)
  let Q := SheafOfModules.overFunctor.{max a u r} R (opensEquiv X U)
  let G := SheafOfModules.overFunctor (liftedRing.{a} R) U
  let E := transport.{a} R
  let T := transportOver.{a} R U
  change (Q ⋙ A.functor) ⋙ (A.inverse ⋙ T ⋙ B.functor) ≅ E ⋙ (G ⋙ B.functor)
  exact Functor.associator Q A.functor _ ≪≫
    isoWhiskerLeft Q (Functor.associator A.functor A.inverse (T ⋙ B.functor)).symm ≪≫
    isoWhiskerLeft Q (isoWhiskerRight A.unitIso.symm _ ≪≫ Functor.leftUnitor _) ≪≫
    (Functor.associator Q T B.functor).symm ≪≫
    isoWhiskerRight (transportOverRestriction.{a,u,r} X R U) B.functor ≪≫
    Functor.associator E G B.functor

/-- Extension from the actual open commutes with transport. -/
def transportExtension :
    originalOpenExtensionFunctor.{a} R U ⋙ transport.{a} R ≅
      transportOnOpen.{a} R U ⋙ SheafTheory.extensionByZero (liftedRing.{a} R) U := by
  let A := (opensEquiv X U).sheafOfModulesEquivOver.{max a u r} R
  let B := U.sheafOfModulesEquivOver.{max a u r} (liftedRing.{a} R)
  let T := transportOver.{a} R U
  let L := SheafTheory.extensionFromOver (liftedRing.{a} R) U
  change (A.inverse ⋙ originalExtensionFromOver.{a} R U) ⋙ transport.{a} R ≅
    (A.inverse ⋙ T ⋙ B.functor) ⋙ (B.inverse ⋙ L)
  exact Functor.associator _ _ _ ≪≫
    isoWhiskerLeft A.inverse (transportOverExtension.{a} R U) ≪≫
    isoWhiskerLeft A.inverse (isoWhiskerLeft T
      ((Functor.leftUnitor L).symm ≪≫ isoWhiskerRight B.unitIso L ≪≫
        Functor.associator B.functor B.inverse L)) ≪≫
    isoWhiskerLeft A.inverse (Functor.associator T B.functor (B.inverse ⋙ L)).symm ≪≫
    (Functor.associator A.inverse (T ⋙ B.functor) (B.inverse ⋙ L)).symm

/-- The additive original section representation has the same evaluation law. -/
def originalOpenUnitHomAddEquiv (M : AmbientSheaves.{a} R) :
    ((originalOpenExtensionFunctor.{a} R U).obj
      (originalRestrictedUnit.{a} R (opensEquiv X U)) ⟶ M) ≃+
      M.val.obj (op (opensEquiv X U)) where
  toEquiv := originalOpenUnitHomEquiv.{a} R U M
  map_add' f g := by
    change originalOpenUnitHomEquiv.{a} R U M (f + g) =
      originalOpenUnitHomEquiv.{a} R U M f + originalOpenUnitHomEquiv.{a} R U M g
    simp only [original_open_unit_hom_eval]
    rfl

section ExtensionStalks

open SheafTheory SheafInjectivesAndRestriction TopCat.Presheaf CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem locallyBijective_stalkIso {X : TopCat.{u}} {P Q : X.Presheaf AddCommGrpCat.{u}}
    (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f]
    (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  refine ⟨?_, (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks f).1
    (inferInstanceAs (Presheaf.IsLocallySurjective _ f)) x⟩
  intro s t h
  obtain ⟨U, hxU, p, rfl⟩ := P.exists_germ_eq s
  obtain ⟨V, hxV, q, rfl⟩ := P.exists_germ_eq t
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, i, j, hW⟩ := Q.germ_eq x hxU hxV _ _ h
  simp only [← f.naturality_apply] at hW
  have hcov := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X) f _ _ hW
  obtain ⟨Z, k, hk, hxZ⟩ := hcov x hxW
  change P.map k.op (P.map i.op p) = P.map k.op (P.map j.op q) at hk
  have e := congrArg (fun t ↦ P.germ Z x hxZ t) hk
  simpa only [TopCat.Presheaf.germ_res_apply] using e

variable {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X)

private def zeroExtendSheafificationStalkIso (M : SheafOfModules.{u} (R.over U)) (x : X) :
    stalk (X := X) (zeroExtend R U M.val).presheaf x ≅
      stalk (X := X) ((explicitExtension R U).obj M).val.presheaf x := by
  let P : X.Presheaf AddCommGrpCat.{u} := (zeroExtend R U M.val).presheaf
  let q := toSheafify (Opens.grothendieckTopology X) P
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map q) :=
    locallyBijective_stalkIso q x
  exact asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map q)

private def explicitToOverExtension :
    explicitExtension R U ≅ extensionFromOver R U :=
  (explicitExtensionAdjunction R U).leftAdjointUniq
    (Adjunction.ofIsRightAdjoint (SheafOfModules.overFunctor R U))

theorem overExtensionZeroOffOpen (M : SheafOfModules.{u} (R.over U)) (x : X) (hx : x ∉ U) :
    IsZero (stalk (X := X) ((extensionFromOver R U).obj M).val.presheaf x) := by
  let P : X.Presheaf AddCommGrpCat.{u} := (zeroExtend R U M.val).presheaf
  let F := PresheafOfModules.toPresheaf R.obj ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hP : IsZero (P.stalk x) := by
    apply AddCommGrpCat.isZero_iff_subsingleton.2
    apply subsingleton_of_forall_eq (0 : P.stalk x)
    intro s
    obtain ⟨W, hxW, t, rfl⟩ := P.exists_germ_eq s
    have ht : t = 0 := by
      funext h
      exact (hx (h.down hxW)).elim
    rw [ht, map_zero]
  exact hP.of_iso ((zeroExtendSheafificationStalkIso R U M x ≪≫
    F.mapIso ((SheafOfModules.forget R).mapIso ((explicitToOverExtension R U).app M))).symm)

private def zeroExtendRestrictionIso (M : SheafOfModules.{u} (R.over U)) :
    ((U.sheafOfModulesEquivOver R).functor.obj M).val.presheaf ≅
      U.isOpenEmbedding.isOpenMap.functor.op ⋙ (zeroExtend R U M.val).presheaf := by
  let η := (PresheafOfModules.toPresheaf (R.over U).obj).map (zeroExtendUnit R U M.val)
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    apply (ConcreteCategory.isIso_iff_bijective _).2
    refine ⟨fun x y h ↦ congrFun h ⟨V.unop.hom.le⟩, ?_⟩
    intro s
    refine ⟨s ⟨V.unop.hom.le⟩, ?_⟩
    funext h
    congr
  exact isoWhiskerLeft U.overEquivalence.inverse.op (asIso η)

private abbrev additiveStalkOnSite {Y : TopCat.{u}} (x : Y) :
    Y.Presheaf AddCommGrpCat.{max a u} ⥤ AddCommGrpCat.{max a u} :=
  (whiskeringLeft _ _ _).obj (OpenNhds.inclusion x).op ⋙ colim

private def restrictionStalkIso {Y : TopCat.{u}} (V : Opens Y) (x : V) :
    (whiskeringLeft _ _ _).obj V.isOpenEmbedding.isOpenMap.functor.op ⋙
        additiveStalkOnSite.{a} (Y := TopCat.of V) x ≅
      additiveStalkOnSite.{a} (Y := Y) x.1 := by
  let D := V.isOpenEmbedding.functorNhds x
  have : D.Initial := Functor.initial_of_adjunction (V.isOpenEmbedding.adjunctionNhds x)
  exact isoWhiskerLeft ((whiskeringLeft _ _ _).obj (OpenNhds.inclusion x.1).op)
    (Functor.Final.colimIso D.op)

theorem extensionFromOverUnitIsIso (M : SheafOfModules.{u} (R.over U)) :
    IsIso ((Adjunction.ofIsRightAdjoint (SheafOfModules.overFunctor R U)).unit.app M) := by
  let E := U.sheafOfModulesEquivOver.{u} R
  let S := SheafOfModules.toSheaf.{u} (U.sheafRestrict.obj R)
  let adj := explicitExtensionAdjunction R U
  let adj' := Adjunction.ofIsRightAdjoint (SheafOfModules.overFunctor R U)
  let P : X.Presheaf AddCommGrpCat.{u} := (zeroExtend R U M.val).presheaf
  let q := toSheafify (Opens.grothendieckTopology X) P
  let f := S.map (E.functor.map (adj.unit.app M))
  have hstalk (x : U) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (X := TopCat.of U) x).map f.hom) := by
    let F : X.Presheaf AddCommGrpCat.{u} ⥤ (TopCat.of U).Presheaf AddCommGrpCat.{u} :=
      (whiskeringLeft _ _ _).obj U.isOpenEmbedding.isOpenMap.functor.op
    let G := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := TopCat.of U) x
    let H := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := X) x.1
    let i : F ⋙ G ≅ H := restrictionStalkIso.{u,u} U x
    have : IsIso (H.map q) := locallyBijective_stalkIso q x.1
    have h' : IsIso ((F ⋙ G).map q) := by
      rw [← NatIso.naturality_2 i q]
      infer_instance
    change IsIso (G.map ((zeroExtendRestrictionIso R U M).hom ≫ F.map q))
    rw [G.map_comp]
    have : IsIso (G.map (F.map q)) := h'
    infer_instance
  have hη : IsIso ((E.functor ⋙ S).map (adj.unit.app M)) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (X := TopCat.of U) f
  have hη' : IsIso (adj.unit.app M) := isIso_of_reflects_iso (adj.unit.app M) (E.functor ⋙ S)
  rw [← adj.unit_leftAdjointUniq_hom_app adj' M]
  change IsIso (adj.unit.app M ≫ (SheafOfModules.overFunctor R U).map
    ((adj.leftAdjointUniq adj').hom.app M))
  infer_instance

section OriginalSupport

variable {X₀ : TopCat.{u}} (R₀ : X₀.Sheaf RingCat.{r})
variable (W : Opens (liftedSpace.{max a r u} X₀))

private theorem originalOverExtensionUnitIsIso
    (M : SheafOfModules.{max a u r} (R₀.over (opensEquiv X₀ W))) :
    IsIso ((originalOverExtensionAdjunction.{a} R₀ W).unit.app M) := by
  let T := transportOver.{a} R₀ W
  let f := (originalOverExtensionAdjunction.{a} R₀ W).unit.app M
  let α := (transportOverRestriction.{a,u,r} X₀ R₀ W).hom.app
    ((originalExtensionFromOver.{a} R₀ W).obj M)
  let G := SheafOfModules.overFunctor (liftedRing.{a} R₀) W
  let β := G.map ((transportOverExtension.{a} R₀ W).hom.app M)
  have h : IsIso (T.map f ≫ α ≫ β) := by
    change IsIso (_ ≫ _ ≫ G.map ((transportEquivalence.{a} R₀).counitIso.hom.app _))
    rw [transportedOverUnit_eq.{a,u,r}]
    exact extensionFromOverUnitIsIso _ _ _
  have : IsIso (T.map f) := IsIso.of_isIso_comp_right (T.map f) (α ≫ β)
  exact isIso_of_reflects_iso f T

/-- The original extension's adjunction unit gives the stalk isomorphism at
every point of the original open subspace. -/
def originalExtensionStalkOnOpen
    (M : SheafOfModules.{max a u r} ((opensEquiv X₀ W).sheafRestrict.obj R₀))
    (x : (opensEquiv X₀ W : Opens X₀)) :
    originalStalkGroup.{a} (X := TopCat.of (opensEquiv X₀ W : Opens X₀)) ((opensEquiv X₀ W).sheafRestrict.obj R₀) x M.val ≅
      originalStalkGroup.{a} R₀ x.1 ((originalOpenExtensionFunctor.{a} R₀ W).obj M).val := by
  let V := opensEquiv X₀ W
  let E := V.sheafOfModulesEquivOver.{max a u r} R₀
  let A := originalOpenExtensionAdjunction.{a} R₀ W
  have h₁ : IsIso ((originalOverExtensionAdjunction.{a} R₀ W).unit.app (E.inverse.obj M)) :=
    originalOverExtensionUnitIsIso R₀ W _
  have h₂ : IsIso (A.unit.app M) := by
    change IsIso ((E.symm.toAdjunction.comp (originalOverExtensionAdjunction.{a} R₀ W)).unit.app M)
    rw [Adjunction.comp_unit_app]
    change IsIso (E.counitIso.inv.app M ≫ E.functor.map
      ((originalOverExtensionAdjunction.{a} R₀ W).unit.app (E.inverse.obj M)))
    infer_instance
  let F := SheafOfModules.forget.{max a u r} (V.sheafRestrict.obj R₀) ⋙
    PresheafOfModules.toPresheaf _ ⋙ additiveStalkOnSite.{max a r} (Y := TopCat.of V) x
  let P := ((originalOpenExtensionFunctor.{a} R₀ W).obj M).val.presheaf
  exact F.mapIso (asIso (A.unit.app M)) ≪≫ (restrictionStalkIso.{max a r} V x).app P

theorem originalExtensionZeroOffOpen
    (M : SheafOfModules.{max a u r} ((opensEquiv X₀ W).sheafRestrict.obj R₀))
    (x : X₀) (hx : x ∉ opensEquiv X₀ W) :
    IsZero (originalStalkGroup.{a} R₀ x ((originalOpenExtensionFunctor.{a} R₀ W).obj M).val) := by
  let y := X₀.uliftFunctorObjHomeo.{max a r u} x
  let P := ((opensEquiv X₀ W).sheafOfModulesEquivOver R₀).inverse.obj M
  let G := SheafOfModules.toSheaf (liftedRing.{a} R₀) ⋙
    TopCat.Sheaf.forget AddCommGrpCat.{max a r u} _ ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{max a r u} y
  let e := G.mapIso ((transportOverExtension.{a} R₀ W).app P)
  have h := overExtensionZeroOffOpen (liftedRing.{a} R₀) W ((transportOver.{a} R₀ W).obj P) y hx
  exact h.of_iso ((stalkGroupIso.{a} R₀ x ((originalOpenExtensionFunctor.{a} R₀ W).obj M).val).symm ≪≫ e)

end OriginalSupport

section ExtensionGerms

set_option maxRecDepth 3000
set_option maxHeartbeats 1500000

variable {X₀ : TopCat.{u}} (R₀ : X₀.Sheaf RingCat.{r})

/-- The scalar stalk of the restricted ring is identified by the neighborhood inclusion. -/
def originalRestrictionStalkRingIso (V : Opens X₀) (x : V) :
    originalStalkRing.{a} (X := TopCat.of V) (V.sheafRestrict.obj R₀) x ≅ originalStalkRing.{a} R₀ x.1 := by
  let D := V.isOpenEmbedding.functorNhds x
  have : D.Initial := Functor.initial_of_adjunction (V.isOpenEmbedding.adjunctionNhds x)
  exact Final.colimitIso D.op (ringNeighborhoods.{a} R₀ x.1)

theorem originalRestrictionStalkRingIso_germ (V : Opens X₀) (x : V)
    (T : Opens V) (hx : x ∈ T) (c : (V.sheafRestrict.obj R₀).obj.obj (op T)) :
    (originalRestrictionStalkRingIso.{a} R₀ V x).hom
      (originalRingGerm.{a} (X := TopCat.of V) (V.sheafRestrict.obj R₀) x T hx c) =
    originalRingGerm.{a} R₀ x.1 (V.isOpenEmbedding.isOpenMap.functor.obj T) ⟨x, hx, rfl⟩ c := by
  let D := V.isOpenEmbedding.functorNhds x
  have : D.Initial := Functor.initial_of_adjunction (V.isOpenEmbedding.adjunctionNhds x)
  exact congr($(Final.ι_colimitIso_hom D.op (ringNeighborhoods.{a} R₀ x.1) (op ⟨T, hx⟩)) (ULift.up c))

variable (W : Opens (liftedSpace.{max a r u} X₀))

/-- The extension stalk isomorphism applies its adjunction unit to a section
before taking the germ on the original space. -/
theorem originalExtensionStalkOnOpen_germ
    (M : SheafOfModules.{max a u r} ((opensEquiv X₀ W).sheafRestrict.obj R₀))
    (x : (opensEquiv X₀ W : Opens X₀)) (T : Opens (opensEquiv X₀ W : Opens X₀)) (hx : x ∈ T)
    (s : M.val.obj (op T)) :
    (originalExtensionStalkOnOpen.{a} R₀ W M x).hom
      (originalModuleGerm.{a} (X := TopCat.of (opensEquiv X₀ W)) ((opensEquiv X₀ W).sheafRestrict.obj R₀) x M.val T hx s) =
    originalModuleGerm.{a} R₀ x.1 ((originalOpenExtensionFunctor.{a} R₀ W).obj M).val
      ((opensEquiv X₀ W).isOpenEmbedding.isOpenMap.functor.obj T) ⟨x, hx, rfl⟩
      (((originalOpenExtensionAdjunction.{a} R₀ W).unit.app M).val.app (op T) s) := by
  let V := opensEquiv X₀ W
  let A := originalOpenExtensionAdjunction.{a} R₀ W
  let P := ((originalOpenExtensionFunctor.{a} R₀ W).obj M).val.presheaf
  let D := V.isOpenEmbedding.functorNhds x
  have : D.Initial := Functor.initial_of_adjunction (V.isOpenEmbedding.adjunctionNhds x)
  change ((restrictionStalkIso.{max a r} V x).app P).hom
    (originalModuleStalkMap.{a} (X := TopCat.of V) (V.sheafRestrict.obj R₀) x (A.unit.app M).val
      (originalModuleGerm.{a} (X := TopCat.of V) (V.sheafRestrict.obj R₀) x M.val T hx s)) = _
  calc
    _ = ((restrictionStalkIso.{max a r} V x).app P).hom
        (originalModuleGerm.{a} (X := TopCat.of V) (V.sheafRestrict.obj R₀) x
          ((originalRestriction.{a} R₀ V).obj ((originalOpenExtensionFunctor.{a} R₀ W).obj M)).val T hx
          ((A.unit.app M).val.app (op T) s)) :=
      congrArg (fun t ↦ ((restrictionStalkIso.{max a r} V x).app P).hom t)
        (originalModuleStalkMap_germ.{a} (X := TopCat.of V) (V.sheafRestrict.obj R₀) x (A.unit.app M).val T hx s)
    _ = _ := congr($(Final.ι_colimitIso_hom D.op ((OpenNhds.inclusion x.1).op ⋙ P) (op ⟨T, hx⟩))
      ((A.unit.app M).val.app (op T) s))

/-- The stalk isomorphism on the open subspace preserves the original germ action. -/
theorem originalExtensionStalkOnOpen_smul
    (M : SheafOfModules.{max a u r} ((opensEquiv X₀ W).sheafRestrict.obj R₀))
    (x : (opensEquiv X₀ W : Opens X₀))
    (c : originalStalkRing.{a} (X := TopCat.of (opensEquiv X₀ W)) ((opensEquiv X₀ W).sheafRestrict.obj R₀) x)
    (s : originalStalkGroup.{a} (X := TopCat.of (opensEquiv X₀ W)) ((opensEquiv X₀ W).sheafRestrict.obj R₀) x M.val) :
    letI := originalStalkModule.{a} (X := TopCat.of (opensEquiv X₀ W)) ((opensEquiv X₀ W).sheafRestrict.obj R₀) x M.val
    (originalExtensionStalkOnOpen.{a} R₀ W M x).hom (c • s) =
      (originalRestrictionStalkRingIso.{a} R₀ (opensEquiv X₀ W) x).hom c •
        (originalExtensionStalkOnOpen.{a} R₀ W M x).hom s := by
  obtain ⟨T, hx, d, t, rfl, rfl⟩ :=
    originalStalkGermsJoint.{a} (X := TopCat.of (opensEquiv X₀ W)) ((opensEquiv X₀ W).sheafRestrict.obj R₀) x M c s
  let V := opensEquiv X₀ W
  let R₁ : (TopCat.of V).Sheaf RingCat.{r} := V.sheafRestrict.obj R₀
  let L := originalOpenExtensionFunctor.{a} R₀ W
  let F := originalRestriction.{a} R₀ V
  let U := V.isOpenEmbedding.isOpenMap.functor.obj T
  have hxU : x.1 ∈ U := ⟨x, hx, rfl⟩
  let h := (originalExtensionStalkOnOpen.{a} R₀ W M x).hom
  let g := originalModuleGerm.{a} R₁ x M.val T hx
  let G := originalModuleGerm.{a} R₀ x.1 (L.obj M).val U hxU
  let f : M.val.obj (op T) ⟶ (F.obj (L.obj M)).val.obj (op T) :=
    ((originalOpenExtensionAdjunction.{a} R₀ W).unit.app M).val.app (op T)
  have hs (q : M.val.obj (op T)) : h (g q) = G (f q) :=
    originalExtensionStalkOnOpen_germ.{a} R₀ W M x T hx q
  have hc :
      (originalRestrictionStalkRingIso.{a} R₀ V x).hom (originalRingGerm.{a} R₁ x T hx d) =
        originalRingGerm.{a} R₀ x.1 U hxU d :=
    originalRestrictionStalkRingIso_germ.{a} R₀ V x T hx d
  calc
    _ = h (g (d • t)) :=
      congrArg (fun z ↦ h z) (original_germ_smul.{a} R₁ x M.val T hx d t).symm
    _ = G (f (d • t)) := hs _
    _ = G (d • (f t : (F.obj (L.obj M)).val.obj (op T))) :=
      congrArg (fun q ↦ G q) (f.hom.map_smul d t)
    _ = originalRingGerm.{a} R₀ x.1 U hxU d • G (f t) :=
      original_germ_smul.{a} R₀ x.1 (L.obj M).val U hxU d (f t)
    _ = _ := congrArg₂ (· • ·) hc.symm (hs t).symm

end ExtensionGerms

end ExtensionStalks

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
/-- Transport of restriction, extension, and evaluation on the extended unit. -/
def openTransportData : openTransportDataType.{a,u,r} := by
  intro X R U
  refine
    { overExtension := originalExtensionFromOver.{a} R U
      overAdjunction := originalOverExtensionAdjunction.{a} R U
      overExtensionComparison := transportOverExtension.{a} R U
      originalOpenAdjunction := originalOpenExtensionAdjunction.{a} R U
      transportOnOpenIsEquivalence := inferInstance
      restrictionComparison := transportRestriction.{a} R U
      extensionComparison := transportExtension.{a} R U
      preservesFiniteLimits := ?_
      preservesFiniteColimits := ?_
      extensionStalkOnOpen := originalExtensionStalkOnOpen.{a} R U
      extensionStalkRing := originalRestrictionStalkRingIso.{a} R (opensEquiv X U)
      extensionStalkRingGerm := originalRestrictionStalkRingIso_germ.{a} R (opensEquiv X U)
      extensionStalkGerm := originalExtensionStalkOnOpen_germ.{a} R U
      extensionStalkSmul := originalExtensionStalkOnOpen_smul.{a} R U
      extensionZeroOffOpen := originalExtensionZeroOffOpen.{a} R U
      unitComparison := transportOpenUnit.{a} R U
      generatorComparison := transport_open_unit_generator.{a} R U
      sectionRepresentation := originalOpenUnitHomAddEquiv.{a} R U
      sectionRepresentation_apply := original_open_unit_hom_eval.{a} R U
      sectionRepresentation_transport := ?_ }
  · change PreservesFiniteLimits (_ ⋙ originalExtensionFromOver.{a} R U)
    infer_instance
  · change PreservesFiniteColimits (_ ⋙ originalExtensionFromOver.{a} R U)
    infer_instance
  · intro M f
    change sectionEquiv.{a} R M U (originalOpenUnitHomEquiv.{a} R U M f) = _
    rw [transport_open_unit_hom.{a} R U M f,
      SheafInjectivesAndRestriction.homOpenUnit_eval]

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section CoefficientStalks

variable {X : TopCat.{u}} {R : X.Presheaf RingCat.{r}}

local instance : PreservesColimitsOfSize.{u,u} AddCommGrpCat.uliftFunctor.{a,max u m} :=
  AddCommGrpCat.instPreservesColimitsOfSizeUliftFunctor

private def coefficientStalkIso (x : X) (M : PresheafOfModules.{max u m} R) :
    AddCommGrpCat.uliftFunctor.{a}.obj ((originalAdditiveStalkFunctor.{u,r,m} R x).obj M) ≅
      (originalAdditiveStalkFunctor.{u,r,max a m} R x).obj
        ((liftCoefficients.{a} R).obj M) :=
  preservesColimitIso.{u,u} AddCommGrpCat.uliftFunctor.{a,max u m} (germDiagram x M)

private lemma coefficientStalkIso_germ (x : X) (M : PresheafOfModules.{max u m} R)
    (U : Opens X) (hx : x ∈ U) (s : M.obj (op U)) :
    (coefficientStalkIso.{a} x M).hom (ULift.up (originalAdditiveGerm x M U hx s)) =
      originalAdditiveGerm x ((liftCoefficients.{a} R).obj M) U hx (ULift.up s) := by
  exact congr($(ι_preservesColimitIso_hom.{u,u} AddCommGrpCat.uliftFunctor.{a,max u m}
    (germDiagram x M) (op ⟨U, hx⟩)) (ULift.up s))

theorem coefficient_lift_stalk_comparison : coefficientLiftStalkComparison.{a,u,r,m} := by
  intro X R x
  let L := liftCoefficients.{a,u,r,max u m} R
  let F := originalAdditiveStalkFunctor.{u,r,m} R x
  let G := originalAdditiveStalkFunctor.{u,r,max a m} R x
  refine ⟨NatIso.ofComponents (coefficientStalkIso.{a} x) ?_, coefficientStalkIso_germ x⟩
  intro M N f
  ext z
  obtain ⟨z⟩ := z
  obtain ⟨U, hx, s, rfl⟩ := moduleGerm_exists x M z
  change (coefficientStalkIso.{a} x N).hom (ULift.up (F.map f (moduleGerm x M U hx s))) =
    G.map (L.map f) ((coefficientStalkIso.{a} x M).hom (ULift.up (moduleGerm x M U hx s)))
  rw [moduleGerm_map]
  change (coefficientStalkIso.{a} x N).hom (ULift.up (originalAdditiveGerm x N U hx (f.app (op U) s))) =
    G.map (L.map f) ((coefficientStalkIso.{a} x M).hom (ULift.up (originalAdditiveGerm x M U hx s)))
  rw [coefficientStalkIso_germ, coefficientStalkIso_germ]
  exact (moduleGerm_map x (L.map f) U hx (ULift.up s)).symm

end CoefficientStalks

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport
open SheafTheory (sectionRing)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem open_transport_linear : openTransportLinear.{a,u,r} := by
  intro X R U D M
  let V := opensEquiv X U
  let P := originalExtendedUnitOf.{a} R U D.overExtension
  let t := originalExtendedGeneratorOf.{a} R U D.overExtension D.overAdjunction
  let e := D.sectionRepresentation M
  let := e.module (sectionRing R V)
  have hs (c : sectionRing R V) (f : P ⟶ M) : e (c • f) = c • e f :=
    (e.linearEquiv (sectionRing R V)).map_smul c f
  refine ⟨?_, ⟨e.linearEquiv (sectionRing R V), D.sectionRepresentation_apply M⟩, ?_, ?_⟩
  · intro c f
    apply e.injective
    let d := originalExtendedUnitRightMul D c
    have h : d.val.app (op V) t = c • t :=
      (D.sectionRepresentation_apply P d).symm.trans
        ((D.sectionRepresentation P).apply_symm_apply _)
    calc
      e (c • f) = c • e f := hs c f
      _ = c • f.val.app (op V) t := congrArg (c • ·) (D.sectionRepresentation_apply M f)
      _ = f.val.app (op V) (c • t) := ((f.val.app (op V)).hom.map_smul c t).symm
      _ = f.val.app (op V) (d.val.app (op V) t) := congrArg (fun s ↦ f.val.app (op V) s) h.symm
      _ = e (d ≫ f) := (D.sectionRepresentation_apply M (d ≫ f)).symm
  · intro c f
    let H := SheafInjectivesAndRestriction.homOpenUnit (liftedRing.{a} R) U ((transport.{a} R).obj M)
    have h (f : P ⟶ M) : sectionEquiv.{a} R M U (e f) =
        H (D.unitComparison.inv ≫ (transport.{a} R).map f) :=
      (D.sectionRepresentation_transport M f).trans
        (SheafInjectivesAndRestriction.homOpenUnit_eval (liftedRing.{a} R) U _
          (D.unitComparison.inv ≫ (transport.{a} R).map f)).symm
    apply H.injective
    change H (D.unitComparison.inv ≫ (transport.{a} R).map (c • f)) =
      H (SheafTheory.openRightMul (liftedRing.{a} R) U (sectionRingEquiv.{a} R U c) ≫
        (D.unitComparison.inv ≫ (transport.{a} R).map f))
    dsimp only [H]
    rw [SheafInjectivesAndRestriction.homOpenUnit_smul]
    change H (D.unitComparison.inv ≫ (transport.{a} R).map (c • f)) =
      sectionRingEquiv.{a} R U c • H (D.unitComparison.inv ≫ (transport.{a} R).map f)
    rw [← h, ← h, hs]
    rfl
  · intro N f g
    rw [D.sectionRepresentation_apply, D.sectionRepresentation_apply]
    rfl

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open SheafTheory

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (x : X)

set_option quotPrecheck false
set_option hygiene false in
local notation "Y" => liftedSpace.{max a u r} X
set_option hygiene false in
local notation "y" => X.uliftFunctorObjHomeo.{max a u r} x

/-- Changing scalars from the original stalk ring to the lifted stalk ring. -/
def transportStalkCoefficients :
    ModuleCat.{max a u r} (originalStalkRing.{a} R x) ⥤
      ModuleCat.{max a u r} (stalkRing (liftedRing.{a} R) y) :=
  ModuleCat.restrictScalars (stalkRingIso.{a} R x).hom.hom

instance : (transportStalkCoefficients.{a} R x).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv (stalkRingIso.{a} R x).ringCatIsoToRingEquiv

/-- The comparison retains the value on every proof that the point belongs to the open. -/
def originalSkyscraperPresheafIso (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)) :
    (transportPresheaf.{a} R).obj (originalSkyscraperPresheaf.{a} R x N) ≅
      skyscraperModulePresheaf (liftedRing.{a} R) y ((transportStalkCoefficients.{a} R x).obj N) := by
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · let A := ((transportPresheaf.{a} R).obj (originalSkyscraperPresheaf.{a} R x N)).obj U
    let B := (skyscraperModulePresheaf (liftedRing.{a} R) y
      ((transportStalkCoefficients.{a} R x).obj N)).obj U
    exact @LinearEquiv.toModuleIso _ _ A B A.isAddCommGroup B.isAddCommGroup A.isModule B.isModule
      (by
      refine
        { toFun := fun s hy ↦ s ⟨hy.down⟩
          invFun := fun s hx ↦ s ⟨hx.down⟩
          left_inv := by intro s; rfl
          right_inv := by intro s; rfl
          map_add' := by intros; rfl
          map_smul' := ?_ }
      intro c s
      funext hy
      change originalRingGerm.{a} R x (opensEquiv X U.unop) hy.down c.down • (s ⟨hy.down⟩ : N) =
        (stalkRingIso.{a} R x).hom
          (TopCat.Presheaf.germ (liftedRing.{a} R).obj U.unop y hy.down c) • (s ⟨hy.down⟩ : N)
      rw [← stalk_ring_germ R x U.unop hy.down c.down]
      rfl)
  · intros
    ext s
    funext hy
    rfl

/-- The sheaf property descends from the usual skyscraper over the equivalent site. -/
theorem originalSkyscraper_isSheaf (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (originalSkyscraperPresheaf.{a} R x N).presheaf := by
  let e := (opensEquiv.{max a u r} X).equivalence
  let P := (originalSkyscraperPresheaf.{a} R x N).presheaf
  let Q := (skyscraper (liftedRing.{a} R) y ((transportStalkCoefficients.{a} R x).obj N)).val.presheaf
  let i : e.functor.op ⋙ P ≅ Q :=
    (PresheafOfModules.toPresheaf _).mapIso (originalSkyscraperPresheafIso.{a} R x N)
  have h : Presheaf.IsSheaf (Opens.grothendieckTopology Y) (e.functor.op ⋙ P) :=
    (Presheaf.isSheaf_of_iso_iff i).mpr (skyscraper (liftedRing.{a} R) y
      ((transportStalkCoefficients.{a} R x).obj N)).isSheaf
  have h' := e.inverse.op_comp_isSheaf (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) (⟨_, h⟩ : TopCat.Sheaf AddCommGrpCat.{max a u r} Y)
  exact
    ((Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerRight e.op.counitIso P)).mp h')

/-- A skyscraper module sheaf on the original space. -/
def originalSkyscraperFunctor :
    ModuleCat.{max a u r} (originalStalkRing.{a} R x) ⥤ AmbientSheaves.{a} R where
  obj N := ⟨originalSkyscraperPresheaf.{a} R x N, originalSkyscraper_isSheaf.{a} R x N⟩
  map f := ⟨(originalSkyscraperPresheafFunctor.{a} R x).map f⟩

/-- The natural comparison of skyscrapers along the site and scalar equivalences. -/
def originalSkyscraperIso :
    originalSkyscraperFunctor.{a} R x ⋙ transport.{a} R ≅
      transportStalkCoefficients.{a} R x ⋙ skyscraperFunctor (liftedRing.{a} R) y :=
  NatIso.ofComponents
    (fun N ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (originalSkyscraperPresheafIso.{a} R x N))
    (by intros; ext U s; rfl)

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

open SheafTheory

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (x : X)

set_option hygiene false in
local notation "y" => X.uliftFunctorObjHomeo.{max a u r} x

/-- The original module stalk comparison is the linearized neighborhood isomorphism. -/
def originalStalkIso :
    transport.{a} R ⋙ stalkFunctor (liftedRing.{a} R) y ≅
      originalStalkFunctor.{a} R x ⋙ transportStalkCoefficients.{a} R x := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let A := (transport.{a} R ⋙ stalkFunctor (liftedRing.{a} R) y).obj M
    let B := (originalStalkFunctor.{a} R x ⋙ transportStalkCoefficients.{a} R x).obj M
    let e : A ≃+ B := (stalkGroupIso.{a} R x M.val).addCommGroupIsoToAddEquiv
    exact @LinearEquiv.toModuleIso _ _ A B A.isAddCommGroup B.isAddCommGroup A.isModule B.isModule
      (e.toLinearEquiv (stalk_group_smul.{a} R x M.val))
  · intro M N f
    ext s
    exact stalk_group_map.{a} R x f.val s

instance originalStalkPreservesFiniteLimits :
    PreservesFiniteLimits (originalStalkFunctor.{a} R x) := by
  have : PreservesFiniteLimits (originalStalkFunctor.{a} R x ⋙ transportStalkCoefficients.{a} R x) :=
    preservesFiniteLimits_of_natIso (originalStalkIso.{a} R x)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (transportStalkCoefficients.{a} R x)

instance originalStalkPreservesFiniteColimits :
    PreservesFiniteColimits (originalStalkFunctor.{a} R x) := by
  have : PreservesFiniteColimits (originalStalkFunctor.{a} R x ⋙ transportStalkCoefficients.{a} R x) :=
    preservesFiniteColimits_of_natIso (originalStalkIso.{a} R x)
  exact preservesFiniteColimits_of_reflects_of_preserves _ (transportStalkCoefficients.{a} R x)

/-- The right adjoint map in original coordinates evaluates the given map on germs. -/
def toOriginalSkyscraper {M : AmbientSheaves.{a} R}
    {N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)}
    (f : (originalStalkFunctor.{a} R x).obj M ⟶ N) :
    M ⟶ (originalSkyscraperFunctor.{a} R x).obj N :=
  ⟨{
    app U := ModuleCat.ofHom
      { toFun := fun s h ↦ f (originalModuleGerm.{a} R x M.val U.unop h.down s)
        map_add' := by
          intro s t
          funext hx
          rw [map_add, map_add]
          rfl
        map_smul' := by
          intro c s
          funext hx
          change f (originalModuleGerm.{a} R x M.val U.unop hx.down (c • s)) =
            originalRingGerm.{a} R x U.unop hx.down c •
              f (originalModuleGerm.{a} R x M.val U.unop hx.down s)
          rw [original_germ_smul, f.hom.map_smul] }
    naturality := by
      intro U V i
      ext s
      funext hx
      change f (originalModuleGerm.{a} R x M.val V.unop hx.down (M.val.map i s)) =
        f (originalModuleGerm.{a} R x M.val U.unop (i.unop.le hx.down) s)
      rw [originalModuleGerm_restrict] }⟩

theorem toOriginalSkyscraper_transport {M : AmbientSheaves.{a} R}
    {N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)}
    (f : (originalStalkFunctor.{a} R x).obj M ⟶ N) :
    (transport.{a} R).map (toOriginalSkyscraper.{a} R x f) ≫
          (originalSkyscraperIso.{a} R x).hom.app N =
      SheafInjectivesAndRestriction.toSkyscraper (liftedRing.{a} R) y
        ((originalStalkIso.{a} R x).hom.app M ≫ (transportStalkCoefficients.{a} R x).map f) := by
  ext U s
  funext hy
  change f (originalModuleGerm.{a} R x M.val (opensEquiv X U.unop) hy.down s) =
    f ((stalkGroupIso.{a} R x M.val).hom (TopCat.Presheaf.germ
      ((transportPresheaf.{a} R).obj M.val).presheaf U.unop y hy.down s))
  rw [stalk_group_germ]

/-- The Hom comparison is a bijection by the full faithfulness of both equivalences. -/
def originalStalkSkyscraperHomEquiv (M : AmbientSheaves.{a} R)
    (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)) :
    ((originalStalkFunctor.{a} R x).obj M ⟶ N) ≃
      (M ⟶ (originalSkyscraperFunctor.{a} R x).obj N) :=
  Equiv.ofBijective (toOriginalSkyscraper.{a} R x) (by
    let F := transport.{a} R
    let H := transportStalkCoefficients.{a} R x
    let A := SheafInjectivesAndRestriction.stalkSkyscraperAdjunction (liftedRing.{a} R) y
    let i := (originalStalkIso.{a} R x).app M
    let j := (originalSkyscraperIso.{a} R x).app N
    let e := (Functor.FullyFaithful.ofFullyFaithful H).homEquiv.trans
      ((i.symm.homCongr (Iso.refl _)).trans ((A.homEquiv (F.obj M) (H.obj N)).trans
        (((Iso.refl _).homCongr j.symm).trans
          (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm)))
    have he : toOriginalSkyscraper.{a} R x = e := by
      funext f
      apply F.map_injective
      apply (cancel_mono j.hom).mp
      calc
        _ = SheafInjectivesAndRestriction.toSkyscraper (liftedRing.{a} R) y (i.hom ≫ H.map f) :=
          toOriginalSkyscraper_transport.{a} R x f
        _ = _ := by
          change _ = F.map ((Functor.FullyFaithful.ofFullyFaithful F).preimage _) ≫ j.hom
          rw [Functor.FullyFaithful.map_preimage]
          change _ = (𝟙 _ ≫ A.homEquiv _ _ (i.hom ≫ H.map f ≫ 𝟙 _) ≫ j.inv) ≫ j.hom
          simp only [Category.comp_id, Category.id_comp, Category.assoc, Iso.inv_hom_id]
          rfl
    exact he ▸ e.bijective)

lemma toOriginalSkyscraper_naturality_left {M M' : AmbientSheaves.{a} R}
    {N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)}
    (f : M' ⟶ M) (g : (originalStalkFunctor.{a} R x).obj M ⟶ N) :
    toOriginalSkyscraper.{a} R x ((originalStalkFunctor.{a} R x).map f ≫ g) =
      f ≫ toOriginalSkyscraper.{a} R x g := by
  ext U s
  funext hx
  change g (originalModuleStalkMap.{a} R x f.val
      (originalModuleGerm.{a} R x M'.val U.unop hx.down s)) =
    g (originalModuleGerm.{a} R x M.val U.unop hx.down (f.val.app U s))
  rw [originalModuleStalkMap_germ]

/-- The original stalk and skyscraper functors are adjoint by evaluation on germs. -/
def originalStalkSkyscraperAdjunction :
    originalStalkFunctor.{a} R x ⊣ originalSkyscraperFunctor.{a} R x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := originalStalkSkyscraperHomEquiv.{a} R x
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        apply (originalStalkSkyscraperHomEquiv.{a} R x M N).injective
        rw [Equiv.apply_symm_apply]
        change f ≫ g = toOriginalSkyscraper.{a} R x
          ((originalStalkFunctor.{a} R x).map f ≫ (originalStalkSkyscraperHomEquiv.{a} R x M' N).symm g)
        rw [toOriginalSkyscraper_naturality_left]
        exact congrArg (fun k ↦ f ≫ k) ((originalStalkSkyscraperHomEquiv.{a} R x M' N).apply_symm_apply g).symm
      homEquiv_naturality_right := by
        intros
        ext U s
        rfl }

/-- Changing rings and sites retains a genuinely exact stalk functor. -/
lemma originalMono_of_stalk_mono {M N : AmbientSheaves.{a} R} (f : M ⟶ N)
    [hf : ∀ x : X, Mono ((originalStalkFunctor.{a} R x).map f)] : Mono f := by
  apply (transport.{a} R).mono_of_mono_map
  have hi (z : liftedSpace.{max a u r} X) :
      Mono ((stalkFunctor (liftedRing.{a} R) z).map ((transport.{a} R).map f)) := by
    obtain ⟨x, rfl⟩ := (X.uliftFunctorObjHomeo.{max a u r}).surjective z
    let i := originalStalkIso.{a} R x
    have h := i.hom.naturality f
    let := hf x
    have hmono : Mono (i.hom.app M ≫
        (transportStalkCoefficients.{a} R x).map ((originalStalkFunctor.{a} R x).map f)) := by
      infer_instance
    let : Mono ((stalkFunctor (liftedRing.{a} R)
        (X.uliftFunctorObjHomeo.{max a u r} x)).map ((transport.{a} R).map f) ≫ i.hom.app N) := by
      exact h.symm ▸ hmono
    exact mono_of_mono _ (i.hom.app N)
  exact SheafInjectivesAndRestriction.mono_of_stalk_map_mono (liftedRing.{a} R) _

variable {R} {x}

/-- The actual original morphism into the product of skyscrapers. -/
def originalStalkProductMap {M : AmbientSheaves.{a} R}
    (N : ∀ x : X, ModuleCat.{max a u r} (originalStalkRing.{a} R x))
    (ι : ∀ x : X, (originalStalkFunctor.{a} R x).obj M ⟶ N x) :
    M ⟶ ∏ᶜ (fun x ↦ (originalSkyscraperFunctor.{a} R x).obj (N x)) :=
  Pi.lift (fun x ↦ (originalStalkSkyscraperAdjunction.{a} R x).homEquiv M (N x) (ι x))

lemma originalStalkProductMap_mono {M : AmbientSheaves.{a} R}
    (N : ∀ x : X, ModuleCat.{max a u r} (originalStalkRing.{a} R x))
    (ι : ∀ x : X, (originalStalkFunctor.{a} R x).obj M ⟶ N x) [hι : ∀ x, Mono (ι x)] :
    Mono (originalStalkProductMap.{a} N ι) := by
  refine originalMono_of_stalk_mono.{a} R (originalStalkProductMap.{a} N ι) (hf := ?_)
  intro x
  let S := originalStalkFunctor.{a} R x
  let A := originalStalkSkyscraperAdjunction.{a} R x
  let f := A.homEquiv M (N x) (ι x)
  have hf : S.map f ≫ A.counit.app (N x) = ι x :=
    (A.homEquiv_counit M (N x) f).symm.trans ((A.homEquiv M (N x)).symm_apply_apply (ι x))
  let : Mono (S.map f) := mono_of_mono_fac hf
  let P := fun x ↦ (originalSkyscraperFunctor.{a} R x).obj (N x)
  have hπ : originalStalkProductMap.{a} N ι ≫ Pi.π P x = f :=
    limit.lift_π _ (Discrete.mk x)
  have h : S.map (originalStalkProductMap.{a} N ι) ≫ S.map (Pi.π P x) = S.map f :=
    (S.map_comp _ _).symm.trans (congrArg S.map hπ)
  exact mono_of_mono_fac h

lemma originalSkyscraperProduct_injective
    (N : ∀ x : X, ModuleCat.{max a u r} (originalStalkRing.{a} R x))
    (hN : ∀ x : X, Injective (N x)) :
    Injective (∏ᶜ (fun x ↦ (originalSkyscraperFunctor.{a} R x).obj (N x))) := by
  let (x : X) := (originalStalkSkyscraperAdjunction.{a} R x).map_injective _ (hN x)
  infer_instance

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

/-- All original and common stalk comparisons use the same germ coordinates. -/
def originalStalkSkyscraperData (R : X.Sheaf RingCat.{r}) (x : X) :
    OriginalStalkSkyscraperComparison.{a} R x where
  ring := (stalkRingIso.{a} R x).ringCatIsoToRingEquiv
  ringGerm := stalk_ring_germ R x
  stalkIso := originalStalkIso.{a} R x
  stalkGerm := fun M ↦ stalk_group_germ R x M.val
  exactLimits := inferInstance
  exactColimits := inferInstance
  skyscraper := originalSkyscraperFunctor.{a} R x
  skyscraperPresheafIso := Iso.refl _
  skyscraperIso := originalSkyscraperIso.{a} R x
  skyscraperIsoOnSection := by intros; rfl
  sections := by
    intro N U
    constructor
    · intro hx
      refine ⟨
        { toFun := fun s ↦ s ⟨hx⟩
          invFun := fun n _ ↦ n
          left_inv := by intro s; rfl
          right_inv := by intro s; rfl
          map_add' := by intros; rfl }, ?_⟩
      intros
      rfl
    · intro hx
      let _ : IsEmpty (PLift (x ∈ U)) := ⟨fun h ↦ hx h.down⟩
      exact inferInstanceAs (Subsingleton (PLift (x ∈ U) → N))
  adjunction := originalStalkSkyscraperAdjunction.{a} R x
  adjunctionOnGerm := by
    intro M N f U hx s
    change ((originalStalkSkyscraperAdjunction.{a} R x).homEquiv M N f).val.app (op U) s ⟨hx⟩ = _
    simp only [originalStalkSkyscraperAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    rfl

theorem original_stalk_skyscraper_comparison : originalStalkSkyscraperComparison.{a,u,r} :=
  fun _ R x ↦ ⟨originalStalkSkyscraperData.{a} R x⟩

theorem original_stalk_product_embedding : originalStalkProductEmbedding.{a,u,r} := by
  intro X R
  refine ⟨originalStalkSkyscraperData.{a} R, ?_⟩
  intro M N i
  let F := transport.{a} R
  let P := fun x ↦ (originalSkyscraperFunctor.{a} R x).obj (N x)
  let Q := fun x ↦ (skyscraperFunctor (liftedRing.{a} R)
    (X.uliftFunctorObjHomeo.{max a u r} x)).obj ((transportStalkCoefficients.{a} R x).obj (N x))
  let p (x : X) : F.obj (P x) ≅ Q x := (originalSkyscraperIso.{a} R x).app (N x)
  let e := PreservesProduct.iso F P ≪≫ Pi.mapIso p
  have hπ (x : X) : e.hom ≫ Pi.π Q x = F.map (Pi.π P x) ≫ (p x).hom := by
    rw [Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π, ← Category.assoc,
      PreservesProduct.iso_hom, piComparison_comp_π]
  refine ⟨fun hm ↦ originalStalkProductMap_mono.{a} N i (hι := hm),
    originalSkyscraperProduct_injective.{a} N, e, hπ, ?_⟩
  let f := originalStalkProductMap.{a} N i
  change F.map f ≫ e.hom = Pi.lift (fun x ↦
    F.map ((originalStalkSkyscraperAdjunction.{a} R x).homEquiv M (N x) (i x)) ≫ (p x).hom)
  apply Pi.hom_ext
  intro x
  rw [Category.assoc, hπ, ← Category.assoc, ← F.map_comp]
  rw [limit.lift_π]
  congr 2
  exact limit.lift_π _ (Discrete.mk x)

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

theorem coefficient_lift_cochains : coefficientLiftCochains.{a,u,r,m,v} := by
  constructor <;> intros <;> exact ⟨rfl, rfl⟩

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport
open SheafTheory (openUnitGenerator)
open SheafInjectivesAndRestriction (openUnitMap openUnitMap_generator homOpenUnit homOpenUnit_eval)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem open_unit_map_transport : openUnitMapTransport.{a,u,r} := by
  intro X R U W D E i
  let M := originalExtendedUnitOf.{a} R W E.overExtension
  let t := originalExtendedGeneratorOf.{a} R W E.overExtension E.overAdjunction
  let f := originalOpenUnitMap D E i
  let T := transport.{a} R
  let j := ((opensEquiv.{max a u r} X).equivalence.functor.map i).op
  have he : (D.sectionRepresentation M) f = M.val.map j t :=
    (D.sectionRepresentation M).apply_symm_apply _
  have h :
      (D.unitComparison.inv ≫ T.map f ≫ E.unitComparison.hom).val.app (op U)
        (openUnitGenerator (liftedRing.{a} R) U) =
      (SheafTheory.openUnit (liftedRing.{a} R) W).val.map i.op
        (openUnitGenerator (liftedRing.{a} R) W) := by
    rw [← Category.assoc]
    change E.unitComparison.hom.val.app (op U)
      ((D.unitComparison.inv ≫ T.map f).val.app (op U) (openUnitGenerator (liftedRing.{a} R) U)) = _
    rw [← D.sectionRepresentation_transport M f, he]
    change E.unitComparison.hom.val.app (op U)
      ((T.obj M).val.map i.op (sectionEquiv.{a} R M W t)) = _
    rw [PresheafOfModules.naturality_apply, E.generatorComparison]
  have hmap : D.unitComparison.inv ≫ T.map f ≫ E.unitComparison.hom =
      openUnitMap (liftedRing.{a} R) i := by
    apply (homOpenUnit (liftedRing.{a} R) U _).injective
    rw [homOpenUnit_eval, homOpenUnit_eval, openUnitMap_generator]
    exact h
  refine ⟨?_, h⟩
  have hm : T.map f =
      D.unitComparison.hom ≫ openUnitMap (liftedRing.{a} R) i ≫ E.unitComparison.inv := by
    rw [← hmap]
    simp
  exact T.mono_of_mono_map (hm ▸ inferInstanceAs
    (Mono (D.unitComparison.hom ≫ openUnitMap (liftedRing.{a} R) i ≫ E.unitComparison.inv)))

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

theorem constant_integer_transport_exists : constantIntegerTransportExists.{a,u} :=
  ⟨constant_integer_transport⟩

theorem open_transport_exists : openTransportExists.{a,u,r} :=
  ⟨openTransportData⟩

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section ReindexPresheaves

variable {C : Type u} [Category C] {D : Type a} [Category D]
variable (e : C ≌ D) (S : Dᵒᵖ ⥤ RingCat.{r})

private abbrev reindexPresheafInverse :
    PresheafOfModules.{m} (e.functor.op ⋙ S) ⥤ PresheafOfModules.{m} S :=
  PresheafOfModules.pushforward (Functor.whiskerRight (NatTrans.op e.counit) S)

private def reindexPresheafUnit (M : PresheafOfModules.{m} S) :
    M ≅ (reindexPresheafInverse e S).obj ((PresheafOfModules.pushforward₀ e.functor S).obj M) := by
  refine PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk
    (M.presheaf.mapIso (e.counitIso.app U.unop).op) ?_) ?_
  · intro c
    ext s
    exact (M.map_smul (e.counit.app U.unop).op c s).symm
  · intro U V i
    ext s
    change (M.presheaf.map i ≫ M.presheaf.map (e.counit.app V.unop).op) s =
      (M.presheaf.map (e.counit.app U.unop).op ≫
        M.presheaf.map (e.functor.map (e.inverse.map i.unop)).op) s
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congr($(congrArg M.presheaf.map ((NatTrans.op e.counit).naturality i)) s)

private def reindexPresheafCounit (M : PresheafOfModules.{m} (e.functor.op ⋙ S)) :
    (PresheafOfModules.pushforward₀ e.functor S).obj ((reindexPresheafInverse e S).obj M) ≅ M := by
  refine PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk
    (M.presheaf.mapIso (e.unitIso.app U.unop).op) ?_) ?_
  · intro c
    ext s
    let p := (e.counit.app (e.functor.obj U.unop)).op
    let q := (e.functor.map (e.unit.app U.unop)).op
    let t : M.obj (op (e.inverse.obj (e.functor.obj U.unop))) := s
    let d : (e.functor.op ⋙ S).obj (op (e.inverse.obj (e.functor.obj U.unop))) := S.map p c
    change c • M.map (e.unit.app U.unop).op t =
      M.map (e.unit.app U.unop).op (d • t)
    have h : S.map q (S.map p c) = c := by
      change (S.map p ≫ S.map q) c = c
      dsimp only [p, q]
      rw [← Functor.map_comp, ← op_comp]
      have h := congrArg (fun f ↦ S.map f.op) (e.functor_unit_comp U.unop)
      exact congr($(h.trans (S.map_id _)) c)
    rw [M.map_smul, show (e.functor.op ⋙ S).map (e.unit.app U.unop).op d = c from h]
  · intro U V i
    ext s
    change (M.presheaf.map (e.inverse.map (e.functor.map i.unop)).op ≫
        M.presheaf.map (e.unit.app V.unop).op) s =
      (M.presheaf.map (e.unit.app U.unop).op ≫ M.presheaf.map i) s
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congr($(congrArg M.presheaf.map ((NatTrans.op e.unit).naturality i)) s)

/-- Precomposition along a site equivalence reindexes presheaves of modules. -/
def reindexPresheafEquivalence :
    PresheafOfModules.{m} S ≌ PresheafOfModules.{m} (e.functor.op ⋙ S) where
  functor := PresheafOfModules.pushforward₀ e.functor S
  inverse := reindexPresheafInverse e S
  unitIso := NatIso.ofComponents (reindexPresheafUnit e S) (by
    intro M N f
    ext U s
    exact (PresheafOfModules.naturality_apply f (e.counit.app U.unop).op s).symm)
  counitIso := NatIso.ofComponents (reindexPresheafCounit e S) (by
    intro M N f
    ext U s
    exact (PresheafOfModules.naturality_apply f (e.unit.app U.unop).op s).symm)
  functor_unitIso_comp M := by
    ext U s
    change (M.presheaf.map (e.counit.app (e.functor.obj U.unop)).op ≫
      M.presheaf.map (e.functor.map (e.unit.app U.unop)).op) s = s
    rw [← Functor.map_comp, ← op_comp]
    have h := congrArg (fun f ↦ M.presheaf.map f.op) (e.functor_unit_comp U.unop)
    exact congr($(h.trans (M.presheaf.map_id _)) s)

end ReindexPresheaves

end AdvancedHomologicalAlgebra.SheafUniverseTransport

namespace AdvancedHomologicalAlgebra.SheafUniverseTransport

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Scalar lift followed by site reindexing for ambient presheaves. -/
def ambientPresheafTransportEquivalence {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) :
    AmbientPresheaves.{a} R ≌ PresheafOfModules.{max a u r} (liftedRing.{a} R).obj :=
  (scalarEquivalence.{max a u} R.obj).trans
    (reindexPresheafEquivalence (opensEquiv.{max a r u} X).equivalence (liftRingSheaf.{a} R).obj)

instance ambientPresheafTransportIsEquivalence {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) :
    (transportPresheaf.{a} R).IsEquivalence :=
  inferInstanceAs (ambientPresheafTransportEquivalence.{a} R).functor.IsEquivalence

theorem ambient_presheaf_exact_equivalence : ambientPresheafExactEquivalence.{a,u,r} := by
  intro X R
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem ambient_presheaf_sections : ambientPresheafSections.{a,u,r} := by
  intro X R M N f U V i s c
  exact ⟨rfl, rfl, rfl, rfl⟩

end AdvancedHomologicalAlgebra.SheafUniverseTransport
