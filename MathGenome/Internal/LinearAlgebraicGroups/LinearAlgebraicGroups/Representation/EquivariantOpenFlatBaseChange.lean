import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantOpenFlatBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PrimeSpectrum
open scoped TensorProduct ModuleCat.Algebra

universe u

namespace LinearAlgebraicGroups.Representation.EquivariantOpenFlatBaseChange

open Scheme.Modules
open Specs.EquivariantOpenFlatBaseChange
open EquivariantAffineModules (affineSectionBaseChange)

noncomputable section

open private pullback_spec_isQuasicoherent
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

private abbrev OpenLocal {X Y : Scheme.{u}} (j : Y ⟶ X) (F : X.Modules) : Prop :=
  (Scheme.Modules.pushforward j).essImage F

set_option backward.isDefEq.respectTransparency false in
private theorem openLocal_iff_restrict {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F : X.Modules) :
    OpenLocal j F ↔ ∀ W : X.Opens, IsIso (F.presheaf.map (homOfLE (j.image_preimage_le W)).op) := by
  change (Scheme.Modules.pushforward j).essImage F ↔ _
  rw [← (restrictAdjunction j).isIso_unit_app_iff_mem_essImage, Hom.isIso_iff_isIso_app]
  simp only [restrictAdjunction_unit_app_app]

set_option backward.isDefEq.respectTransparency false in
private def pushforwardIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Scheme.Modules.pushforward f ≅ restrictFunctor (inv f) := by
  let P := Scheme.Modules.pushforward f
  let Q := Scheme.Modules.pushforward (inv f)
  let A := restrictFunctor (inv f)
  exact (Functor.rightUnitor P).symm ≪≫
    Functor.isoWhiskerLeft P (restrictFunctorAdjCounitIso (inv f)).symm ≪≫
    (Functor.associator P Q A).symm ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.pushforwardComp f (inv f) ≪≫
        Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id f) ≪≫ Scheme.Modules.pushforwardId X) A ≪≫
    Functor.leftUnitor A

set_option backward.isDefEq.respectTransparency false in
private theorem affine_open_pushforward {R : CommRingCat.{u}} {Y : Scheme.{u}} [IsAffine Y]
    (j : Y ⟶ Spec R) (H : Y.Modules) [H.IsQuasicoherent] :
    ((Scheme.Modules.pushforward j).obj H).IsQuasicoherent := by
  let e := Y.isoSpec
  let f := e.inv ≫ j
  obtain ⟨φ, hφ⟩ := Spec.map_surjective f
  let K := (Scheme.Modules.pushforward e.hom).obj H
  let E : Scheme.Modules.pushforward e.hom ≅ restrictFunctor e.inv :=
    pushforwardIsoRestrict e.hom
  let : K.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of Γ(Y, ⊤))).ringCatSheaf).prop_of_iso
      (E.app H).symm (isQuasicoherent_restrictFunctor e.inv H)
  have : ((Scheme.Modules.pushforward (Spec.map φ)).obj K).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr (isIso_fromTildeΓ_pushforward φ K)
  let D : (Scheme.Modules.pushforward (Spec.map φ)).obj K ≅
      (Scheme.Modules.pushforward j).obj H :=
    (Scheme.Modules.pushforwardCongr hφ).app K ≪≫
      (Scheme.Modules.pushforwardComp e.hom f).app H ≪≫
      (Scheme.Modules.pushforwardCongr (by simp [f, e])).app H
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso D ‹_›

private theorem localized_map_bijective {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N]
    (r : R) (f : M →ₗ[R] N) [IsLocalizedModule.Away r f]
    (h : Function.Bijective (fun s : M => r • s)) : Function.Bijective f := by
  have hpow (n : ℕ) : Function.Bijective (fun s : M => r ^ n • s) := by
    induction n with
    | zero => simpa only [pow_zero, one_smul] using
        (show Function.Bijective (fun x : M => x) from Function.bijective_id)
    | succ n ih =>
      rw [pow_succ]
      change Function.Bijective (fun x : M => (r ^ n * r) • x)
      simp only [mul_smul]
      exact ih.comp h
  constructor
  · intro x y xy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_iff_exists (.powers r) f).mp xy
    exact (hpow n).injective hn
  · intro y
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (.powers r) f y
    obtain ⟨z, hz⟩ := (hpow n).surjective x
    refine ⟨z, ?_⟩
    apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f (⟨r ^ n, n, rfl⟩ : Submonoid.powers r))).injective
    change r ^ n • f z = r ^ n • y
    change r ^ n • z = x at hz
    rw [← f.map_smul, hz]
    exact hx.symm

set_option backward.isDefEq.respectTransparency false in
private theorem extendScalars_bijective_smul {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) (r : R)
    (h : Function.Bijective (fun x : M => r • x)) :
    Function.Bijective (fun x : (ModuleCat.extendScalars φ).obj M => φ r • x) := by
  let E := ModuleCat.extendScalars φ
  let f : M ⟶ M := ModuleCat.ofHom (algebraMap R (Module.End R M) r)
  let : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr h
  let N : ModuleCat.{u} S := E.obj M
  let b : N ⟶ N := ModuleCat.ofHom (X := N) (Y := N)
    (algebraMap S (Module.End S N) (φ r))
  have hb : E.map f = b := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    rw [ModuleCat.ExtendScalars.map_tmul]
    let := φ.toAlgebra
    change (1 : S) ⊗ₜ[R] (r • m) = (φ r * 1) ⊗ₜ[R] m
    rw [← TensorProduct.smul_tmul, Algebra.smul_def]
    rfl
  let : IsIso b := hb ▸ inferInstanceAs (IsIso (E.map f))
  exact ConcreteCategory.bijective_of_isIso b

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_top_bijective_smul {R : CommRingCat.{u}} (F : (Spec R).Modules)
    (r : R) (h : Function.Bijective (F.presheaf.map (basicOpen r).leTop.op)) :
    Function.Bijective (fun x : Γ(F, ⊤) => r • x) := by
  let D := F.presheaf.map (basicOpen r).leTop.op
  let e : Γ(F, ⊤) ≃ Γ(F, basicOpen r) := Equiv.ofBijective D h
  have hr : Function.Bijective (fun x : Γ(F, basicOpen r) => r • x) :=
    (Module.End.isUnit_iff _).mp (F.isUnit_algebraMap_end_of_le_basicOpen r le_rfl)
  have he : e ∘ (fun x : Γ(F, ⊤) => r • x) = (fun x : Γ(F, basicOpen r) => r • x) ∘ e := by
    funext x
    exact F.map_smul_Spec (basicOpen r).leTop.op r x
  have hb := hr.comp e.bijective
  rw [← he] at hb
  exact (e.bijective.of_comp_iff' _).mp hb

private abbrev principalOpen {R : CommRingCat.{u}} (r : R) : (Spec R).Opens :=
  basicOpen r

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
private theorem local_of_bijective_smul {S : CommRingCat.{u}} (s : S)
    (G : (Spec S).Modules) [G.IsQuasicoherent]
    (hs : Function.Bijective (fun x : Γ(G, ⊤) => s • x)) :
    OpenLocal (principalOpen s).ι G := by
  let D : (Spec S).Opens := basicOpen s
  let η := (restrictAdjunction D.ι).unit.app G
  let F := (Scheme.Modules.pushforward D.ι).obj (G.restrict D.ι)
  let : IsAffine D.toScheme := IsAffineOpen.Spec_basicOpen s
  let : F.IsQuasicoherent := affine_open_pushforward D.ι (G.restrict D.ι)
  have hη : IsIso ((modulesSpecToSheaf.map η).hom.app (op ⊤)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    let u : D.ι ''ᵁ (D.ι ⁻¹ᵁ (⊤ : (Spec S).Opens)) = basicOpen s := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_top_eq]
    let f := ((modulesSpecToSheaf.obj G).obj.map (basicOpen s).leTop.op).hom
    let : IsLocalizedModule.Away s f :=
      (isIso_fromTildeΓ_iff_isLocalizing G).mp inferInstance s
    have hf := localized_map_bijective s f hs
    have h₁ : Function.Bijective (G.presheaf.map (basicOpen s).leTop.op) := hf
    let e := G.presheaf.map (eqToHom u).op
    have h₂ := ConcreteCategory.bijective_of_isIso e
    have h₃ : ⇑((modulesSpecToSheaf.map η).hom.app (op ⊤)) =
        (fun x : Γ(G, ⊤) => e (G.presheaf.map (basicOpen s).leTop.op x)) := by
      -- The component is ordinary restriction to the principal open.
      funext x
      change G.presheaf.map (homOfLE (D.ι.image_preimage_le ⊤)).op x = _
      rw [← G.presheaf.map_comp_apply]
      rfl
    rw [h₃]
    exact h₂.comp h₁
  have hη' : IsIso (modulesSpecToSheaf.map η) :=
    isLocalizing_of_isIso_app_top hη
      ((isIso_fromTildeΓ_iff_isLocalizing G).mp inferInstance)
      ((isIso_fromTildeΓ_iff_isLocalizing F).mp inferInstance)
  let : IsIso η := isIso_of_reflects_iso η modulesSpecToSheaf
  exact (restrictAdjunction D.ι).mem_essImage_of_unit_isIso G

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
private theorem pullback_principal_open_local {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R)
    (H : (principalOpen r).toScheme.Modules) [H.IsQuasicoherent] :
    OpenLocal (principalOpen (φ r)).ι
      ((Scheme.Modules.pullback (Spec.map φ)).obj
        ((Scheme.Modules.pushforward (principalOpen r).ι).obj H)) := by
  let D : (Spec R).Opens := basicOpen r
  let F := (Scheme.Modules.pushforward D.ι).obj H
  let G := (Scheme.Modules.pullback (Spec.map φ)).obj F
  let : IsAffine D.toScheme := IsAffineOpen.Spec_basicOpen r
  let : F.IsQuasicoherent := affine_open_pushforward D.ι H
  let : G.IsQuasicoherent := pullback_spec_isQuasicoherent φ F
  have hF : OpenLocal D.ι F := ⟨H, ⟨Iso.refl _⟩⟩
  have htop := (openLocal_iff_restrict D.ι F).mp hF ⊤
  let e : D.ι ''ᵁ (D.ι ⁻¹ᵁ (⊤ : (Spec R).Opens)) = basicOpen r := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_top_eq]
  have hbij : Function.Bijective (F.presheaf.map (basicOpen r).leTop.op) := by
    let t := F.presheaf.map (eqToHom e.symm).op
    have h := (ConcreteCategory.bijective_of_isIso t).comp
      (by
        let := htop
        exact ConcreteCategory.bijective_of_isIso (F.presheaf.map (homOfLE (D.ι.image_preimage_le ⊤)).op))
    rw [← ConcreteCategory.coe_comp, ← F.presheaf.map_comp] at h
    exact h
  have hr := restrict_top_bijective_smul F r hbij
  obtain ⟨a, _⟩ := affineSectionBaseChange φ F
  have hφ := extendScalars_bijective_smul φ.hom ((moduleSpecΓFunctor (R := R)).obj F) r hr
  apply local_of_bijective_smul (φ r) G
  have he : a.toLinearEquiv ∘ (fun x : Γ(G, ⊤) => φ r • x) =
      (fun x => φ r • x) ∘ a.toLinearEquiv := by
    funext x
    exact a.toLinearEquiv.map_smul (φ r) x
  have hb := hφ.comp a.toLinearEquiv.bijective
  rw [← he] at hb
  exact (a.toLinearEquiv.bijective.of_comp_iff' _).mp hb

section OpenSections

variable {X : Scheme.{u}}

/-- Intersect each open with a fixed open. -/
private def meetOpen (W : X.Opens) : X.Opens ⥤ X.Opens where
  obj U := W ⊓ U
  map f := homOfLE (inf_le_inf_left _ (leOfHom f))

private def meetOpenIso (W : X.Opens) :
    Opens.map W.ι.base ⋙ W.ι.opensFunctor ≅ meetOpen W :=
  NatIso.ofComponents
    (fun U => eqToIso (by simp [meetOpen, Scheme.Hom.image_preimage_eq_opensRange_inf]))
    (fun _ => Subsingleton.elim _ _)

private instance (W : X.Opens) :
    (meetOpen W).IsContinuous (Opens.grothendieckTopology X) (Opens.grothendieckTopology X) :=
  letI := Functor.isContinuous_comp (Opens.map W.ι.base) W.ι.opensFunctor
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology W.toScheme)
    (Opens.grothendieckTopology X)
  Functor.isContinuous_of_iso (meetOpenIso W) _ _

set_option backward.isDefEq.respectTransparency false in
private def meetOpenRingMap (W : X.Opens) :
    X.ringCatSheaf ⟶ ((meetOpen W).sheafPushforwardContinuous _ _ _).obj X.ringCatSheaf where
  hom.app U := X.ringCatSheaf.obj.map (homOfLE (inf_le_right (a := W) (b := U.unop))).op
  hom.naturality U V f := by
    change X.ringCatSheaf.obj.map _ ≫ X.ringCatSheaf.obj.map _ =
      X.ringCatSheaf.obj.map _ ≫ X.ringCatSheaf.obj.map _
    simp only [← Functor.map_comp]
    rfl

/-- The sheaf on the ambient space whose sections over U are sections over W ∩ U. -/
private def openSections (W : X.Opens) : X.Modules ⥤ X.Modules :=
  SheafOfModules.pushforward (meetOpenRingMap W)

set_option backward.isDefEq.respectTransparency false in
private def openSectionsMap {W W' : X.Opens} (f : W ⟶ W') :
    openSections W' ⟶ openSections W :=
  let α : meetOpen W ⟶ meetOpen W' :=
    { app U := homOfLE (inf_le_inf_right U (leOfHom f)) }
  SheafOfModules.pushforwardNatTrans (meetOpenRingMap W') α ≫
    (SheafOfModules.pushforwardCongr (by
      ext U x
      change ((X.ringCatSheaf.obj.map _ ≫ X.ringCatSheaf.obj.map _) x) = X.ringCatSheaf.obj.map _ x
      rw [← Functor.map_comp]
      rfl)).hom

set_option backward.isDefEq.respectTransparency false in
private def openSectionsFunctor (F : X.Modules) : X.Opensᵒᵖ ⥤ X.Modules where
  obj W := (openSections W.unop).obj F
  map f := (openSectionsMap f.unop).app F
  map_id W := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    change F.presheaf.map (homOfLE (show W.unop ⊓ U ≤ W.unop ⊓ U from le_rfl)).op x = x
    simp
  map_comp {A B C} f g := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    change F.presheaf.map (homOfLE (show C.unop ⊓ U ≤ A.unop ⊓ U from
      inf_le_inf_right U (leOfHom (f ≫ g).unop))).op x =
      F.presheaf.map (homOfLE (inf_le_inf_right U (leOfHom g.unop))).op
        (F.presheaf.map (homOfLE (inf_le_inf_right U (leOfHom f.unop))).op x)
    rw [← F.presheaf.map_comp_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
private def openSectionsIso (W : X.Opens) :
    restrictFunctor W.ι ⋙ Scheme.Modules.pushforward W.ι ≅ openSections W := by
  let A : W.toScheme.ringCatSheaf ⟶
      (W.ι.opensFunctor.sheafPushforwardContinuous _ _ _).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight
      ({ app U := (W.ι.appIso U.unop).inv } :
        W.toScheme.presheaf ⟶ W.ι.opensFunctor.op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat)⟩
  letI := Functor.isContinuous_comp (Opens.map W.ι.base) W.ι.opensFunctor
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology W.toScheme)
    (Opens.grothendieckTopology X)
  refine SheafOfModules.pushforwardComp W.ι.toRingCatSheafHom A ≪≫ ?_
  refine SheafOfModules.pushforwardCongr₂ _ (meetOpenIso W).symm ?_
  ext U x
  let e : W ⊓ U.unop = W.ι ''ᵁ W.ι ⁻¹ᵁ U.unop :=
    ((W.ι.image_preimage_eq_opensRange_inf U.unop).trans (by simp)).symm
  let t := X.presheaf.map (eqToHom e).op
  have h : W.ι.app U.unop ≫ (W.ι.appIso (W.ι ⁻¹ᵁ U.unop)).inv ≫ t =
      X.presheaf.map (homOfLE (inf_le_right : W ⊓ U.unop ≤ U.unop)).op := by
    rw [W.ι.app_appIso_inv_assoc]
    dsimp only [t]
    rw [← X.presheaf.map_comp]
    rfl
  exact congrArg (fun f : Γ(X, U.unop) ⟶ Γ(X, W ⊓ U.unop) => f x) h

set_option backward.isDefEq.respectTransparency false in
private theorem openSectionsCover_isLimit {I : Type u} (F : X.Modules) (U : I → X.Opens) :
    Nonempty (IsLimit ((openSectionsFunctor F).mapCone (Pairwise.cocone U).op)) := by
  let c := (openSectionsFunctor F).mapCone (Pairwise.cocone U).op
  refine ⟨isLimitOfReflects (SheafOfModules.forget _) ?_⟩
  apply PresheafOfModules.evaluationJointlyReflectsLimits _
  intro W
  refine isLimitOfReflects (forget₂ (ModuleCat _) Ab) ?_
  let U' (i : I) := U i ⊓ W.unop
  have hi : (⨆ i, U i) ⊓ W.unop = ⨆ i, U' i := iSup_inf_eq U W.unop
  let e : (Pairwise.diagram U).op ⋙ openSectionsFunctor F ⋙
      SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj W ⋙ forget₂ (ModuleCat _) Ab ≅
        (Pairwise.diagram U').op ⋙ F.presheaf :=
    NatIso.ofComponents (fun j => F.presheaf.mapIso ((eqToIso (show
        (Pairwise.diagram U').obj j.unop = (Pairwise.diagram U).obj j.unop ⊓ W.unop by
          cases j.unop <;> simp [U', inf_left_comm, inf_comm])).op)) (by
        intro a b f
        change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
        simp only [← Functor.map_comp]
        rfl)
  let i : (Cone.postcompose e.hom).obj
      ((forget₂ (ModuleCat _) Ab).mapCone
        ((PresheafOfModules.evaluation X.ringCatSheaf.obj W).mapCone
          ((SheafOfModules.forget X.ringCatSheaf).mapCone c))) ≅
      F.presheaf.mapCone (Pairwise.cocone U').op :=
    Cone.ext (F.presheaf.mapIso ((eqToIso hi.symm).op)) (by
      intro j
      change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
      simp only [← Functor.map_comp]
      rfl)
  exact (IsLimit.postcomposeHomEquiv e _)
    (IsLimit.ofIsoLimit (F.isSheaf.isSheafPairwiseIntersections U').some i.symm)

end OpenSections

set_option backward.isDefEq.respectTransparency false in
private theorem openLocal_of_range_le {X Y Z : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion j] (h : f.opensRange ≤ j.opensRange)
    {F : X.Modules} (hF : OpenLocal f F) : OpenLocal j F := by
  obtain ⟨H, ⟨e⟩⟩ := hF
  let q := IsOpenImmersion.lift j f h
  let K := (Scheme.Modules.pushforward q).obj H
  refine ⟨K, ⟨(Scheme.Modules.pushforwardComp q j).app H ≪≫
    (Scheme.Modules.pushforwardCongr (IsOpenImmersion.lift_fac j f h)).app H ≪≫ e⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_pushforward_inside {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (H : Y.Modules) [H.IsQuasicoherent]
    (W : X.Opens) (h : W ≤ j.opensRange) :
    (((Scheme.Modules.pushforward j).obj H).restrict W.ι).IsQuasicoherent := by
  have h' : Set.range W.ι ⊆ Set.range j := by
    rw [Scheme.Opens.range_ι]
    exact h
  let q := IsOpenImmersion.lift j W.ι h'
  have hq : q ≫ j = W.ι := IsOpenImmersion.lift_fac _ _ _
  let : IsOpenImmersion (q ≫ j) := hq.symm ▸ inferInstanceAs (IsOpenImmersion W.ι)
  let : IsOpenImmersion q := IsOpenImmersion.of_comp q j
  let F := (Scheme.Modules.pushforward j).obj H
  let e : F.restrict W.ι ≅ H.restrict q :=
    ((restrictFunctorCongr hq).app F).symm ≪≫
      (restrictFunctorComp q j).app F ≪≫
      (restrictFunctor q).mapIso ((restrictFunctorAdjCounitIso j).app H)
  exact (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso e.symm
    (isQuasicoherent_restrictFunctor q H)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
private theorem pullback_affine_open_local {R S : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : R ⟶ S) (j : Y ⟶ Spec R) [IsOpenImmersion j] [QuasiCompact j]
    [Flat (Spec.map φ)] (H : Y.Modules) [H.IsQuasicoherent] :
    OpenLocal ((Spec.map φ) ⁻¹ᵁ j.opensRange).ι
      ((Scheme.Modules.pullback (Spec.map φ)).obj ((Scheme.Modules.pushforward j).obj H)) := by
  classical
  let g := Spec.map φ
  let P := Scheme.Modules.pullback g
  let F := (Scheme.Modules.pushforward j).obj H
  let l := (g ⁻¹ᵁ j.opensRange).ι
  have hcompact : IsCompact (Set.range j) := by
    let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace j
    exact isCompact_range j.continuous
  obtain ⟨I, hI, a, ha⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact
    j.opensRange hcompact
  let : Fintype I := Fintype.ofFinite I
  let V (i : I) := basicOpen (a i)
  let c := (openSectionsFunctor F).mapCone (Pairwise.cocone V).op
  have hc : IsLimit c := (openSectionsCover_isLimit F V).some
  let : P.PreservesHomology := LinearAlgebraicGroups.FlatCohomology.flatPullbackExact g
  let : PreservesFiniteLimits P := Functor.preservesFiniteLimits_of_preservesHomology P
  have hprincipal (b : R) (hb : basicOpen b ≤ j.opensRange) :
      OpenLocal l (P.obj ((openSections (basicOpen b)).obj F)) := by
    let D : (Spec R).Opens := basicOpen b
    let K := F.restrict D.ι
    let : K.IsQuasicoherent := restrict_pushforward_inside j H D hb
    have h₁ := pullback_principal_open_local φ b K
    have h₂ : (principalOpen (φ b)).ι.opensRange ≤ l.opensRange := by
      simp only [Scheme.Opens.opensRange_ι, l, ← SpecMap_preimage_basicOpen]
      exact (Opens.map g.base).monotone hb
    exact (Scheme.Modules.pushforward l).essImage.prop_of_iso
      (P.mapIso ((openSectionsIso D).app F))
      (openLocal_of_range_le _ _ h₂ h₁)
  let d := ((Pairwise.diagram V).op ⋙ openSectionsFunctor F) ⋙ P
  have hd' (i : (Pairwise I)ᵒᵖ) : OpenLocal l (d.obj i) := by
    cases i using Opposite.rec
    rename_i i
    cases i with
    | single i => exact hprincipal (a i) (ha ▸ le_iSup V i)
    | pair i i' =>
      have he : principalOpen (a i * a i') = V i ⊓ V i' := basicOpen_mul _ _
      have hle : V i ⊓ V i' ≤ j.opensRange :=
        inf_le_left.trans (ha ▸ le_iSup V i)
      have hb : principalOpen (a i * a i') ≤ j.opensRange :=
        Eq.mpr (congrArg (fun W : (Spec R).Opens => W ≤ j.opensRange) he) hle
      have h := hprincipal (a i * a i') hb
      have h' : OpenLocal l (P.obj ((openSections (V i ⊓ V i')).obj F)) :=
        congrArg (fun W : (Spec R).Opens => OpenLocal l (P.obj ((openSections W).obj F))) he ▸ h
      exact h'
  have hlim : OpenLocal l (P.obj ((openSections (⨆ i, V i)).obj F)) :=
    (Scheme.Modules.pushforward l).essImage.prop_of_isLimit (isLimitOfPreserves P hc) hd'
  have hF : OpenLocal j.opensRange.ι F :=
    openLocal_of_range_le j j.opensRange.ι (by simp) ⟨H, ⟨Iso.refl _⟩⟩
  let : IsIso ((restrictAdjunction j.opensRange.ι).unit.app F) :=
    (restrictAdjunction j.opensRange.ι).isIso_unit_app_iff_mem_essImage.mpr hF
  let e : (openSections (⨆ i, V i)).obj F ≅ F :=
    eqToIso (congrArg (fun W : (Spec R).Opens => (openSections W).obj F) ha.symm) ≪≫
      ((openSectionsIso j.opensRange).app F).symm ≪≫
      (asIso ((restrictAdjunction j.opensRange.ι).unit.app F :
        F ⟶ (Scheme.Modules.pushforward j.opensRange.ι).obj (F.restrict j.opensRange.ι))).symm
  exact (Scheme.Modules.pushforward l).essImage.prop_of_iso (P.mapIso e) hlim

set_option backward.isDefEq.respectTransparency false in
/-- Restrict a sheaf direct image to an open by first restricting the sheaf
to the inverse image open and then taking the restricted direct image. -/
private def restrictPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward (f ∣_ U) := by
  let V := f ⁻¹ᵁ U
  let F := U.ι.opensFunctor ⋙ (Opens.map f.base)
  let G := Opens.map (f ∣_ U).base ⋙ V.ι.opensFunctor
  let e : F ≅ G := NatIso.ofComponents
    (fun W => eqToIso (image_morphismRestrict_preimage f U W).symm)
    (fun _ => Subsingleton.elim _ _)
  let α : U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ Y.presheaf :=
    { app W := (U.ι.appIso W.unop).inv }
  let β : V.toScheme.presheaf ⟶ V.ι.opensFunctor.op ⋙ X.presheaf :=
    { app W := (V.ι.appIso W.unop).inv }
  let φ : U.toScheme.ringCatSheaf ⟶
      (U.ι.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  let ψ : V.toScheme.ringCatSheaf ⟶
      (V.ι.opensFunctor.sheafPushforwardContinuous _ _ _).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight β (forget₂ CommRingCat RingCat)⟩
  refine SheafOfModules.pushforwardComp φ f.toRingCatSheafHom ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp (f ∣_ U).toRingCatSheafHom ψ).symm
  refine SheafOfModules.pushforwardCongr₂ _ e.symm ?_
  ext W x
  change X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op
      (f.app (U.ι ''ᵁ W.unop) ((U.ι.appIso W.unop).inv x)) =
    (V.ι.appIso ((f ∣_ U) ⁻¹ᵁ W.unop)).inv ((f ∣_ U).app W.unop x)
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  rw [morphismRestrict_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_affine_open_local_of_isAffine {X U Y : Scheme.{u}}
    [IsAffine X] [IsAffine U] (g : U ⟶ X) [Flat g]
    (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (H : Y.Modules) [H.IsQuasicoherent] :
    OpenLocal (g ⁻¹ᵁ j.opensRange).ι
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward j).obj H)) := by
  let e := X.isoSpec
  let d := U.isoSpec
  let j' := j ≫ e.hom
  let g' := d.inv ≫ g ≫ e.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g'
  let : Flat (Spec.map φ) := hφ.symm ▸ inferInstanceAs (Flat g')
  have h := pullback_affine_open_local φ j' H
  rw [hφ] at h
  let V := g' ⁻¹ᵁ j'.opensRange
  let G := (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward j).obj H)
  let eF : (Scheme.Modules.pushforward e.hom).obj ((Scheme.Modules.pushforward j).obj H) ≅
      (Scheme.Modules.pushforward j').obj H := (Scheme.Modules.pushforwardComp j e.hom).app H
  let c : (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pushforward j').obj H) ≅
      (Scheme.Modules.pushforward j).obj H :=
    (Scheme.Modules.pullback e.hom).mapIso eF.symm ≪≫
      asIso ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).counit.app _)
  let b : (Scheme.Modules.pullback g').obj ((Scheme.Modules.pushforward j').obj H) ≅
      (Scheme.Modules.pullback d.inv).obj G :=
    ((Scheme.Modules.pullbackComp (d.inv ≫ g) e.hom).app _).symm ≪≫
      (Scheme.Modules.pullback (d.inv ≫ g)).mapIso c ≪≫
      ((Scheme.Modules.pullbackComp d.inv g).app _).symm
  obtain ⟨K, ⟨k⟩⟩ := h
  let Giso : (Scheme.Modules.pushforward d.inv).obj ((Scheme.Modules.pullback d.inv).obj G) ≅ G :=
    ((pushforwardIsoRestrict d.inv).app _ ≪≫ (restrictFunctorIsoPullback (inv d.inv)).app _) ≪≫
      (Scheme.Modules.pullbackComp (inv d.inv) d.inv).app G ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id d.inv)).app G ≪≫
      (Scheme.Modules.pullbackId U).app G
  apply openLocal_of_range_le (V.ι ≫ d.inv) (g ⁻¹ᵁ j.opensRange).ι
  · have he : e.hom ⁻¹ᵁ e.hom ''ᵁ j.opensRange = j.opensRange := e.hom.preimage_image_eq _
    have hV : V = d.inv ⁻¹ᵁ (g ⁻¹ᵁ j.opensRange) := by
      simp only [V, g', j', Scheme.Hom.opensRange_comp, Scheme.Hom.comp_preimage, he]
    rw [Scheme.Opens.opensRange_ι, Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, hV]
    exact d.inv.image_preimage_le _
  · exact ⟨K, ⟨((Scheme.Modules.pushforwardComp V.ι d.inv).app K).symm ≪≫
      (Scheme.Modules.pushforward d.inv).mapIso (k ≪≫ b) ≪≫ Giso⟩⟩

private theorem opensRange_of_isPullback {X Y U V : Scheme.{u}}
    {j : Y ⟶ X} {l : V ⟶ U} {g : U ⟶ X} {r : V ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion l] (h : IsPullback l r g j) :
    l.opensRange = g ⁻¹ᵁ j.opensRange := by
  apply Opens.ext
  change Set.range l = (g ⁻¹ᵁ j.opensRange : Set U)
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ]
  exact IsOpenImmersion.range_pullbackFst j g

set_option backward.isDefEq.respectTransparency false in
private theorem openLocal_on_basis {U : Scheme.{u}} {J : Type u} (W : J → U.Opens)
    (hW : Opens.IsBasis (Set.range W)) (L : U.Opens) (G : U.Modules)
    (hG : ∀ i, OpenLocal ((W i).ι ⁻¹ᵁ L).ι (G.restrict (W i).ι)) :
    OpenLocal L.ι G := by
  let η := (restrictAdjunction L.ι).unit.app G
  let T := SheafOfModules.toSheaf U.ringCatSheaf
  have hη : IsIso (T.map η) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hW
    intro i
    let A := W i
    let B := A.ι ⁻¹ᵁ L
    let G' := G.restrict A.ι
    have htop := (openLocal_iff_restrict B.ι G').mp (hG i) ⊤
    let D : A.toScheme.Opens := B.ι ''ᵁ B.ι ⁻¹ᵁ ⊤
    have hD : D = B := by
      change B.ι ''ᵁ B.ι ⁻¹ᵁ ⊤ = B
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_top_eq]
    have h₁ : A.ι ''ᵁ D = L.ι ''ᵁ (L.ι ⁻¹ᵁ A) := by
      rw [hD, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
    have h₂ : A.ι ''ᵁ (⊤ : A.toScheme.Opens) = A := by
      simp [Scheme.Hom.image_top_eq_opensRange]
    let e₁ := G.presheaf.map (eqToHom h₂).op
    let e₂ := G.presheaf.map (eqToHom h₁.symm).op
    have hc : (T.map η).hom.app (op (W i)) =
        e₁ ≫ G'.presheaf.map (homOfLE (B.ι.image_preimage_le ⊤)).op ≫ e₂ := by
      change G.presheaf.map (homOfLE (L.ι.image_preimage_le A)).op =
        e₁ ≫ G.presheaf.map (homOfLE (A.ι.image_mono (B.ι.image_preimage_le ⊤))).op ≫ e₂
      dsimp only [e₁, e₂]
      simp only [← Functor.map_comp]
      rfl
    rw [hc]
    let : IsIso e₁ := inferInstanceAs (IsIso (G.presheaf.map (eqToHom h₂).op))
    let : IsIso e₂ := inferInstanceAs (IsIso (G.presheaf.map (eqToHom h₁.symm).op))
    let : IsIso (G'.presheaf.map (homOfLE (B.ι.image_preimage_le ⊤)).op) := htop
    exact IsIso.comp_isIso
  let : IsIso (T.map η) := hη
  let : IsIso (T.map η).hom :=
    (sheafToPresheaf (Opens.grothendieckTopology U) Ab).map_isIso (T.map η)
  let : IsIso η := Hom.isIso_iff_isIso_app.mpr fun W =>
    NatIso.isIso_app_of_isIso (T.map η).hom (op W)
  exact (restrictAdjunction L.ι).mem_essImage_of_unit_isIso G

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_open_local {X Y U : Scheme.{u}}
    (g : U ⟶ X) [Flat g] (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (H : Y.Modules) [H.IsQuasicoherent] :
    OpenLocal (g ⁻¹ᵁ j.opensRange).ι
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward j).obj H)) := by
  let J := {W : U.Opens // IsAffineOpen W ∧ ∃ T : X.Opens, IsAffineOpen T ∧ W ≤ g ⁻¹ᵁ T}
  have hb : Opens.IsBasis (Set.range (Subtype.val : J → U.Opens)) := by
    apply Opens.isBasis_iff_nbhd.mpr
    intro A x hx
    obtain ⟨T, hT, hxt, _⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (U := ⊤) (x := g x) (by trivial)
    obtain ⟨W, hW, hxw, hWA⟩ := Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens
      (U := A ⊓ g ⁻¹ᵁ T) (x := x) ⟨hx, hxt⟩
    exact ⟨W, ⟨⟨W, hW, T, hT, hWA.trans inf_le_right⟩, rfl⟩, hxw, hWA.trans inf_le_left⟩
  let F := (Scheme.Modules.pushforward j).obj H
  let G := (Scheme.Modules.pullback g).obj F
  let L := g ⁻¹ᵁ j.opensRange
  apply openLocal_on_basis Subtype.val hb L G
  rintro ⟨W, hW, T, hT, hWT⟩
  let g' := g.resLE T W hWT
  let j' := j ∣_ T
  let V := j ⁻¹ᵁ T
  let H' := H.restrict V.ι
  let : IsAffine W.toScheme := hW
  let : IsAffine T.toScheme := hT
  have h' := pullback_affine_open_local_of_isAffine g' j' H'
  let e : (Scheme.Modules.pullback g').obj ((Scheme.Modules.pushforward j').obj H') ≅
      G.restrict W.ι :=
    (Scheme.Modules.pullback g').mapIso ((restrictPushforwardIso j T).app H).symm ≪≫
      (Scheme.Modules.pullback g').mapIso ((restrictFunctorIsoPullback T.ι).app F) ≪≫
      (Scheme.Modules.pullbackComp g' T.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr (g.resLE_comp_ι hWT)).app F ≪≫
      ((Scheme.Modules.pullbackComp W.ι g).app F).symm ≪≫
      ((restrictFunctorIsoPullback W.ι).app G).symm
  apply openLocal_of_range_le (g' ⁻¹ᵁ j'.opensRange).ι (W.ι ⁻¹ᵁ L).ι
  · rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, g.resLE_preimage hWT]
    have hr : j'.opensRange = T.ι ⁻¹ᵁ j.opensRange :=
      opensRange_of_isPullback (isPullback_morphismRestrict j T)
    rw [hr, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact (Opens.map W.ι.base).monotone ((Opens.map g.base).monotone inf_le_right)
  · exact (Scheme.Modules.pushforward _).essImage.prop_of_iso e h'

set_option backward.isDefEq.respectTransparency false in
/-- The canonical mate for flat base change of the direct image of a quasi-compact open immersion. -/
theorem flatOpenBaseChange : FlatOpenBaseChange.{u} := by
  intro k _ X Y U V j l g r h hp hj hjc hg H hH
  let : IsOpenImmersion l.left := MorphismProperty.of_isPullback hp.flip inferInstance
  let F := (Scheme.Modules.pushforward j.left).obj H
  let G := (Scheme.Modules.pullback g.left).obj F
  have hG' := pullback_open_local g.left j.left H
  have hG : OpenLocal l.left G :=
    openLocal_of_range_le _ _ (by rw [Scheme.Opens.opensRange_ι, opensRange_of_isPullback hp]) hG'
  let A := Scheme.Modules.pullbackPushforwardAdjunction l.left
  let : IsIso (A.unit.app G) := A.isIso_unit_app_iff_mem_essImage.mpr hG
  let : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction j.left).counit.app H) := inferInstance
  unfold openBaseChange
  rw [Adjunction.homEquiv_unit]
  infer_instance

end

end LinearAlgebraicGroups.Representation.EquivariantOpenFlatBaseChange
