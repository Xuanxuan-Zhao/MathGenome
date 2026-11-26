import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.LinePushforwardProjection
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Sites.LocalProperties

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u v

noncomputable section

namespace LinearAlgebraicGroups.LinePushforwardProjection

open Specs.LinePushforwardProjection

theorem isIsoOnBasis : IsIsoOnBasis.{u, v} := by
  intro X M N a ι U hU h
  let F : X.Modules ⥤ TopCat.Sheaf Ab X := SheafOfModules.toSheaf _
  have : IsIso (F.map a) :=
    TopCat.Sheaf.isIso_iff_isIso_basis (φ := F.map a) hU h
  have : IsIso ((Scheme.Modules.toPresheaf X).map a) :=
    Functor.map_isIso (TopCat.Sheaf.forget Ab X) (F.map a)
  exact isIso_of_reflects_iso a (Scheme.Modules.toPresheaf X)

theorem isIsoOnCover : IsIsoOnCover.{u, v} := by
  intro X M N a ι U hU h
  let F : X.Modules ⥤ TopCat.Sheaf Ab X := SheafOfModules.toSheaf _
  have : IsIso (F.map a) := by
    rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro x
    obtain ⟨i, hx⟩ := hU.exists_mem x
    let y : (U i).toScheme := ⟨x, hx⟩
    let j := (U i).ι
    let e := Scheme.Modules.restrictStalkNatIso j y
    have h₁ := h i
    have h₂ : IsIso ((Scheme.Modules.restrictFunctor j ⋙
        Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y).map a) :=
      Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y)
        ((Scheme.Modules.restrictFunctor j).map a)
    change IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} (j y)).map a)
    rw [← isIso_comp_left_iff (e.hom.app M), ← e.hom.naturality]
    infer_instance
  have : IsIso ((Scheme.Modules.toPresheaf X).map a) :=
    Functor.map_isIso (TopCat.Sheaf.forget Ab X) (F.map a)
  exact isIso_of_reflects_iso a (Scheme.Modules.toPresheaf X)

theorem isIsoOfAffineSections : IsIsoOfAffineSections.{u} := by
  intro R M N a hM hN ha
  have hM' := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp hM
  have hN' := (isQuasicoherent_iff_isIso_fromTildeΓ N).mp hN
  have htilde : IsIso ((tilde.functor R).map (moduleSpecΓFunctor.map a)) :=
    Functor.map_isIso (tilde.functor R) (moduleSpecΓFunctor.map a)
  have hcomp := IsIso.comp_isIso' htilde hN'
  have h := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality a
  change (tilde.functor R).map (moduleSpecΓFunctor.map a) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ a at h
  exact (@isIso_comp_left_iff _ _ _ _ _ M.fromTildeΓ a hM').mp (h ▸ hcomp)

section OpenCharts

variable {X Y A B : Scheme.{u}} {f : X ⟶ Y} {g : A ⟶ B}
  (i : A ⟶ X) (j : B ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]

private lemma restrictUnitIsoApp (M : X.Modules) {U : X.Opens} (h : U ≤ i.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction i).unit.app M).app U) := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have he : i ''ᵁ (i ⁻¹ᵁ U) = U := by
    rw [i.image_preimage_eq_opensRange_inf, inf_eq_right.mpr h]
  have e : homOfLE (i.image_preimage_le U) = eqToHom he := Subsingleton.elim _ _
  rw [e, eqToHom_op]
  exact Functor.map_isIso M.presheaf (eqToHom _)

private def pushforwardSquare (h : g ≫ j = i ≫ f) :
    Scheme.Modules.pushforward i ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward j :=
  Scheme.Modules.pushforwardComp i f ≪≫ Scheme.Modules.pushforwardCongr h.symm ≪≫
    (Scheme.Modules.pushforwardComp g j).symm

set_option backward.isDefEq.respectTransparency false in
private def restrictPushforwardHom (h : IsPullback g i j f) (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict j ⟶
      (Scheme.Modules.pushforward g).obj (M.restrict i) :=
  ((Scheme.Modules.restrictAdjunction j).homEquiv _ _).symm
    ((Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictAdjunction i).unit.app M) ≫
      (pushforwardSquare i j h.w).hom.app (M.restrict i))

set_option backward.isDefEq.respectTransparency false in
theorem restrictPushforward : RestrictPushforward.{u} := by
  intro X Y A B f g i j _ _ h M
  let adj := Scheme.Modules.restrictAdjunction j
  let G := Scheme.Modules.pushforward g
  let F := Scheme.Modules.pushforward f
  let P := F.obj M
  let T := G.obj (M.restrict i)
  let E := pushforwardSquare i j h.w
  let b : P ⟶ (Scheme.Modules.pushforward j).obj T :=
    F.map ((Scheme.Modules.restrictAdjunction i).unit.app M) ≫ E.hom.app (M.restrict i)
  let a := restrictPushforwardHom i j h M
  have ha : adj.unit.app P ≫ (Scheme.Modules.pushforward j).map a = b := by
    exact (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv P T).apply_symm_apply b)
  have hi : IsIso a := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro V
    let U := j ''ᵁ V
    have hU : U ≤ j.opensRange := Set.image_subset_range _ _
    have hpre : f ⁻¹ᵁ U ≤ i.opensRange :=
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h V).ge.trans
        (Set.image_subset_range _ _)
    have := restrictUnitIsoApp j P hU
    have := restrictUnitIsoApp i M hpre
    have hb : IsIso (b.app U) := by
      change IsIso ((((Scheme.Modules.restrictAdjunction i).unit.app M).app (f ⁻¹ᵁ U)) ≫
        (E.hom.app (M.restrict i)).app U)
      infer_instance
    have hc := congrArg (fun c ↦ Scheme.Modules.Hom.app c U) ha
    change (adj.unit.app P).app U ≫ a.app (j ⁻¹ᵁ U) = b.app U at hc
    have hd : IsIso (a.app (j ⁻¹ᵁ U)) := by
      rw [← isIso_comp_left_iff ((adj.unit.app P).app U), hc]
      exact hb
    exact (j.preimage_image_eq V) ▸ hd
  refine ⟨asIso a, ?_⟩
  have hc := congrArg (fun c ↦ Scheme.Modules.Hom.app c ⊤) ha
  change chartSections j P ≫ a.app ⊤ =
    chartSections i M ≫ (E.hom.app (M.restrict i)).app ⊤ at hc
  change chartSections j P ≫ a.app ⊤ = chartSections i M
  rw [hc]
  have he : (E.hom.app (M.restrict i)).app ⊤ = 𝟙 _ := by
    simp [E, pushforwardSquare, Scheme.Modules.Hom.comp_app]
  rw [he]
  exact Category.comp_id _

end OpenCharts

theorem chartFiberComparison : ChartFiberComparison.{u} := by
  intro A B X Y g f i j _ h y
  let a : g.fiber y ⟶ f.fiber (j y) := pullback.map _ _ _ _ i
    (Spec.map (j.residueFieldMap y)) j h.w (by simp)
  have ha : IsIso a :=
    (isPullback_fiberToSpecResidueField_of_isPullback h.flip y).isIso_fst_of_isIso
  refine ⟨asIso a, ?_, ?_⟩
  · change a ≫ pullback.fst f (Y.fromSpecResidueField (j y)) = _
    exact pullback.lift_fst (f := f) (g := Y.fromSpecResidueField (j y))
      (g.fiberι y ≫ i) (g.fiberToSpecResidueField y ≫ Spec.map (j.residueFieldMap y)) _
  · change a ≫ pullback.snd f (Y.fromSpecResidueField (j y)) = _
    exact pullback.lift_snd (f := f) (g := Y.fromSpecResidueField (j y))
      (g.fiberι y ≫ i) (g.fiberToSpecResidueField y ≫ Spec.map (j.residueFieldMap y)) _

theorem affinePushforward : AffinePushforward.{u} := by
  intro R S φ M h
  exact isIso_fromTildeΓ_pushforward φ M

private lemma affineScalar {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) =
      (Scheme.ΓSpecIso S).inv (φ r) := by
  exact congr($(Scheme.ΓSpecIso_inv_naturality φ).hom r).symm

def affineSectionsIso {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec S).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M) ≅
      (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M) := by
  let A := moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M)
  let B := (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M)
  let e : A ≃ₗ[R] B :=
    { toAddEquiv := AddEquiv.refl _
      map_smul' := fun r s ↦ by
        let s' : Γ(M, ⊤) := s
        change (show Prop from (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) • s' =
          (Scheme.ΓSpecIso S).inv (φ r) • s')
        rw [affineScalar] }
  exact e.toModuleIso

theorem affinePushforwardSections : AffinePushforwardSections.{u} := by
  intro R S φ M
  exact ⟨affineSectionsIso φ M, fun _ ↦ rfl⟩

private def affineSectionsNatIso {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (affineSectionsIso φ) (fun _ ↦
    ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

private def affinePullbackTildeIso {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  ((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
      (tilde.adjunction (R := S))).ofNatIsoRight (affineSectionsNatIso φ).symm)

set_option backward.isDefEq.respectTransparency false in
private lemma affinePullbackTildeIso_sections {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (A : ModuleCat.{u} R) (s : A) :
    ((affinePullbackTildeIso φ).hom.app A).app ⊤
        (pullbackSections (Spec.map φ) (tilde A) ((tilde.isoTop A).hom s)) =
      (tilde.isoTop ((ModuleCat.extendScalars φ.hom).obj A)).hom
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app A s) := by
  let a := (tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
  let b := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))
  let e := affineSectionsNatIso φ
  have h := Adjunction.unit_leftAdjointUniq_hom_app a (b.ofNatIsoRight e.symm) A
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app] at h
  have h' : a.unit.app A ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor).map
        ((affinePullbackTildeIso φ).hom.app A) =
      b.unit.app A ≫ e.inv.app ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj A) := h
  have hs := congr($(h') s)
  dsimp only [a, b] at hs
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at hs
  exact hs

private lemma inverseTildeSections {R : CommRingCat.{u}} (P : (Spec R).Modules)
    [IsIso P.fromTildeΓ] (s : moduleSpecΓFunctor.obj P) :
    (asIso P.fromTildeΓ).inv.app ⊤ s =
      (tilde.isoTop (moduleSpecΓFunctor.obj P)).hom s := by
  let c := asIso P.fromTildeΓ
  have h := (tilde.adjunction (R := R)).right_triangle_components P
  have h' : (tilde.isoTop (moduleSpecΓFunctor.obj P)).hom ≫
      moduleSpecΓFunctor.map c.hom = 𝟙 _ := h
  have h'' := (Functor.mapIso moduleSpecΓFunctor c).inv_hom_id
  apply (ConcreteCategory.bijective_of_isIso (moduleSpecΓFunctor.map c.hom)).injective
  exact (congr($h'' s)).trans (congr($h' s)).symm

private lemma tildeComparisonSections {R : CommRingCat.{u}} (P : (Spec R).Modules)
    [IsIso P.fromTildeΓ] {B : ModuleCat.{u} R} (b : moduleSpecΓFunctor.obj P ≅ B)
    (s : moduleSpecΓFunctor.obj P) :
    (tilde.isoTop B).inv
        (((asIso P.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso b).hom.app ⊤ s) =
      b.hom s := by
  have h := congr($((tilde.toTildeΓNatIso (R := R)).hom.naturality b.hom) s)
  change (tilde.isoTop B).hom (b.hom s) =
    (tilde.map b.hom).app ⊤ ((tilde.isoTop (moduleSpecΓFunctor.obj P)).hom s) at h
  change (tilde.isoTop B).inv ((tilde.map b.hom).app ⊤ ((asIso P.fromTildeΓ).inv.app ⊤ s)) = _
  rw [inverseTildeSections, ← h, Iso.hom_inv_id_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem affinePullbackSections {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (P : (Spec R).Modules) [IsIso P.fromTildeΓ] :
    ∃ e : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj P) ≅
        (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P),
      ∀ s : moduleSpecΓFunctor.obj P,
        e.hom (pullbackSections (Spec.map φ) P s) =
          (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ s := by
  let f := Spec.map φ
  let A := moduleSpecΓFunctor.obj P
  let c := asIso P.fromTildeΓ
  let F := Scheme.Modules.pullback f
  let d := (affinePullbackTildeIso φ).app A
  let t := tilde.isoTop ((ModuleCat.extendScalars φ.hom).obj A)
  let e := moduleSpecΓFunctor.mapIso (F.mapIso c.symm ≪≫ d) ≪≫ t.symm
  refine ⟨e, fun s ↦ ?_⟩
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality c.inv
  have hs := congrArg (fun a ↦ Scheme.Modules.Hom.app a ⊤ s) hn
  change pullbackSections f (tilde A) (c.inv.app ⊤ s) =
    (F.map c.inv).app ⊤ (pullbackSections f P s) at hs
  change t.inv (d.hom.app ⊤ ((F.map c.inv).app ⊤ (pullbackSections f P s))) = _
  rw [← hs, inverseTildeSections P s]
  exact (congrArg t.inv (affinePullbackTildeIso_sections φ A s)).trans
    (Iso.hom_inv_id_apply t _)

private def unitSectionsIso (S : CommRingCat.{u}) :
    moduleSpecΓFunctor.obj (structureModule (Spec S)) ≅ ModuleCat.of S S := by
  let A := moduleSpecΓFunctor.obj (structureModule (Spec S))
  let e : A ≃ₗ[S] (ModuleCat.of S S) :=
    { toAddEquiv := (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv.toAddEquiv
      map_smul' := fun r s ↦ by
        let s' : Γ(Spec S, ⊤) := s
        change (show Prop from (Scheme.ΓSpecIso S).hom ((Scheme.ΓSpecIso S).inv r * s') =
          r * (Scheme.ΓSpecIso S).hom s')
        simp }
  exact e.toModuleIso

private lemma isIsoFromTildeOfTrivialization {S : CommRingCat.{u}} {M : (Spec S).Modules}
    (t : M ≅ structureModule (Spec S)) : IsIso M.fromTildeΓ :=
  isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf ≪≫ t.symm⟩⟩

private def affineTrivializedSectionsIso {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M : (Spec S).Modules} (t : M ≅ structureModule (Spec S)) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M) ≅
      (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) :=
  affineSectionsIso φ M ≪≫ (ModuleCat.restrictScalars φ.hom).mapIso
    (moduleSpecΓFunctor.mapIso t ≪≫ unitSectionsIso S)

theorem freeAffinePushforward : FreeAffinePushforward.{u} := by
  intro R S φ M t n B b
  let P := (Scheme.Modules.pushforward (Spec.map φ)).obj M
  have : IsIso P.fromTildeΓ := affinePushforward φ M (isIsoFromTildeOfTrivialization t)
  let i : moduleSpecΓFunctor.obj P ≅ ModuleCat.of R (Fin n → R) :=
    affineTrivializedSectionsIso φ t ≪≫ b.equivFun.toModuleIso
  exact ⟨(asIso P.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso i,
    fun s ↦ tildeComparisonSections P i s⟩

section Fiber

variable {X Y : Scheme.{u}}

private instance opensMapPreservesTerminal (f : X ⟶ Y) :
    PreservesLimit (CategoryTheory.Functor.empty.{0} (Opens Y)) (Opens.map f.base) :=
  preservesTerminal_of_iso (Opens.map f.base) ((Opens.map f.base).mapIso
    (terminalIsTerminal.uniqueUpToIso (isTerminalTop (α := Opens Y))) ≪≫
    (isTerminalTop (α := Opens X)).uniqueUpToIso terminalIsTerminal)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical unit identification for the pullback of the structure module. -/
def pullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureModule Y) ≅ structureModule X := by
  letI : (Opens.map f.base).Final := inferInstance
  letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let a := SheafOfModules.pullbackObjUnitToUnit (F := Opens.map f.base) f.toRingCatSheafHom
  haveI : IsIso a := inferInstanceAs (IsIso
    (SheafOfModules.pullbackObjUnitToUnit (F := Opens.map f.base) f.toRingCatSheafHom))
  exact asIso a

set_option backward.isDefEq.respectTransparency false in
private lemma pullbackUnitIso_sections (f : X ⟶ Y) :
    pullbackSections f (structureModule Y) ≫ (pullbackUnitIso f).hom.app ⊤ =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab).map f.appTop := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have h : adj.unit.app (structureModule Y) ≫
      (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    refine (adj.homEquiv_unit _ _ _).symm.trans ?_
    let : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
    exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (F := Opens.map f.base) f.toRingCatSheafHom)
  exact congrArg (fun a ↦ Scheme.Modules.Hom.app a ⊤) h

variable (R S K : Type u) [CommRing R] [CommRing S] [CommRing K]
  [Algebra R S] [Algebra R K]

private def fiberSpecIso : affineFiber R S K ≅ Spec (CommRingCat.of (K ⊗[R] S)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso R K S

private lemma fiberSpecIso_base :
    (fiberSpecIso R S K).inv ≫ fiberBase R S K =
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] S))) := by
  rw [Iso.inv_comp_eq]
  symm
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R K S).hom) ≫ _ = _
  rw [Category.assoc, pullbackSpecIso_hom_fst, pullbackSymmetry_hom_comp_fst]

private lemma fiberSpecIso_source :
    (fiberSpecIso R S K).inv ≫ fiberSource R S K =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)
        (A := K) (B := S)).toRingHom) := by
  rw [Iso.inv_comp_eq]
  symm
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R K S).hom) ≫ _ = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun a ↦ (pullbackSymmetry _ _).hom ≫ a)
    (pullbackSpecIso_hom_snd R K S)).trans ?_
  exact pullbackSymmetry_hom_comp_snd _ _

variable {T : Scheme.{u}} (e : T ≅ Spec (CommRingCat.of (K ⊗[R] S)))
  (q : T ⟶ Spec (CommRingCat.of K)) (j : T ⟶ Spec (CommRingCat.of S))

private def fiberRingIso : Γ(T, ⊤) ≅ CommRingCat.of (K ⊗[R] S) :=
  Scheme.Γ.mapIso e.op.symm ≪≫ Scheme.ΓSpecIso _

private lemma fiberRingIso_base
    (hq : e.inv ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] S)))) (r : K) :
    (fiberRingIso R S K e).hom (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r)) =
      algebraMap K (K ⊗[R] S) r := by
  have h := congrArg Scheme.Hom.appTop hq
  rw [Scheme.Hom.comp_appTop] at h
  change (Scheme.ΓSpecIso _).hom ((ConcreteCategory.hom
      (q.appTop ≫ e.inv.appTop))
      ((Scheme.ΓSpecIso _).inv r)) = _
  rw [h, affineScalar]
  simp

set_option quotPrecheck false in
local notation "includeSource" =>
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)
    (A := K) (B := S)).toRingHom)

private lemma fiberRingIso_source (hj : e.inv ≫ j = includeSource) (s : S) :
    (fiberRingIso R S K e).hom (j.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) =
      (1 : K) ⊗ₜ[R] s := by
  have h := congrArg Scheme.Hom.appTop hj
  rw [Scheme.Hom.comp_appTop] at h
  change (Scheme.ΓSpecIso _).hom ((ConcreteCategory.hom
      (j.appTop ≫ e.inv.appTop))
      ((Scheme.ΓSpecIso _).inv s)) = _
  rw [h, affineScalar]
  simp

private def fiberUnitSectionsIso
    (hq : e.inv ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] S)))) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj (structureModule T)) ≅
      ModuleCat.of K (K ⊗[R] S) := by
  let A := moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj (structureModule T))
  let l : A ≃ₗ[K] (ModuleCat.of K (K ⊗[R] S)) :=
    { toAddEquiv := (fiberRingIso R S K e).commRingCatIsoToRingEquiv.toAddEquiv
      map_smul' := fun r s ↦ by
        let s' : Γ(T, ⊤) := s
        change (show Prop from (fiberRingIso R S K e).hom
            (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r) * s') =
          r • (fiberRingIso R S K e).hom s')
        rw [map_mul, fiberRingIso_base R S K e q hq, Algebra.smul_def] }
  exact l.toModuleIso

private theorem affineFiberComparisonOfIso
    (hq : e.inv ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] S))))
    (hj : e.inv ≫ j = includeSource) (M : (Spec (CommRingCat.of S)).Modules)
    (t : M ≅ structureModule (Spec (CommRingCat.of S))) :
    ∃ E : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj
          ((Scheme.Modules.pullback j).obj M)) ≅ ModuleCat.of K (K ⊗[R] S),
      ∀ s : moduleSpecΓFunctor.obj M,
        E.hom (pullbackSections j M s) =
          (1 : K) ⊗ₜ[R] ((Scheme.ΓSpecIso (CommRingCat.of S)).hom (t.hom.app ⊤ s) : S) := by
  let F := Scheme.Modules.pullback j
  let G := Scheme.Modules.pushforward q
  let H := moduleSpecΓFunctor (R := CommRingCat.of K)
  let E := H.mapIso (G.mapIso (F.mapIso t ≪≫ pullbackUnitIso j)) ≪≫
    fiberUnitSectionsIso R S K e q hq
  refine ⟨E, fun s ↦ ?_⟩
  have h := (Scheme.Modules.pullbackPushforwardAdjunction j).unit_naturality t.hom
  have hs := congrArg (fun a ↦ Scheme.Modules.Hom.app a ⊤ s) h
  change ((F.map t.hom).app ⊤) (pullbackSections j M s) =
    pullbackSections j (structureModule (Spec (CommRingCat.of S))) (t.hom.app ⊤ s) at hs
  have hu := congr($(pullbackUnitIso_sections j) (t.hom.app ⊤ s))
  let s' : Γ(Spec (CommRingCat.of S), ⊤) := t.hom.app ⊤ s
  change (fiberRingIso R S K e).hom
    ((pullbackUnitIso j).hom.app ⊤ ((F.map t.hom).app ⊤ (pullbackSections j M s))) =
      (1 : K) ⊗ₜ[R] (Scheme.ΓSpecIso (CommRingCat.of S)).hom s'
  rw [hs]
  change (pullbackUnitIso j).hom.app ⊤
    (pullbackSections j (structureModule (Spec (CommRingCat.of S))) s') = j.appTop s' at hu
  rw [hu]
  have hs' := fiberRingIso_source R S K e j hj ((Scheme.ΓSpecIso (CommRingCat.of S)).hom s')
  rw [Iso.hom_inv_id_apply] at hs'
  exact hs'

theorem affineFiberComparison : AffineFiberComparison.{u} := by
  intro R S K _ _ _ _ _ M t
  exact affineFiberComparisonOfIso R S K (fiberSpecIso R S K) (fiberBase R S K)
    (fiberSource R S K) (fiberSpecIso_base R S K) (fiberSpecIso_source R S K) M t

private theorem affineFiberBaseChangeOfIsPullback
    (h : IsPullback q j (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (M : (Spec (CommRingCat.of S)).Modules) (t : M ≅ structureModule (Spec (CommRingCat.of S))) :
    let P := moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj M)
    ∃ E : ModuleCat.of K (K ⊗[R] P) ≅ moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward q).obj ((Scheme.Modules.pullback j).obj M)),
      ∀ s : moduleSpecΓFunctor.obj M,
        E.hom ((1 : K) ⊗ₜ[R] (s : P)) = pullbackSections j M s := by
  intro P
  let e := h.flip.isoPullback ≪≫ fiberSpecIso R S K
  have hq : e.inv ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] S))) := by
    change ((fiberSpecIso R S K).inv ≫ h.flip.isoPullback.inv) ≫ q = _
    rw [Category.assoc, IsPullback.isoPullback_inv_snd]
    exact fiberSpecIso_base R S K
  have hj : e.inv ≫ j = includeSource := by
    change ((fiberSpecIso R S K).inv ≫ h.flip.isoPullback.inv) ≫ j = _
    rw [Category.assoc, IsPullback.isoPullback_inv_fst]
    exact fiberSpecIso_source R S K
  let φ := CommRingCat.ofHom (algebraMap R S)
  let i := affineTrivializedSectionsIso φ t
  let l : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of (CommRingCat.of S) S) ≃ₗ[R] S :=
    { toAddEquiv := AddEquiv.refl _
      map_smul' := fun r s ↦ by
        let s' : S := s
        change (show Prop from (algebraMap R S r) * s' = r • s')
        exact (Algebra.smul_def r s').symm }
  let e₀ : ModuleCat.of K (K ⊗[R] P) ≅ ModuleCat.of K (K ⊗[R] S) :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
      (i.toLinearEquiv.trans l)).toModuleIso
  obtain ⟨e₁, he₁⟩ := affineFiberComparisonOfIso R S K e q j hq hj M t
  refine ⟨e₀ ≪≫ e₁.symm, fun s ↦ ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e₁.hom).injective
  rw [he₁]
  change e₁.hom (e₁.inv (e₀.hom ((1 : K) ⊗ₜ[R] (s : P)))) = _
  rw [Iso.inv_hom_id_apply]
  rfl

theorem affineFiberBaseChange : AffineFiberBaseChange.{u} := by
  intro R S K _ _ _ _ _ M t
  exact affineFiberBaseChangeOfIsPullback R S K (fiberBase R S K) (fiberSource R S K)
    (IsPullback.of_hasPullback _ _).flip M t

theorem affineBaseChangeSections : AffineBaseChangeSections.{u} := by
  intro R S K φ g T q j h M t P
  obtain ⟨ψ, rfl⟩ : ∃ ψ : R ⟶ K, Spec.map ψ = g := ⟨Spec.preimage g, Spec.map_preimage g⟩
  have : IsIso P.fromTildeΓ := affinePushforward φ M (isIsoFromTildeOfTrivialization t)
  obtain ⟨a, ha⟩ := affinePullbackSections ψ P
  let : Algebra R S := φ.hom.toAlgebra
  let : Algebra R K := ψ.hom.toAlgebra
  obtain ⟨b, hb⟩ := affineFiberBaseChangeOfIsPullback R S K q j h M t
  refine ⟨a ≪≫ b, fun s ↦ ?_⟩
  have hs := ha (show moduleSpecΓFunctor.obj P from s)
  exact (congrArg (fun x ↦ b.hom x) hs).trans (hb s)

theorem affineResidueFiber : AffineResidueFiber.{u} := by
  intro R S _ _ _ p f
  let T := Spec (CommRingCat.of p.asIdeal.ResidueField)
  let B := Spec (CommRingCat.of R)
  let t : T ⟶ B := Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
  let j : Spec (B.residueField p) ⟶ T :=
    Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv
  have hj : j ≫ t = B.fromSpecResidueField p :=
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ _
  let a : f.fiber p ⟶ affineFiber R S p.asIdeal.ResidueField :=
    pullback.map _ _ _ _ (𝟙 _) j (𝟙 _) (by change f ≫ 𝟙 _ = 𝟙 _ ≫ f; simp) (by simpa using hj.symm)
  have ha : IsIso a := by
    let : IsIso j := by dsimp [j]; infer_instance
    exact inferInstanceAs (IsIso (pullback.map _ _ _ _ (𝟙 _) j (𝟙 _) _ _))
  refine ⟨(asIso a).symm, ?_, ?_⟩
  · change (asIso a).inv ≫ f.fiberι p = _
    rw [Iso.inv_comp_eq]
    change pullback.fst f (B.fromSpecResidueField p) =
      a ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) t
    symm
    exact pullback.lift_fst (f := Spec.map (CommRingCat.ofHom (algebraMap R S))) (g := t)
      (pullback.fst f (B.fromSpecResidueField p))
      (pullback.snd f (B.fromSpecResidueField p) ≫ j) _
  · change (asIso a).inv ≫ f.fiberToSpecResidueField p ≫ j = _
    rw [Iso.inv_comp_eq]
    symm
    exact pullback.lift_snd (f := Spec.map (CommRingCat.ofHom (algebraMap R S))) (g := t)
      (pullback.fst f (B.fromSpecResidueField p) ≫ 𝟙 _)
      (pullback.snd f (B.fromSpecResidueField p) ≫ j) _

theorem affineResidueSections : AffineResidueSections.{u} := by
  intro R S φ p M t f g
  exact affineBaseChangeSections φ g (f.fiberToSpecResidueField p) (f.fiberι p)
    (IsPullback.of_hasPullback f g).flip M t

end Fiber

open MonoidalCategory

private lemma overLocallyBijective {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) (U : C) {F G : Cᵒᵖ ⥤ Ab.{u}} (p : F ⟶ G)
    [Presheaf.IsLocallyInjective J p] [Presheaf.IsLocallySurjective J p] :
    let q := Functor.whiskerLeft (Over.forget U).op p
    Presheaf.IsLocallyInjective (J.over U) q ∧ Presheaf.IsLocallySurjective (J.over U) q := by
  dsimp
  constructor
  · constructor
    intro V s t h
    rw [GrothendieckTopology.mem_over_iff]
    have he : Sieve.overEquiv V.unop (Presheaf.equalizerSieve s t) =
        (Presheaf.equalizerSieve (F := F) s t) := by
      ext W w
      rw [Sieve.overEquiv_iff]
      rfl
    rw [he]
    exact Presheaf.equalizerSieve_mem J (φ := p) s t h
  · constructor
    intro V s
    rw [GrothendieckTopology.mem_over_iff]
    have he : Sieve.overEquiv V (Presheaf.imageSieve
        (Functor.whiskerLeft (Over.forget U).op p) s) =
        Presheaf.imageSieve p s := by
      ext W w
      rw [Sieve.overEquiv_iff]
      rfl
    rw [he]
    exact Presheaf.imageSieve_mem J (f := p) s

set_option backward.isDefEq.respectTransparency false in
private def overTrivialization {X : Scheme.{u}} {N : X.Modules} {U : X.Opens}
    (t : N.restrict U.ι ≅ structureModule U.toScheme) :
    N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) := by
  let e := Scheme.Modules.overEquiv U
  refine e.fullyFaithfulFunctor.preimageIso (?_ ≪≫ t ≪≫ ?_)
  · exact (Scheme.Modules.overFunctorEquiv U).app N
  · exact (Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm

set_option backward.isDefEq.respectTransparency false in
private def rankOneFreeIso {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasWeakSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}] :
    SheafOfModules.free (R := R) PUnit.{u+1} ≅ SheafOfModules.unit R where
  hom := Sigma.desc (fun _ ↦ 𝟙 _)
  inv := SheafOfModules.ιFree PUnit.unit
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    cases i
    unfold SheafOfModules.ιFree SheafOfModules.free
    rw [← Category.assoc, Sigma.ι_comp_desc, Category.id_comp, Category.comp_id]
  inv_hom_id := Sigma.ι_comp_desc (fun _ ↦ 𝟙 _) _

set_option backward.isDefEq.respectTransparency false in
theorem quasicoherentOfLine {X : Scheme.{u}} {M : X.Modules} (h : IsLine M) :
    M.IsQuasicoherent := by
  classical
  let I := {U : X.Opens // Nonempty (M.restrict U.ι ≅ structureModule U.toScheme)}
  let U : I → X.Opens := Subtype.val
  have hU : IsOpenCover U := by
    refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨V, hx, t⟩ := h x
    exact (le_iSup U ⟨V, t⟩) hx
  let a (i : I) : SheafOfModules.free PUnit.{u+1} ≅ M.over (U i) :=
    rankOneFreeIso (X.ringCatSheaf.over (U i)) ≪≫ (overTrivialization i.property.some).symm
  let D : M.LocalGeneratorsData :=
    { I := I
      X := U
      coversTop := (Opens.coversTop_iff _ _).mpr hU
      generators i := (SheafOfModules.free.generatingSections PUnit.{u+1}).ofEpi (a i).hom }
  have : D.IsLocallyFreeData := by
    constructor
    intro i
    change IsIso (((SheafOfModules.free.generatingSections PUnit.{u+1}).ofEpi (a i).hom).π)
    simp only [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    infer_instance
  have : M.IsLocallyFree := D.isLocallyFree
  infer_instance

theorem affineLinePushforward : AffineLinePushforward.{u} := by
  intro R S φ M h
  have : M.IsQuasicoherent := quasicoherentOfLine h
  exact affinePushforward φ M inferInstance

set_option backward.isDefEq.respectTransparency false in
theorem finitePushforwardOnChart : FinitePushforwardOnChart.{u} := by
  intro X Y f _ R j _ M hM S P
  let A := pullback f j
  let q := pullback.snd f j
  have : IsAffine A := isAffine_of_isAffineHom q
  let a := (asIso A.toSpecΓ).symm
  let i : Spec S ⟶ X := a.hom ≫ pullback.fst f j
  let φ : R ⟶ S := Spec.preimage (a.hom ≫ q)
  have hφ : Spec.map φ = a.hom ≫ q := Spec.map_preimage _
  have hi : IsOpenImmersion i := by
    dsimp [i]
    infer_instance
  have h : IsPullback (Spec.map φ) i j f :=
    (IsPullback.of_hasPullback f j).flip.of_iso' a (.refl _) (.refl _) (.refl _)
      (by simpa only [Iso.refl_hom, Category.comp_id] using hφ.symm)
      (by simp [i]) (by simp) (by simp)
  refine ⟨i, φ, hi, h, ?_⟩
  have : M.IsQuasicoherent := quasicoherentOfLine hM
  have : (M.restrict i).IsQuasicoherent :=
    inferInstanceAs (((Scheme.Modules.restrictFunctor i).obj M).IsQuasicoherent)
  let Q := (Scheme.Modules.pushforward (Spec.map φ)).obj (M.restrict i)
  have : IsIso Q.fromTildeΓ := affinePushforward φ (M.restrict i) inferInstance
  obtain ⟨c, hc⟩ := restrictPushforward i j h M
  let b := affineSectionsIso φ (M.restrict i)
  let d := (asIso Q.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso b
  refine ⟨c ≪≫ d, fun s ↦ ?_⟩
  exact (tildeComparisonSections Q b (c.hom.app ⊤ (chartSections j P s))).trans (congr($hc s))

set_option backward.isDefEq.respectTransparency false in
private lemma tensorUnitIsoApp {X : Scheme.{u}} {M N : X.Modules} (U : X.Opens)
    (t : N.restrict U.ι ≅ structureModule U.toScheme) :
    IsIso ((tensorToSheaf M N).app (.op U)) := by
  let J := Opens.grothendieckTopology X
  let : J.WEqualsLocallyBijective Ab.{u} :=
    (inferInstance : (Opens.grothendieckTopology X).WEqualsLocallyBijective Ab.{u})
  let P := tensorPresheaf M N
  let p := (PresheafOfModules.toPresheaf _).map (tensorToSheaf M N)
  let q := Functor.whiskerLeft (Over.forget U).op p
  let R := (Over.forget U).op ⋙ X.presheaf
  let e := overTrivialization t
  let e' : PresheafOfModulesOfCommRing R :=
    ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M).val
  let i : ((SheafOfModules.overFunctor X.ringCatSheaf U).obj N).val ≅
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val :=
    (SheafOfModules.forget _).mapIso e
  have hA : Presheaf.IsSheaf (J.over U) ((Over.forget U).op ⋙ P.presheaf) := by
    let g := PresheafOfModules.toPresheaf ((X.ringCatSheaf.over U).obj)
    let c : (e' ⊗ ((SheafOfModules.overFunctor X.ringCatSheaf U).obj N).val) ≅ e' :=
      MonoidalCategory.tensorIso (Iso.refl _) i ≪≫ ρ_ _
    exact (Presheaf.isSheaf_of_iso_iff (J := J.over U) (g.mapIso c)).mpr ((M.over U).isSheaf)
  have hB : Presheaf.IsSheaf (J.over U) ((Over.forget U).op ⋙ (tensorModule M N).presheaf) :=
    ((J.overPullback Ab U).obj ((SheafOfModules.toSheaf _).obj (tensorModule M N))).property
  let A : Sheaf (J.over U) Ab := ⟨_, hA⟩
  let B : Sheaf (J.over U) Ab := ⟨_, hB⟩
  let b : A ⟶ B := ⟨q⟩
  have hp : p = CategoryTheory.toSheafify J P.presheaf := rfl
  have hW : J.W p := hp ▸ J.W_toSheafify P.presheaf
  have := hW.isLocallyInjective
  have := hW.isLocallySurjective
  have hq := overLocallyBijective J U p
  have : IsIso b := (Sheaf.isLocallyBijective_iff_isIso b).mp hq
  have hb : IsIso b.hom := (ObjectProperty.isIso_hom_iff b).mpr ‹IsIso b›
  have h : IsIso (b.hom.app (op (Over.mk (𝟙 U)))) :=
    (NatTrans.isIso_iff_isIso_app b.hom).mp hb _
  let F := forget₂ (ModuleCat Γ(X, U)) Ab.{u}
  have : IsIso (F.map ((tensorToSheaf M N).app (.op U))) := h
  exact isIso_of_reflects_iso _ F

section OpenLine

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (N : Y.Modules)

set_option quotPrecheck false in
local notation "W" => f ⁻¹ᵁ U
set_option quotPrecheck false in
local notation "i" => AlgebraicGeometry.Scheme.Opens.ι (f ⁻¹ᵁ U)
local notation "j" => AlgebraicGeometry.Scheme.Opens.ι U
local notation "g" => morphismRestrict f U

private def pushOpenSquare :
    Scheme.Modules.pushforward i ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward j :=
  Scheme.Modules.pushforwardComp i f ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pushforwardComp g j).symm

private def restrictPullbackIso :
    ((Scheme.Modules.pullback f).obj N).restrict i ≅
      (Scheme.Modules.pullback g).obj (N.restrict j) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction i)).leftAdjointUniq
    (((Scheme.Modules.restrictAdjunction j).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g)).ofNatIsoRight
        (pushOpenSquare f U).symm)).app N

set_option backward.isDefEq.respectTransparency false in
private lemma restrictPullback_unit :
    let A := (Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction i)
    let B := (Scheme.Modules.restrictAdjunction j).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g)
    A.unit.app N ≫
        (Scheme.Modules.pushforward i ⋙ Scheme.Modules.pushforward f).map
          (restrictPullbackIso f U N).hom ≫
        (pushOpenSquare f U).hom.app ((Scheme.Modules.pullback g).obj (N.restrict j)) =
      B.unit.app N := by
  dsimp only
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction i))
    (((Scheme.Modules.restrictAdjunction j).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g)).ofNatIsoRight (pushOpenSquare f U).symm) N
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app] at h
  have h' : ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction i)).unit.app N ≫
        (Scheme.Modules.pushforward i ⋙ Scheme.Modules.pushforward f).map
          (restrictPullbackIso f U N).hom =
      ((Scheme.Modules.restrictAdjunction j).comp
        (Scheme.Modules.pullbackPushforwardAdjunction g)).unit.app N ≫
          (pushOpenSquare f U).inv.app ((Scheme.Modules.pullback g).obj (N.restrict j)) := h
  rw [← Category.assoc, h', Category.assoc]
  simp

private def openSectionsIso (V : X.Opens) (M : X.Modules) :
    Γ(M, V) ≅ Γ(M.restrict V.ι, ⊤) :=
  M.presheaf.mapIso (eqToIso V.ι_image_top).op ≪≫ (M.restrictAppIso V.ι ⊤).symm

private lemma openSectionsIso_smul (V : X.Opens) (M : X.Modules)
    (r : Γ(X, V)) (s : Γ(M, V)) :
    (openSectionsIso V M).hom (r • s) =
      V.topIso.inv r • (openSectionsIso V M).hom s := by
  let a := (M.restrictAppIso V.ι ⊤).inv
  let m := M.presheaf.map (eqToHom V.ι_image_top).op
  change a (m (r • s)) = _ • a (m s)
  rw [show m (r • s) = X.presheaf.map (eqToHom V.ι_image_top).op r • m s
    from M.map_smul (eqToHom V.ι_image_top) r s]
  refine (M.smul_restrictAppIso_inv_apply V.ι ⊤ _ _).trans ?_
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
  rfl

private lemma restrictUnit_top (V : X.Opens) (M : X.Modules) :
    ((Scheme.Modules.restrictAdjunction V.ι).unit.app M).app V ≫
      (M.restrict V.ι).presheaf.map (eqToHom V.ι_preimage_self.symm).op =
      (openSectionsIso V M).hom := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  change M.presheaf.map (homOfLE (V.ι.image_preimage_le V)).op ≫
      M.presheaf.map ((V.ι.opensFunctor).map (eqToHom V.ι_preimage_self.symm)).op =
        M.presheaf.map (eqToHom V.ι_image_top).op ≫ 𝟙 _
  rw [Category.comp_id, ← Functor.map_comp, ← op_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private lemma restrictPullbackSections :
    let L := (Scheme.Modules.pullback f).obj N
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U ≫
      (openSectionsIso W L).hom ≫ (restrictPullbackIso f U N).hom.app ⊤ =
      (openSectionsIso U N).hom ≫ pullbackSections g (N.restrict j) := by
  dsimp only
  let L := (Scheme.Modules.pullback f).obj N
  let K := (Scheme.Modules.pullback g).obj (N.restrict j)
  let α := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U
  let β := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (N.restrict j))
  let r := eqToHom (W).ι_preimage_self.symm
  let s := eqToHom U.ι_preimage_self.symm
  let e := (restrictPullbackIso f U N).hom
  let E := (pushOpenSquare f U).hom.app K
  have h := congrArg (fun a ↦ Scheme.Modules.Hom.app a U) (restrictPullback_unit f U N)
  change (α ≫ ((Scheme.Modules.restrictAdjunction i).unit.app L).app W) ≫
      e.app (i ⁻¹ᵁ W) ≫ E.app U =
    ((Scheme.Modules.restrictAdjunction j).unit.app N).app U ≫ β.app (j ⁻¹ᵁ U) at h
  have hr :
      E.app U ≫ K.presheaf.map ((Opens.map (g).base).map s).op =
        K.presheaf.map r.op := by
    simp only [E, pushOpenSquare, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
      Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
      Category.id_comp, Category.comp_id]
    rw [← Functor.map_comp, ← op_comp]
    congr 1
  have ha := congrArg (fun a ↦ a ≫ K.presheaf.map ((Opens.map (g).base).map s).op) h
  simp only [Category.assoc, hr] at ha
  let M' := L.restrict i
  have he := (e.mapPresheaf.naturality r.op).symm
  change e.app (i ⁻¹ᵁ W) ≫ K.presheaf.map r.op =
      M'.presheaf.map r.op ≫ e.app ⊤ at he
  rw [he] at ha
  -- The restriction on the right is the one in the preimage of the target chart.
  have hb := (β.mapPresheaf.naturality s.op).symm
  change β.app (j ⁻¹ᵁ U) ≫ K.presheaf.map ((Opens.map (g).base).map s).op =
    (N.restrict j).presheaf.map s.op ≫ β.app ⊤ at hb
  rw [hb] at ha
  have hleft := congrArg (fun a ↦ α ≫ a ≫ e.app ⊤) (restrictUnit_top W L)
  have hright := congrArg (fun a ↦ a ≫ β.app ⊤) (restrictUnit_top U N)
  simp only [Category.assoc] at hleft hright ha
  exact hleft.symm.trans (ha.trans hright)

private abbrev sectionModule {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) :
    ModuleCat Γ(X, V) := ModuleCat.of Γ(X, V) Γ(M, V)

private def openLineCoordinates {X : Scheme.{u}} {M : X.Modules} (V : X.Opens)
    (t : M.restrict V.ι ≅ structureModule V.toScheme) :
    sectionModule M V ≅ ModuleCat.of Γ(X, V) Γ(X, V) := by
  let F : CommRingCat.{u} ⥤ Ab.{u} := forget₂ _ RingCat ⋙ forget₂ _ _
  let e := openSectionsIso V M ≪≫ asIso (t.hom.app ⊤) ≪≫ F.mapIso V.topIso
  let l : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
    { toAddEquiv := e.addCommGroupIsoToAddEquiv
      map_smul' := fun r x ↦ by
        let y := (openSectionsIso V M).hom x
        change V.topIso.hom (t.hom.app ⊤ ((openSectionsIso V M).hom (r • x))) =
          r * V.topIso.hom (t.hom.app ⊤ y)
        rw [openSectionsIso_smul, Scheme.Modules.Hom.app_smul]
        let z : Γ(V.toScheme, ⊤) := t.hom.app ⊤ y
        change (show Prop from V.topIso.hom (V.topIso.inv r * z) = _)
        rw [map_mul, Iso.inv_hom_id_apply] }
  exact l.toModuleIso

private lemma openLineCoordinates_apply {X : Scheme.{u}} {M : X.Modules} (V : X.Opens)
    (t : M.restrict V.ι ≅ structureModule V.toScheme) (x : Γ(M, V)) :
    (openLineCoordinates V t).hom x =
      V.topIso.hom (t.hom.app ⊤ ((openSectionsIso V M).hom x)) := rfl

private def pullbackLineOnOpen
    (t : N.restrict j ≅ structureModule U.toScheme) :
    ((Scheme.Modules.pullback f).obj N).restrict i ≅ structureModule (W).toScheme :=
  restrictPullbackIso f U N ≪≫ (Scheme.Modules.pullback g).mapIso t ≪≫ pullbackUnitIso g

set_option backward.isDefEq.respectTransparency false in
private lemma pulledLineCoordinateOne (t : N.restrict j ≅ structureModule U.toScheme)
    (n : Γ(N, U)) (hn : (openLineCoordinates U t).hom n = 1) :
    (openLineCoordinates W (pullbackLineOnOpen f U N t)).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U n) = 1 := by
  let e := (restrictPullbackIso f U N).hom
  let z := (openSectionsIso U N).hom n
  have h := congr($(restrictPullbackSections f U N) n)
  have h₁ : t.hom.app ⊤ z = (1 : Γ(U.toScheme, ⊤)) := by
    apply (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective
    rw [openLineCoordinates_apply] at hn
    rw [map_one]
    exact hn
  have h₂ := (Scheme.Modules.pullbackPushforwardAdjunction g).unit_naturality t.hom
  have h₃ := congrArg (fun a ↦ Scheme.Modules.Hom.app a ⊤ z) h₂
  change ((Scheme.Modules.pullback g).map t.hom).app ⊤
      (pullbackSections g (N.restrict j) z) =
    pullbackSections g (structureModule U.toScheme) (t.hom.app ⊤ z) at h₃
  let q := (pullbackUnitIso g).hom.app ⊤
  rw [openLineCoordinates_apply]
  change (W).topIso.hom (q (((Scheme.Modules.pullback g).map t.hom).app ⊤
    (e.app ⊤ ((openSectionsIso W ((Scheme.Modules.pullback f).obj N)).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U n))))) = 1
  change e.app ⊤ ((openSectionsIso W ((Scheme.Modules.pullback f).obj N)).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U n)) =
    pullbackSections g (N.restrict j) z at h
  rw [h, h₃]
  have hu := congr($(pullbackUnitIso_sections g) (t.hom.app ⊤ z))
  change q (pullbackSections g (structureModule U.toScheme) (t.hom.app ⊤ z)) =
    (g).appTop (t.hom.app ⊤ z) at hu
  rw [hu, h₁, map_one, map_one]

end OpenLine


section Projection

open MonoidalCategory ModuleCat.MonoidalCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) (N : Y.Modules)

set_option quotPrecheck false in
local notation "P" => (Scheme.Modules.pushforward f).obj M
set_option quotPrecheck false in
local notation "L" => (Scheme.Modules.pullback f).obj N
set_option quotPrecheck false in
local notation "η" => (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N

section ScalarComparison

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⟶ F.op ⋙ R)
  (A B : PresheafOfModulesOfCommRing R)

local notation "Fstar" => PresheafOfModulesOfCommRing.pushforward φ

set_option backward.isDefEq.respectTransparency false in
private def tensorPushforwardApp (U : Cᵒᵖ) :
    (((Fstar).obj A) ⊗ ((Fstar).obj B) : PresheafOfModulesOfCommRing S).obj U ⟶
      ((Fstar).obj (A ⊗ B)).obj U := by
  let V := F.op.obj U
  change MonoidalCategory.tensorObj ((ModuleCat.restrictScalars (φ.app U).hom).obj (A.obj V))
      ((ModuleCat.restrictScalars (φ.app U).hom).obj (B.obj V)) ⟶
    (ModuleCat.restrictScalars (φ.app U).hom).obj (MonoidalCategory.tensorObj (A.obj V) (B.obj V))
  exact tensorLift (fun a b ↦ (a : A.obj V) ⊗ₜ[R.obj V] (b : B.obj V))
    (fun a a' b ↦ TensorProduct.add_tmul a a' b)
    (fun r a b ↦ TensorProduct.smul_tmul' (R := R.obj V) (R' := R.obj V) (M := A.obj V) (N := B.obj V) (φ.app U r) a b)
    (fun a b b' ↦ TensorProduct.tmul_add a b b')
    (fun r a b ↦ TensorProduct.tmul_smul (R := R.obj V) (R' := R.obj V) (M := A.obj V) (N := B.obj V) (φ.app U r) a b)

set_option backward.isDefEq.respectTransparency false in
private def tensorPushforward :
    ((Fstar).obj A) ⊗ ((Fstar).obj B) ⟶ (Fstar).obj (A ⊗ B) where
  app U := tensorPushforwardApp φ A B U
  naturality {U V} i := by
    apply tensor_ext
    intro a b
    change tensorPushforwardApp φ A B V
        ((((Fstar).obj A) ⊗ ((Fstar).obj B) : PresheafOfModulesOfCommRing S).map i (a ⊗ₜ b)) =
      (((Fstar).obj (A ⊗ B)).map i) (tensorPushforwardApp φ A B U (a ⊗ₜ b))
    have hl := PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul
      (M₁ := (Fstar).obj A) (M₂ := (Fstar).obj B) i a b
    erw [hl]
    exact (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul
      (M₁ := A) (M₂ := B) (F.op.map i) a b).symm

end ScalarComparison

set_option backward.isDefEq.respectTransparency false in
private def projectionPresheaf :
    tensorPresheaf P N ⟶ ((Scheme.Modules.pushforward f).obj (tensorModule M L)).val :=
  PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 (P).val) (η).val ≫
    tensorPushforward f.c M.val (L).val ≫
    (PresheafOfModulesOfCommRing.pushforward f.c).map (tensorToSheaf M L)

/-- The canonical projection morphism, obtained by extending the bilinear map
on sections through sheafification. -/
def projectionMap :
    tensorModule P N ⟶ (Scheme.Modules.pushforward f).obj (tensorModule M L) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv
    (tensorPresheaf P N) _).symm (projectionPresheaf f M N)

set_option backward.isDefEq.respectTransparency false in
private lemma projectionMap_precompose :
    tensorToSheaf P N ≫ (projectionMap f M N).val = projectionPresheaf f M N := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let β := projectionPresheaf f M N
  have h := (adj.homEquiv (tensorPresheaf P N)
    ((Scheme.Modules.pushforward f).obj (tensorModule M L))).apply_symm_apply β
  refine Eq.trans ?_ h
  have hη := adj.homEquiv_id (tensorPresheaf P N)
  exact (congrArg (fun a ↦ a ≫ (projectionMap f M N).val) hη).trans
    (adj.homEquiv_unit _ _ (projectionMap f M N)).symm

set_option backward.isDefEq.respectTransparency false in
theorem projectionMap_isProjectionMap : IsProjectionMap f M N (projectionMap f M N) := by
  intro U s t
  exact congrArg (fun a ↦ a.app (.op U) (s ⊗ₜ[Γ(Y, U)] t))
    (projectionMap_precompose f M N)

set_option backward.isDefEq.respectTransparency false in
private lemma projectionMap_isIso_app (U : Y.Opens)
    (t : N.restrict U.ι ≅ structureModule U.toScheme) :
    IsIso ((projectionMap f M N).app U) := by
  let W := f ⁻¹ᵁ U
  let c := openLineCoordinates U t
  let t' := pullbackLineOnOpen f U N t
  let d := openLineCoordinates W t'
  let n : Γ(N, U) := c.inv 1
  have hn : c.hom n = 1 := Iso.inv_hom_id_apply c 1
  let ηU : Γ(N, U) ⟶ Γ(L, W) := (η).app U
  have hn' : d.hom (ηU n) = 1 := pulledLineCoordinateOne f U N t n hn
  have hη (r : Γ(Y, U)) :
      ηU (r • n) = (f.app U r) • (ηU n : Γ(L, W)) :=
    Scheme.Modules.Hom.app_smul η (U := U) r n
  have hcoord (x : Γ(N, U)) : d.hom (ηU x) = f.app U (c.hom x) := by
    let r : Γ(Y, U) := c.hom x
    have hx : r • n = x := by
      apply (ConcreteCategory.bijective_of_isIso c.hom).injective
      change c.hom (r • n) = r
      have hc : c.hom (r • n) = r * c.hom n := c.hom.hom.map_smul r n
      rw [hc, hn, mul_one]
    calc
      d.hom (ηU x) = d.hom (ηU (r • n)) := congrArg (fun m ↦ d.hom (ηU m)) hx.symm
      _ = d.hom ((f.app U r) • (ηU n : Γ(L, W))) := congrArg (fun m ↦ d.hom m) (hη r)
      _ = f.app U r := by
        have hd : d.hom (f.app U r • ηU n) = f.app U r * d.hom (ηU n) :=
          d.hom.hom.map_smul (f.app U r) (ηU n)
        rw [hd, hn', mul_one]
  let T := tensorToSheaf M L
  have hT : IsIso (T.app (.op W)) := tensorUnitIsoApp W t'
  let e₀ : (tensorPresheaf P N).obj (.op U) ≅ (P).val.obj (.op U) :=
    tensorIso (Iso.refl _) c ≪≫ ρ_ _
  let e₁ : (((Scheme.Modules.pushforward f).obj (tensorModule M L)).val.obj (.op U)) ≅
      (P).val.obj (.op U) :=
    (ModuleCat.restrictScalars (f.app U).hom).mapIso
      ((asIso (T.app (.op W))).symm ≪≫ tensorIso (Iso.refl _) d ≪≫ ρ_ _)
  let β := (projectionPresheaf f M N).app (.op U)
  have βe : β ≫ e₁.hom = e₀.hom := by
    apply tensor_ext
    intro x y
    have h :
        β (x ⊗ₜ[Γ(Y, U)] y) =
          T.app (.op W) (x ⊗ₜ[Γ(X, W)] ηU y) := rfl
    change e₁.hom (β (x ⊗ₜ[Γ(Y, U)] y)) = e₀.hom (x ⊗ₜ[Γ(Y, U)] y)
    rw [h]
    let A : ModuleCat Γ(X, W) := M.val.obj (.op W)
    let b := (tensorIso (Iso.refl A) d).hom
    change (ρ_ A).hom (b ((asIso (T.app (.op W))).inv
        ((asIso (T.app (.op W))).hom (x ⊗ₜ[Γ(X, W)] ηU y)))) =
      e₀.hom (x ⊗ₜ[Γ(Y, U)] y)
    rw [Iso.hom_inv_id_apply]
    let x' : Γ(M, W) := x
    exact congrArg (fun r : Γ(X, W) ↦ r • x') (hcoord y)
  have hβ : IsIso β := (isIso_comp_right_iff β e₁.hom).mp
    (βe ▸ inferInstanceAs (IsIso e₀.hom))
  have hpre : IsIso ((tensorToSheaf P N).app (.op U)) := tensorUnitIsoApp U t
  have hp : IsIso ((projectionMap f M N).val.app (.op U)) := by
    rw [← isIso_comp_left_iff ((tensorToSheaf P N).app (.op U))]
    change IsIso ((tensorToSheaf P N ≫ (projectionMap f M N).val).app (.op U))
    rw [projectionMap_precompose]
    exact hβ
  exact Functor.map_isIso (forget₂ (ModuleCat Γ(Y, U)) Ab.{u})
    ((projectionMap f M N).val.app (.op U))

private lemma trivialOnSmallerOpen {U V : Y.Opens} (h : V ≤ U)
    (t : N.restrict U.ι ≅ structureModule U.toScheme) :
    Nonempty (N.restrict V.ι ≅ structureModule V.toScheme) := by
  let j := Y.homOfLE h
  let e := Scheme.Modules.restrictFunctorCongr
    (show V.ι = j ≫ U.ι from (Y.homOfLE_ι h).symm)
  exact ⟨e.app N ≪≫ (Scheme.Modules.restrictFunctorComp j U.ι).app N ≪≫
    (Scheme.Modules.restrictFunctor j).mapIso t ≪≫ Scheme.Modules.restrictUnitIso j⟩

theorem projectionFormula : ProjectionFormula.{u} := by
  intro X Y f M N h
  let I := {U : Y.Opens // Nonempty (N.restrict U.ι ≅ structureModule U.toScheme)}
  have hI : Opens.IsBasis (Set.range (Subtype.val : I → Y.Opens)) := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨U, hxU, ⟨t⟩⟩ := h x
    refine ⟨U ⊓ W, ⟨⟨U ⊓ W, trivialOnSmallerOpen N inf_le_left t⟩, rfl⟩,
      ⟨hxU, hx⟩, inf_le_right⟩
  have : IsIso (projectionMap f M N) := isIsoOnBasis (projectionMap f M N)
    (Subtype.val : I → Y.Opens) hI (fun i ↦ by
      obtain ⟨t⟩ := i.property
      exact projectionMap_isIso_app f M N i.val t)
  exact ⟨asIso (projectionMap f M N), projectionMap_isProjectionMap f M N⟩

end Projection

end LinearAlgebraicGroups.LinePushforwardProjection
