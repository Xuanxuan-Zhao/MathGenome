import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits hiding pullback
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.EquivariantAffineModules
open Specs.EquivariantCoherentClosedImage
open Specs.CharacterDescent (Character)
open EquivariantAffineModules
open SheafOfModules Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- Restrict a sheaf direct image to an open by first restricting the sheaf
to the inverse image open and then taking the restricted direct image. -/
def restrictPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
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
/-- Direct image along an isomorphism agrees with restriction along its inverse. -/
def pushforwardIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Scheme.Modules.pushforward f ≅ restrictFunctor (inv f) := by
  let P := Scheme.Modules.pushforward f
  let Q := Scheme.Modules.pushforward (inv f)
  let R := restrictFunctor (inv f)
  exact (Functor.rightUnitor P).symm ≪≫
    Functor.isoWhiskerLeft P (restrictFunctorAdjCounitIso (inv f)).symm ≪≫
    (Functor.associator P Q R).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp f (inv f) ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id f) ≪≫
      Scheme.Modules.pushforwardId X) R ≪≫ Functor.leftUnitor R

set_option backward.isDefEq.respectTransparency false in
private theorem pushforward_isQuasicoherent_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((pushforwardIsoRestrict f).app M).symm
    (Scheme.Modules.isQuasicoherent_restrictFunctor (inv f) M)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem affine_pushforward_isQuasicoherent {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  let e := X.isoSpec
  let d := Y.isoSpec
  let F := (Scheme.Modules.pushforward e.hom).obj M
  have hF : F.IsQuasicoherent := pushforward_isQuasicoherent_of_isIso e.hom M
  let g := Spec.map f.appTop
  let G := (Scheme.Modules.pushforward g).obj F
  have hG : G.IsQuasicoherent := by
    apply (isQuasicoherent_iff_isIso_fromTildeΓ G).mpr
    exact isIso_fromTildeΓ_pushforward f.appTop F
  let N := (Scheme.Modules.pushforward d.inv).obj G
  have hN : N.IsQuasicoherent := pushforward_isQuasicoherent_of_isIso d.inv G
  have hf : (e.hom ≫ g) ≫ d.inv = f := by
    change (X.isoSpec.hom ≫ Spec.map f.appTop) ≫ Y.isoSpec.inv = f
    rw [Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let E : N ≅ (Scheme.Modules.pushforward f).obj M :=
    (Scheme.Modules.pushforward d.inv).mapIso ((Scheme.Modules.pushforwardComp e.hom g).app M) ≪≫
      (Scheme.Modules.pushforwardComp (e.hom ≫ g) d.inv).app M ≪≫
      (Scheme.Modules.pushforwardCongr hf).app M
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso E hN


section ClosedCoherence

open LinearAlgebraicGroups.ProjectiveFiniteness (finite_closed_pushforward_sections)
open private fromSpecSectionTopIso presentationRestrict_isFinite
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

set_option backward.isDefEq.respectTransparency false in
private theorem exists_finite_presentation_tilde {R : CommRingCat.{u}}
    [IsNoetherianRing R] (G : ModuleCat.{u} R) [Module.Finite R G] :
    ∃ P : (tilde G).Presentation, P.IsFinite := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R G).FG)
  let l := Finsupp.linearCombination R (fun a : (s : Set G) => a.val)
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (LinearMap.ker l)
  let P := presentationTilde G (s : Set G) hs (t : Set ((s : Set G) →₀ R)) ht
  refine ⟨P, ?_⟩
  constructor
  · constructor
    change Finite (↥(s : Set G))
    infer_instance
  · constructor
    change Finite (↥(t : Set ((s : Set G) →₀ R)))
    infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem exists_finite_presentation_spec {R : CommRingCat.{u}}
    [IsNoetherianRing R] (N : (Spec R).Modules) [N.IsQuasicoherent]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj N)] :
    ∃ P : N.Presentation, P.IsFinite := by
  obtain ⟨P, hP⟩ := exists_finite_presentation_tilde ((moduleSpecΓFunctor (R := R)).obj N)
  have hIso : IsIso (Scheme.Modules.fromTildeΓ (R := R) N) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ (R := R) N).mp inferInstance
  exact ⟨P.ofIsIso (Scheme.Modules.fromTildeΓ (R := R) N), inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_finite_presentation_fromSpec
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (M : Y.Modules) {U : Y.Opens}
    (hU : IsAffineOpen U) [(M.restrict U.ι).IsQuasicoherent]
    [Module.Finite Γ(Y, U) Γ(M, U)] :
    ∃ P : (M.restrict hU.fromSpec).Presentation, P.IsFinite := by
  let R := Γ(Y, U)
  let i := hU.isoSpec.inv
  let N := M.restrict hU.fromSpec
  let G := (moduleSpecΓFunctor (R := R)).obj N
  have hN : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      ((restrictFunctorComp i U.ι).app M).symm
      (Scheme.Modules.isQuasicoherent_restrictFunctor i (M.restrict U.ι))
  have hR : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hG : Module.Finite R G := Module.Finite.equiv (fromSpecSectionTopIso hU M).symm
  exact @exists_finite_presentation_spec R hR N hN hG

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_on_affine_open
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (M : Y.Modules) {U : Y.Opens}
    (hU : IsAffineOpen U) [(M.restrict U.ι).IsQuasicoherent]
    [Module.Finite Γ(Y, U) Γ(M, U)] :
    ∃ P : (M.over U).Presentation, P.IsFinite := by
  let N := M.restrict hU.fromSpec
  obtain ⟨Q, hQ⟩ := exists_finite_presentation_fromSpec M hU
  let r := hU.isoSpec.hom
  let Q' := presentationRestrict r Q
  have hQ' : Q'.IsFinite := presentationRestrict_isFinite r N Q
  have hr : r ≫ hU.fromSpec = U.ι := hU.isoSpec_hom_fromSpec
  let e := ((restrictFunctorComp r hU.fromSpec).app M).symm ≪≫
    (restrictFunctorCongr hr).app M
  let D := overEquiv U
  let d : D.inverse.obj (N.restrict r) ≅ M.over U :=
    D.inverse.mapIso (e ≪≫ ((overFunctorEquiv U).app M).symm) ≪≫ (D.unitIso.app _).symm
  let unitComparison := (U.sheafOfModulesEquivOverInverseUnit Y.ringCatSheaf).symm
  let P' := Q'.map D.inverse unitComparison
  have hP' : P'.IsFinite := by
    constructor
    · constructor
      change Finite (Q'.map D.inverse unitComparison).generators.I
      rw [Presentation.map_generators_I]
      exact GeneratingSections.IsFiniteType.finite
    · constructor
      change Finite (Q'.map D.inverse unitComparison).relations.I
      rw [Presentation.map_relations_I]
      exact GeneratingSections.IsFiniteType.finite
  exact ⟨P'.ofIsIso d.hom, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- Direct image of a finitely presented sheaf under a closed immersion into a
locally Noetherian scheme has a finite local presentation. -/
theorem closedPushforward_finitePresentation
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation := by
  let N := (Scheme.Modules.pushforward f).obj M
  have h (U : Y.affineOpens) : ∃ P : (N.over U.val).Presentation, P.IsFinite := by
    let V := f ⁻¹ᵁ U.val
    have hU : IsAffine U.val.toScheme := U.property
    have hV : IsAffine V.toScheme := U.property.preimage f
    have hN : (N.restrict U.val.ι).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent U.val.toScheme.ringCatSheaf).prop_of_iso
        ((restrictPushforwardIso f U.val).app M).symm
        (affine_pushforward_isQuasicoherent (f ∣_ U.val) (M.restrict V.ι))
    have hF : Module.Finite Γ(Y, U.val) Γ(N, U.val) :=
      finite_closed_pushforward_sections f M U.property
    exact finitePresentation_on_affine_open N U.property
  choose P hP using h
  let D : N.QuasicoherentData :=
    { I := Y.affineOpens
      X := Subtype.val
      coversTop := (Opens.coversTop_iff _ _).mpr (iSup_affineOpens_eq_top Y)
      presentation := P }
  have hD : D.IsFinitePresentation := by
    constructor
    intro i
    exact hP i
  exact SheafOfModules.IsFinitePresentation.mk (M := N) ⟨D, hD⟩

end ClosedCoherence

section BaseChange

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {V Z S X : Scheme.{u}} {j : V ⟶ S} {v : V ⟶ Z}
  {p : S ⟶ X} {i : Z ⟶ X}

private def pullbackSquareNatIso (w : j ≫ p = v ≫ i) :
    Scheme.Modules.pullback p ⋙ Scheme.Modules.pullback j ≅ Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback v :=
by
  let e₁ : Scheme.Modules.pullback p ⋙ Scheme.Modules.pullback j ≅ Scheme.Modules.pullback (j ≫ p) := Scheme.Modules.pullbackComp j p
  let e₂ : Scheme.Modules.pullback (j ≫ p) ≅ Scheme.Modules.pullback (v ≫ i) := Scheme.Modules.pullbackCongr w
  let e₃ : Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback v ≅ Scheme.Modules.pullback (v ≫ i) := Scheme.Modules.pullbackComp v i
  exact (e₁ ≪≫ e₂) ≪≫ e₃.symm

/-- The canonical Scheme.Modules.pullback comparison in a commutative square. -/
def pullbackSquareIso (w : j ≫ p = v ≫ i) (F : X.Modules) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback p).obj F) ≅ (Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback i).obj F) :=
  (pullbackSquareNatIso w).app F

/-- The base-change transformation, obtained by transposing the Scheme.Modules.pullback square. -/
def directImageBaseChangeNat (w : j ≫ p = v ≫ i) :
    pushforward i ⋙ Scheme.Modules.pullback p ⟶ Scheme.Modules.pullback v ⋙ pushforward j :=
  mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction i) (Scheme.Modules.pullbackPushforwardAdjunction j)
    (pullbackSquareNatIso w).hom

abbrev directImageBaseChange (w : j ≫ p = v ≫ i) (H : Z.Modules) :=
  (directImageBaseChangeNat w).app H

theorem directImageBaseChange_counit (w : j ≫ p = v ≫ i) (H : Z.Modules) :
    (Scheme.Modules.pullback j).map (directImageBaseChange w H) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction j).counit.app ((Scheme.Modules.pullback v).obj H) =
      (pullbackSquareIso w _).hom ≫ (Scheme.Modules.pullback v).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app H) :=
  mateEquiv_counit _ _ (pullbackSquareNatIso w).hom H

theorem directImageBaseChange_natural (w : j ≫ p = v ≫ i)
    {H K : Z.Modules} (m : H ⟶ K) :
    (Scheme.Modules.pullback p).map ((pushforward i).map m) ≫ directImageBaseChange w K =
      directImageBaseChange w H ≫ (pushforward j).map ((Scheme.Modules.pullback v).map m) :=
  (directImageBaseChangeNat w).naturality m

theorem directImageBaseChange_unit (w : j ≫ p = v ≫ i) (F : X.Modules) :
    (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F) ≫
        directImageBaseChange w ((Scheme.Modules.pullback i).obj F) =
      (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app ((Scheme.Modules.pullback p).obj F) ≫
        (pushforward j).map (pullbackSquareIso w F).hom :=
  unit_mateEquiv _ _ (pullbackSquareNatIso w).hom F

set_option backward.isDefEq.respectTransparency false in
theorem pullSection_counit (i : Z ⟶ X) (H : Z.Modules) (s : Γ(H, ⊤)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app H).app ⊤
      (pullSection i ((pushforward i).obj H) s) = s := by
  have eq := (Scheme.Modules.pullbackPushforwardAdjunction i).right_triangle_components H
  exact congrArg (fun g : (pushforward i).obj H ⟶ (pushforward i).obj H => g.app ⊤ s) eq

set_option backward.isDefEq.respectTransparency false in
theorem pullbackSquareIso_section (w : j ≫ p = v ≫ i) (F : X.Modules) (s : Γ(F, ⊤)) :
    (pullbackSquareIso w F).hom.app ⊤
      (pullSection j ((Scheme.Modules.pullback p).obj F) (pullSection p F s)) =
        pullSection v ((Scheme.Modules.pullback i).obj F) (pullSection i F s) := by
  let e := (Scheme.Modules.pullbackComp v i).app F
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).1
  calc
    e.hom.app ⊤ ((pullbackSquareIso w F).hom.app ⊤ _) =
        ((Scheme.Modules.pullbackCongr w).app F).hom.app ⊤
          (((Scheme.Modules.pullbackComp j p).app F).hom.app ⊤
            (pullSection j ((Scheme.Modules.pullback p).obj F) (pullSection p F s))) := by
      have h : (pullbackSquareIso w F).hom ≫ e.hom =
          ((Scheme.Modules.pullbackComp j p).app F).hom ≫ ((Scheme.Modules.pullbackCongr w).app F).hom := by
        simp [pullbackSquareIso, pullbackSquareNatIso, e]
      let s' := pullSection j ((Scheme.Modules.pullback p).obj F) (pullSection p F s)
      exact congrArg (fun (f : (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback p).obj F) ⟶
          (Scheme.Modules.pullback (v ≫ i)).obj F) => f.app ⊤ s') h
    _ = pullSection (v ≫ i) F s := by
      have hj : ((Scheme.Modules.pullbackComp j p).app F).hom.app ⊤
          (pullSection j ((Scheme.Modules.pullback p).obj F) (pullSection p F s)) =
        pullSection (j ≫ p) F s := pullSection_comp j p F s
      rw [hj]
      exact pullSection_congr w F s
    _ = e.hom.app ⊤ (pullSection v ((Scheme.Modules.pullback i).obj F) (pullSection i F s)) :=
      (pullSection_comp v i F s).symm

set_option backward.isDefEq.respectTransparency false in
theorem directImageBaseChange_section (w : j ≫ p = v ≫ i) (H : Z.Modules) (s : Γ(H, ⊤)) :
    (directImageBaseChange w H).app ⊤
      (pullSection p ((pushforward i).obj H) s) = pullSection v H s := by
  let F := (pushforward i).obj H
  let c := (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app H
  let A := Scheme.Modules.pullbackPushforwardAdjunction j
  let f := (pullbackSquareIso w F).hom ≫ (Scheme.Modules.pullback v).map c
  let e := A.homEquiv ((Scheme.Modules.pullback p).obj F) ((Scheme.Modules.pullback v).obj H)
  have hm : directImageBaseChange w H = e f := by
    apply e.symm.injective
    rw [Equiv.symm_apply_apply]
    calc
      e.symm (directImageBaseChange w H) =
          (Scheme.Modules.pullback j).map (directImageBaseChange w H) ≫ A.counit.app _ :=
        A.homEquiv_counit _ _ (directImageBaseChange w H)
      _ = f := directImageBaseChange_counit w H
  change _ = _ at hm
  rw [hm]
  dsimp only [e]
  rw [Adjunction.homEquiv_unit]
  change ((Scheme.Modules.pullback v).map c).app ⊤
    ((pullbackSquareIso w F).hom.app ⊤
      (pullSection j ((Scheme.Modules.pullback p).obj F) (pullSection p F s))) = _
  rw [pullbackSquareIso_section]
  let t := pullSection i F s
  exact (pullSection_naturality v c t).symm.trans
    (congrArg (pullSection v H) (pullSection_counit i H s))

end BaseChange

section PullbackCoherence

set_option backward.isDefEq.respectTransparency false in
private theorem opensMap_final {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Opens.map f.base).Final where
  out U := by
    let z : StructuredArrow U (Opens.map f.base) :=
      StructuredArrow.mk (Y := (⊤ : X.Opens)) (homOfLE (by simp))
    apply isConnected_of_isTerminal _ (x := z)
    refine IsTerminal.ofUniqueHom (fun V => ?_) (fun V m => ?_)
    · exact StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _)
    · apply StructuredArrow.hom_ext
      exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
private theorem exists_finitePresentation_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) (P : M.Presentation) [P.IsFinite] :
    ∃ Q : ((Scheme.Modules.pullback f).obj M).Presentation, Q.IsFinite := by
  let _ : (Opens.map f.base).Final := opensMap_final f
  let e : unit Y.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj (unit X.ringCatSheaf) :=
    (asIso (pullbackObjUnitToUnit f.toRingCatSheafHom)).symm
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  refine ⟨P.map (Scheme.Modules.pullback f) e, ?_⟩
  constructor
  · constructor
    change Finite (P.map (Scheme.Modules.pullback f) e).generators.I
    rw [Presentation.map_generators_I]
    exact GeneratingSections.IsFiniteType.finite
  · constructor
    change Finite (P.map (Scheme.Modules.pullback f) e).relations.I
    rw [Presentation.map_relations_I]
    exact GeneratingSections.IsFiniteType.finite

set_option backward.isDefEq.respectTransparency false in
private theorem exists_finitePresentation_invImage
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (P : (M.over U).Presentation) [P.IsFinite] :
    ∃ Q : (((Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U)).Presentation, Q.IsFinite := by
  let E := (overEquiv U).functor
  let P' := P.map E (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm
  have hP' : P'.IsFinite :=
    ⟨⟨(show Finite P.generators.I from GeneratingSections.IsFiniteType.finite)⟩,
      ⟨(show Finite P.relations.I from GeneratingSections.IsFiniteType.finite)⟩⟩
  let P'' := P'.ofIsIso ((overFunctorEquiv U).app M).hom
  let V := f ⁻¹ᵁ U
  let g := f ∣_ U
  obtain ⟨Q, hQ⟩ := exists_finitePresentation_pullback g (M.restrict U.ι) P''
  let e : (Scheme.Modules.pullback g).obj (M.restrict U.ι) ≅ ((Scheme.Modules.pullback f).obj M).restrict V.ι :=
    (Scheme.Modules.pullback g).mapIso ((restrictFunctorIsoPullback U.ι).app M) ≪≫
      (pullbackSquareIso (morphismRestrict_ι f U) M) ≪≫
      (restrictFunctorIsoPullback V.ι).symm.app ((Scheme.Modules.pullback f).obj M)
  let D := overEquiv V
  let d : D.inverse.obj ((Scheme.Modules.pullback g).obj (M.restrict U.ι)) ≅ ((Scheme.Modules.pullback f).obj M).over V :=
    D.inverse.mapIso (e ≪≫ ((overFunctorEquiv V).app ((Scheme.Modules.pullback f).obj M)).symm) ≪≫
      (D.unitIso.app _).symm
  let v := (V.sheafOfModulesEquivOverInverseUnit Y.ringCatSheaf).symm
  let Q' := Q.map D.inverse v
  have hQ' : Q'.IsFinite := by
    constructor
    · constructor
      change Finite (Q.map D.inverse v).generators.I
      rw [Presentation.map_generators_I]
      exact GeneratingSections.IsFiniteType.finite
    · constructor
      change Finite (Q.map D.inverse v).relations.I
      rw [Presentation.map_relations_I]
      exact GeneratingSections.IsFiniteType.finite
  exact ⟨Q'.ofIsIso d.hom, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- Inverse image preserves finite local presentations. -/
theorem pullback_finitePresentation {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) [M.IsFinitePresentation] : ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  obtain ⟨P, hP⟩ := IsFinitePresentation.exists_quasicoherentData M
  let U (i : P.I) := f ⁻¹ᵁ P.X i
  have hU : IsOpenCover U := f.iSup_preimage_eq_top ((Opens.coversTop_iff _ P.X).mp P.coversTop).iSup_eq_top
  have h (i : P.I) : ∃ Q : (((Scheme.Modules.pullback f).obj M).over (U i)).Presentation, Q.IsFinite := by
    have := hP.isFinite_presentation i
    exact exists_finitePresentation_invImage f M (P.X i) (P.presentation i)
  choose Q hQ using h
  let D : ((Scheme.Modules.pullback f).obj M).QuasicoherentData :=
    { I := P.I
      X := U
      coversTop := (Opens.coversTop_iff _ U).mpr hU
      presentation := Q }
  have hD : D.IsFinitePresentation := by
    constructor
    intro i
    exact hQ i
  exact SheafOfModules.IsFinitePresentation.mk (M := (Scheme.Modules.pullback f).obj M) ⟨D, hD⟩

end PullbackCoherence

/-- The direct image of a short exact sequence under a closed immersion is short exact. -/
theorem closedPushforward_shortExact {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (S : ShortComplex Z.Modules) (hS : S.ShortExact) :
    (S.map (pushforward i)).ShortExact := by
  have := LinearAlgebraicGroups.ProjectiveFiniteness.pushforward_preservesHomology_of_isClosedImmersion i
  have : PreservesFiniteColimits (pushforward i) := Functor.preservesFiniteColimits_of_preservesHomology _
  exact hS.map_of_exact (pushforward i)


section AffineBaseChange

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open private pullSection_bijective_of_isIso pullback_spec_isQuasicoherent from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

private abbrev topModule {X : Scheme.{u}} (F : X.Modules) : ModuleCat.{u} Γ(X, ⊤) :=
  F.val.obj (op ⊤)

private theorem isoSpec_inv_appTop (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  apply (cancel_epi X.isoSpec.hom.appTop).mp
  rw [← Scheme.Hom.comp_appTop, X.isoSpec.inv_hom_id, Scheme.Hom.id_appTop]
  change 𝟙 _ = X.toSpecΓ.appTop ≫ _
  rw [Scheme.toSpecΓ_appTop, Iso.hom_inv_id]

private def sectionsIsoSpec (X : Scheme.{u}) [IsAffine X] (F : X.Modules) :
    topModule F ≅ (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj
      ((Scheme.Modules.pullback X.isoSpec.inv).obj F) := by
  let M := topModule F
  let N := (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj
      ((Scheme.Modules.pullback X.isoSpec.inv).obj F)
  let f : M →ₗ[Γ(X, ⊤)] N :=
    { toFun := pullSection X.isoSpec.inv F
      map_add' := fun x y =>
        (((Scheme.Modules.pullbackPushforwardAdjunction X.isoSpec.inv).unit.app F).app ⊤).hom.map_add x y
      map_smul' := fun r x => by
        change pullSection X.isoSpec.inv F (r • x) =
          (Scheme.ΓSpecIso Γ(X, ⊤)).inv r • pullSection X.isoSpec.inv F x
        rw [pullSection_smul, isoSpec_inv_appTop] }
  exact (LinearEquiv.ofBijective f (pullSection_bijective_of_isIso X.isoSpec.inv F)).toModuleIso

private theorem pullback_open_isQuasicoherent {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj F).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback f).app F) (isQuasicoherent_restrictFunctor f F)

private theorem affine_pullbackSections {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] :
    ∃ e : topModule ((Scheme.Modules.pullback f).obj F) ≅
        (ModuleCat.extendScalars.{u,u,u} f.appTop.hom).obj (topModule F),
      ∀ s : topModule F, e.hom (pullSection f F s) =
        (ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app (topModule F) s := by
  let g := Spec.map f.appTop
  let G := (Scheme.Modules.pullback X.isoSpec.inv).obj F
  let P := ModuleCat.extendScalars.{u,u,u} f.appTop.hom
  let D := ModuleCat.extendRestrictScalarsAdj f.appTop.hom
  let eX := sectionsIsoSpec X F
  let eY := sectionsIsoSpec Y ((Scheme.Modules.pullback f).obj F)
  let Γ' := moduleSpecΓFunctor (R := Γ(Y, ⊤))
  have : G.IsQuasicoherent := pullback_open_isQuasicoherent _ F
  obtain ⟨e, he⟩ := affineSectionBaseChange f.appTop G
  have w : Y.isoSpec.inv ≫ f = g ≫ X.isoSpec.inv := (Scheme.isoSpec_inv_naturality f).symm
  let E := Γ'.mapIso (pullbackSquareIso w F)
  refine ⟨eY ≪≫ E ≪≫ e ≪≫ P.mapIso eX.symm, fun s => ?_⟩
  change P.map eX.inv (e.hom ((pullbackSquareIso w F).hom.app ⊤
      (pullSection Y.isoSpec.inv ((Scheme.Modules.pullback f).obj F) (pullSection f F s)))) = _
  rw [pullbackSquareIso_section w F s]
  change P.map eX.inv (e.hom (pullSection g G (eX.hom s))) = _
  rw [he]
  have h := congrArg (fun v => v (eX.hom s)) (D.unit.naturality eX.inv)
  change (D.unit.app (topModule F)) (eX.inv (eX.hom s)) =
    P.map eX.inv ((D.unit.app _) (eX.hom s)) at h
  rw [← h]
  congr 1
  exact congrArg (fun v : topModule F ⟶ topModule F => v s) eX.hom_inv_id

private theorem affine_isQuasicoherent_pullback {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj F).IsQuasicoherent := by
  let i := X.isoSpec.inv
  let j := Y.isoSpec.inv
  let g := Spec.map f.appTop
  let G := (Scheme.Modules.pullback i).obj F
  have hG : G.IsQuasicoherent := pullback_open_isQuasicoherent i F
  have w : j ≫ f = g ≫ i := (Scheme.isoSpec_inv_naturality f).symm
  have e := pullbackSquareIso w F
  have hP : ((Scheme.Modules.pullback g).obj G).IsQuasicoherent := by
    exact pullback_spec_isQuasicoherent f.appTop G
  have Q : ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback f).obj F)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(Y, ⊤)).ringCatSheaf).prop_of_iso e.symm hP
  have hj : ((Scheme.Modules.pullback Y.isoSpec.hom).obj ((Scheme.Modules.pullback j).obj
      ((Scheme.Modules.pullback f).obj F))).IsQuasicoherent := by
    exact pullback_open_isQuasicoherent Y.isoSpec.hom _
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pullbackComp Y.isoSpec.hom j).app _) ≪≫
      ((Scheme.Modules.pullbackCongr Y.isoSpec.hom_inv_id).app _) ≪≫ ((Scheme.Modules.pullbackId Y).app _)) hj

private theorem affine_isIso_of_top {X : Scheme.{u}} [IsAffine X] {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (m : F ⟶ G) [IsIso (m.app ⊤)] :
    IsIso m := by
  let P := Scheme.Modules.pullback X.isoSpec.inv
  let D := Scheme.Modules.pullback X.isoSpec.hom
  let Γ' := moduleSpecΓFunctor (R := Γ(X, ⊤))
  let eF := sectionsIsoSpec X F
  let eG := sectionsIsoSpec X G
  let f : topModule F ⟶ topModule G := m.val.app (op ⊤)
  have hf : IsIso f := (ConcreteCategory.isIso_iff_bijective f).2 ((ConcreteCategory.isIso_iff_bijective (m.app ⊤)).1 inferInstance)
  have eq : eF.hom ≫ Γ'.map (P.map m) = f ≫ eG.hom := by
    ext s
    exact (pullSection_naturality X.isoSpec.inv m s).symm
  have h : IsIso (Γ'.map (P.map m)) := IsIso.of_isIso_fac_left eq
  let adj := tilde.adjunction (R := Γ(X, ⊤))
  have hF : (P.obj F).IsQuasicoherent := pullback_open_isQuasicoherent _ F
  have hG : (P.obj G).IsQuasicoherent := pullback_open_isQuasicoherent _ G
  have : IsIso (adj.counit.app (P.obj F))  := (isQuasicoherent_iff_isIso_fromTildeΓ (P.obj F)).mp hF
  have : IsIso (adj.counit.app (P.obj G))  := (isQuasicoherent_iff_isIso_fromTildeΓ (P.obj G)).mp hG
  have : IsIso ((moduleSpecΓFunctor ⋙ tilde.functor Γ(X, ⊤)).map (P.map m)) :=
    (tilde.functor Γ(X, ⊤)).map_isIso (Γ'.map (P.map m))
  have : IsIso (P.map m) := IsIso.of_isIso_fac_left (adj.counit.naturality (P.map m)).symm
  let c : P ⋙ D ≅ 𝟭 _ := Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv ≪≫
    Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id ≪≫ Scheme.Modules.pullbackId X
  have : IsIso ((P ⋙ D).map m) := D.map_isIso (P.map m)
  exact IsIso.of_isIso_fac_left (c.hom.naturality m).symm

open scoped TensorProduct

private theorem extendScalars_pushout {R S A B : CommRingCat.{u}}
    {p : R ⟶ S} {i : R ⟶ A} {j : S ⟶ B} {v : A ⟶ B}
    (sq : CategoryTheory.IsPushout p i j v) (M : ModuleCat.{u} A) :
    ∃ e : (ModuleCat.extendScalars.{u,u,u} p.hom).obj ((ModuleCat.restrictScalars i.hom).obj M) ≅
        (ModuleCat.restrictScalars j.hom).obj ((ModuleCat.extendScalars.{u,u,u} v.hom).obj M),
      ∀ m : M,
        e.hom ((ModuleCat.extendRestrictScalarsAdj p.hom).unit.app
          ((ModuleCat.restrictScalars i.hom).obj M) m) =
        (ModuleCat.extendRestrictScalarsAdj v.hom).unit.app M m := by
  let : Algebra R S := p.hom.toAlgebra
  let : Algebra R A := i.hom.toAlgebra
  let : Algebra S B := j.hom.toAlgebra
  let : Algebra A B := v.hom.toAlgebra
  let : Algebra R B := (p ≫ j).hom.toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom sq.w)
  let : Algebra.IsPushout R S A B := CommRingCat.isPushout_iff_isPushout.mp sq
  let : Module R M := Module.compHom M i.hom
  let : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let E := (Algebra.IsPushout.cancelBaseChange R S A B M).symm
  let e : (ModuleCat.extendScalars.{u,u,u} p.hom).obj ((ModuleCat.restrictScalars i.hom).obj M) ≅
      (ModuleCat.restrictScalars j.hom).obj ((ModuleCat.extendScalars.{u,u,u} v.hom).obj M) :=
    E.toModuleIso
  refine ⟨e, fun m => ?_⟩
  change E ((1 : S) ⊗ₜ[R] m) = (1 : B) ⊗ₜ[A] m
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one]

private theorem directImageBaseChange_isIso_affine
    {V Z S X : Scheme.{u}} [IsAffine S] [IsAffine X] [IsAffine Z]
    {j : V ⟶ S} {v : V ⟶ Z} {p : S ⟶ X} {i : Z ⟶ X}
    (sq : IsPullback j v p i) (H : Z.Modules) [H.IsQuasicoherent] :
    IsIso (directImageBaseChange sq.w H) := by
  let F := (Scheme.Modules.pushforward i).obj H
  let G := (Scheme.Modules.pullback v).obj H
  let A := (Scheme.Modules.pullback p).obj F
  let B := (Scheme.Modules.pushforward j).obj G
  let m := directImageBaseChange sq.w H
  have : IsAffine V := .of_isPullback sq
  have : F.IsQuasicoherent := affine_pushforward_isQuasicoherent i H
  have : G.IsQuasicoherent := affine_isQuasicoherent_pullback v H
  have : A.IsQuasicoherent := affine_isQuasicoherent_pullback p F
  have : B.IsQuasicoherent := affine_pushforward_isQuasicoherent j G
  obtain ⟨e, he⟩ := affine_pullbackSections p F
  obtain ⟨d, hd⟩ := affine_pullbackSections v H
  obtain ⟨b, hb⟩ := extendScalars_pushout (isPushout_appTop_of_isPullback sq) (topModule H)
  let d' := (ModuleCat.restrictScalars j.appTop.hom).mapIso d
  let m' : topModule A ⟶ topModule B := m.val.app (op ⊤)
  have eq : e.inv ≫ m' ≫ d'.hom = b.hom := by
    apply (ModuleCat.extendRestrictScalarsAdj p.appTop.hom).homEquiv _ _ |>.injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply ModuleCat.hom_ext
    ext s
    have hs : e.inv ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).unit.app (topModule F) s) =
        pullSection p F s := by
      rw [← he s]
      exact congrArg (fun g : topModule A ⟶ topModule A => g (pullSection p F s)) e.hom_inv_id
    change d.hom (m.app ⊤ (e.inv ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).unit.app
      (topModule F) s))) = b.hom ((ModuleCat.extendRestrictScalarsAdj p.appTop.hom).unit.app
        (topModule F) s)
    rw [hs, directImageBaseChange_section sq.w H s]
    exact (hd s).trans (hb s).symm
  have : IsIso (e.inv ≫ m' ≫ d'.hom) := eq ▸ inferInstanceAs (IsIso b.hom)
  have : IsIso (m' ≫ d'.hom) := IsIso.of_isIso_comp_left e.inv (m' ≫ d'.hom)
  have hm' : IsIso m' := IsIso.of_isIso_comp_right m' d'.hom
  have hm : IsIso (m.app ⊤) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ((ConcreteCategory.isIso_iff_bijective m').1 hm')
  exact @affine_isIso_of_top S _ A B ‹A.IsQuasicoherent› ‹B.IsQuasicoherent› m hm

end AffineBaseChange

section BaseChangeOpen

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

private theorem openPullback_unit_isIso_app {S X : Scheme.{u}} (p : S ⟶ X)
    [IsOpenImmersion p] (F : X.Modules) (W : S.Opens) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).app (p ''ᵁ W)) := by
  let P := Scheme.Modules.pushforward p
  let e := restrictFunctorIsoPullback p
  have h := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction p)
    (Scheme.Modules.pullbackPushforwardAdjunction p) F
  let U := p ''ᵁ W
  have he : p ''ᵁ (p ⁻¹ᵁ U) = U := congrArg (p ''ᵁ ·) (p.preimage_image_eq W)
  have hu : IsIso (((restrictAdjunction p).unit.app F).app U) := by
    rw [restrictAdjunction_unit_app_app]
    have hmap : homOfLE (p.image_preimage_le U) = (eqToIso he).hom := Subsingleton.elim _ _
    rw [hmap]
    infer_instance
  have h' := congrArg (fun f => Scheme.Modules.Hom.app f U) h
  change ((restrictAdjunction p).unit.app F).app U ≫ (P.map (e.hom.app F)).app U = _ at h'
  rw [← h']
  infer_instance

private theorem directImageBaseChange_isIso_open {V Z S X : Scheme.{u}}
    {j : V ⟶ S} {v : V ⟶ Z} {p : S ⟶ X} {i : Z ⟶ X}
    [IsOpenImmersion p] [IsOpenImmersion v] (sq : IsPullback j v p i) (H : Z.Modules) :
    IsIso (directImageBaseChange sq.w H) := by
  let adjP := Scheme.Modules.pullbackPushforwardAdjunction p
  let adjV := Scheme.Modules.pullbackPushforwardAdjunction v
  let α := (pullbackSquareNatIso sq.w).hom
  let β := directImageBaseChangeNat sq.w
  let doubledMate := (mateEquiv adjV adjP) β
  have hMate : IsIso doubledMate := by
    change IsIso ((mateEquiv adjV adjP) ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction i)
      (Scheme.Modules.pullbackPushforwardAdjunction j)) α))
    rw [iterated_mateEquiv_conjugateEquiv]
    infer_instance
  let F := (Scheme.Modules.pushforward i).obj H
  let G := (Scheme.Modules.pullback v).obj H
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  let U := p ''ᵁ W
  have h := unit_mateEquiv adjV adjP β H
  have h' := congrArg (fun f => Scheme.Modules.Hom.app f U) h
  change (adjV.unit.app H).app (i ⁻¹ᵁ U) ≫ (doubledMate.app G).app U =
    (adjP.unit.app F).app U ≫ (β.app H).app (p ⁻¹ᵁ U) at h'
  have hU : v ''ᵁ (j ⁻¹ᵁ W) = i ⁻¹ᵁ U :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq W
  have : IsIso ((adjV.unit.app H).app (i ⁻¹ᵁ U)) := by
    rw [← hU]
    exact openPullback_unit_isIso_app v H _
  have : IsIso ((adjP.unit.app F).app U) := openPullback_unit_isIso_app p F W
  have : IsIso ((adjP.unit.app F).app U ≫ (β.app H).app (p ⁻¹ᵁ U)) := h' ▸ inferInstance
  have t : IsIso ((β.app H).app (p ⁻¹ᵁ U)) := IsIso.of_isIso_comp_left ((adjP.unit.app F).app U) ((β.app H).app (p ⁻¹ᵁ U))
  exact (p.preimage_image_eq W) ▸ t

end BaseChangeOpen

section Pastings

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

local notation "P" => Scheme.Modules.pullback
local notation "Q" => Scheme.Modules.pushforward
local notation "C" => Scheme.Modules.pullbackComp
local notation "E" => Scheme.Modules.pullbackCongr
local notation "adj" => Scheme.Modules.pullbackPushforwardAdjunction

@[reassoc]
private theorem schemePullComp_assoc {W V U X : Scheme.{u}}
    (f : W ⟶ V) (g : V ⟶ U) (h : U ⟶ X) (F : X.Modules) :
    (P f).map ((C g h).hom.app F) ≫ (C f (g ≫ h)).hom.app F =
      (C f g).hom.app ((P h).obj F) ≫ (C (f ≫ g) h).hom.app F ≫
        (E (Category.assoc f g h)).hom.app F := by
  have h₀ := congrArg (fun τ => NatTrans.app τ F)
    (Scheme.Modules.pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at h₀
  have hInv : (C f (g ≫ h)).inv.app F ≫ (P f).map ((C g h).inv.app F) ≫
      (C f g).hom.app ((P h).obj F) ≫ (C (f ≫ g) h).hom.app F =
      (E (Category.assoc f g h)).inv.app F := by
    simpa only [Scheme.Modules.pullbackCongr, eqToIso.inv, eqToHom_app] using h₀
  calc
    _ = (P f).map ((C g h).hom.app F) ≫ (C f (g ≫ h)).hom.app F ≫
        ((C f (g ≫ h)).inv.app F ≫ (P f).map ((C g h).inv.app F) ≫
          (C f g).hom.app ((P h).obj F) ≫ (C (f ≫ g) h).hom.app F) ≫
        (E (Category.assoc f g h)).hom.app F := by
          rw [hInv, Iso.inv_hom_id_app, Category.comp_id]
    _ = _ := by
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← (P f).map_comp_assoc,
        Iso.hom_inv_id_app]
      rw [(P f).map_id, Category.id_comp]

@[reassoc]
private theorem schemePullCongr_trans {S X : Scheme.{u}} {f g h : S ⟶ X}
    (e : f = g) (e' : g = h) (F : X.Modules) :
    (E e).hom.app F ≫ (E e').hom.app F = (E (e.trans e')).hom.app F := by
  subst g h
  simp [Scheme.Modules.pullbackCongr]

@[reassoc]
private theorem schemePullComp_congr_left {W V U : Scheme.{u}} {f f' : W ⟶ V}
    (e : f = f') (g : V ⟶ U) (F : U.Modules) :
    (E e).hom.app ((P g).obj F) ≫ (C f' g).hom.app F =
      (C f g).hom.app F ≫ (E (congrArg (· ≫ g) e)).hom.app F := by
  subst f'
  simp [Scheme.Modules.pullbackCongr]

@[reassoc]
private theorem schemePullComp_congr_right {W V U : Scheme.{u}} (f : W ⟶ V)
    {g g' : V ⟶ U} (e : g = g') (F : U.Modules) :
    (P f).map ((E e).hom.app F) ≫ (C f g').hom.app F =
      (C f g).hom.app F ≫ (E (congrArg (f ≫ ·) e)).hom.app F := by
  subst g'
  simp [Scheme.Modules.pullbackCongr]

private theorem schemePullComp_congr_right_inv {W V U : Scheme.{u}} (f : W ⟶ V)
    {g g' : V ⟶ U} (e : g = g') (F : U.Modules) :
    (C f g).inv.app F ≫ (P f).map ((E e).hom.app F) =
      (E (congrArg (f ≫ ·) e)).hom.app F ≫ (C f g').inv.app F := by
  apply (cancel_mono ((C f g').hom.app F)).mp
  simp only [Category.assoc, schemePullComp_congr_right, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Category.comp_id]

private theorem schemePullComp_assoc_inv {W V U X : Scheme.{u}}
    (f : W ⟶ V) (g : V ⟶ U) (h : U ⟶ X) (F : X.Modules) :
    (C f (g ≫ h)).inv.app F ≫ (P f).map ((C g h).inv.app F) ≫
        (C f g).hom.app ((P h).obj F) =
      (E (Category.assoc f g h).symm).hom.app F ≫ (C (f ≫ g) h).inv.app F := by
  have h₀ := congrArg (fun τ => NatTrans.app τ F)
    (Scheme.Modules.pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at h₀
  apply (cancel_mono ((C (f ≫ g) h).hom.app F)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  simpa only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app] using h₀

variable {W V Z R S X : Scheme.{u}}
    {l : W ⟶ R} {u' : W ⟶ V} {j : V ⟶ S} {v : V ⟶ Z}
    {q : R ⟶ S} {p : S ⟶ X} {i : Z ⟶ X}

private theorem pullbackSquareIso_paste (h₁ : l ≫ q = u' ≫ j) (h₂ : j ≫ p = v ≫ i)
    (w : l ≫ q ≫ p = (u' ≫ v) ≫ i) (F : X.Modules) :
    (P l).map ((C q p).hom.app F) ≫ (pullbackSquareIso w F).hom =
      (pullbackSquareIso h₁ ((P p).obj F)).hom ≫
        (P u').map (pullbackSquareIso h₂ F).hom ≫ (C u' v).hom.app ((P i).obj F) := by
  change (P l).map ((C q p).hom.app F) ≫
    ((C l (q ≫ p)).hom.app F ≫ (E w).hom.app F) ≫ (C (u' ≫ v) i).inv.app F =
    (((C l q).hom.app ((P p).obj F) ≫ (E h₁).hom.app ((P p).obj F)) ≫
      (C u' j).inv.app ((P p).obj F)) ≫
    (P u').map (((C j p).hom.app F ≫ (E h₂).hom.app F) ≫ (C v i).inv.app F) ≫
      (C u' v).hom.app ((P i).obj F)
  simp only [Functor.map_comp, Category.assoc, schemePullComp_assoc_assoc,
    schemePullCongr_trans_assoc]
  have ha : (P u').map ((C j p).hom.app F) =
      (C u' j).hom.app ((P p).obj F) ≫ (C (u' ≫ j) p).hom.app F ≫
      (E (Category.assoc u' j p)).hom.app F ≫ (C u' (j ≫ p)).inv.app F := by
    apply (cancel_mono ((C u' (j ≫ p)).hom.app F)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact schemePullComp_assoc u' j p F
  rw [reassoc_of% ha]
  simp only [Iso.inv_hom_id_app_assoc, schemePullComp_congr_left_assoc,
    reassoc_of% schemePullComp_congr_right_inv, schemePullComp_assoc_inv,
    schemePullCongr_trans_assoc]

private theorem directImageBaseChange_paste (h₁ : l ≫ q = u' ≫ j) (h₂ : j ≫ p = v ≫ i)
    (w : l ≫ q ≫ p = (u' ≫ v) ≫ i) (H : Z.Modules) :
    (C q p).hom.app ((Q i).obj H) ≫ directImageBaseChange w H =
      (P q).map (directImageBaseChange h₂ H) ≫
        directImageBaseChange h₁ ((P v).obj H) ≫ (Q l).map ((C u' v).hom.app H) := by
  apply ((adj l).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.counit_naturality, directImageBaseChange_counit,
    reassoc_of% directImageBaseChange_counit]
  have nat := (pullbackSquareNatIso h₁).hom.naturality (directImageBaseChange h₂ H)
  change (P l).map ((P q).map (directImageBaseChange h₂ H)) ≫
    (pullbackSquareIso h₁ _).hom =
      (pullbackSquareIso h₁ _).hom ≫ (P u').map ((P j).map (directImageBaseChange h₂ H)) at nat
  rw [reassoc_of% nat, ← (P u').map_comp_assoc, directImageBaseChange_counit h₂,
    Functor.map_comp, Category.assoc]
  have hc := (C u' v).hom.naturality ((adj i).counit.app H)
  change (P u').map ((P v).map ((adj i).counit.app H)) ≫ (C u' v).hom.app H =
    (C u' v).hom.app ((P i).obj ((Q i).obj H)) ≫ (P (u' ≫ v)).map ((adj i).counit.app H) at hc
  rw [hc, ← reassoc_of% pullbackSquareIso_paste h₁ h₂ w]

private theorem directImageBaseChange_paste_isIso_iff
    (h₁ : l ≫ q = u' ≫ j) (h₂ : j ≫ p = v ≫ i)
    (w : l ≫ q ≫ p = (u' ≫ v) ≫ i) (H : Z.Modules)
    [IsIso (directImageBaseChange h₁ ((P v).obj H))] :
    IsIso (directImageBaseChange w H) ↔ IsIso ((P q).map (directImageBaseChange h₂ H)) := by
  let e := (C q p).hom.app ((Q i).obj H)
  let m := directImageBaseChange w H
  let n := (P q).map (directImageBaseChange h₂ H)
  let d := directImageBaseChange h₁ ((P v).obj H) ≫ (Q l).map ((C u' v).hom.app H)
  have hd : IsIso d := by dsimp only [d]; infer_instance
  have h : e ≫ m = n ≫ d := directImageBaseChange_paste h₁ h₂ w H
  constructor
  · intro hm
    have : IsIso (n ≫ d) := h ▸ inferInstanceAs (IsIso (e ≫ m))
    exact IsIso.of_isIso_comp_right n d
  · intro hn
    have : IsIso (e ≫ m) := h.symm ▸ inferInstanceAs (IsIso (n ≫ d))
    exact IsIso.of_isIso_comp_left e m

private theorem directImageBaseChange_isIso_congr {V Z S X : Scheme.{u}}
    {j : V ⟶ S} {v v' : V ⟶ Z} {p p' : S ⟶ X} {i : Z ⟶ X}
    (w : j ≫ p = v ≫ i) (w' : j ≫ p' = v' ≫ i) (hp : p = p') (hv : v = v') (H : Z.Modules) :
    IsIso (directImageBaseChange w H) ↔ IsIso (directImageBaseChange w' H) := by
  subst p' v'
  rfl

end Pastings

section AffineLocality

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

private theorem affineBaseChange_isIso_on_open {V Z S X : Scheme.{u}}
    {j : V ⟶ S} {v : V ⟶ Z} {p : S ⟶ X} {i : Z ⟶ X} [IsAffineHom i]
    (sq : IsPullback j v p i) (H : Z.Modules) [H.IsQuasicoherent]
    {U : X.Opens} {W : S.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (hWU : W ≤ p ⁻¹ᵁ U) :
    IsIso ((Scheme.Modules.pullback W.ι).map (directImageBaseChange sq.w H)) := by
  let sqW := isPullback_morphismRestrict j W
  let right := isPullback_morphismRestrict i U
  let outer := (sqW.flip.paste_horiz sq.flip).flip
  let r := p.resLE U W hWU
  have hr : r ≫ U.ι = W.ι ≫ p := Scheme.Hom.resLE_comp_ι p hWU
  have outer' : IsPullback ((j ∣_ W)) ((j ⁻¹ᵁ W).ι ≫ v) (r ≫ U.ι) i := by
    rw [hr]
    exact outer
  have hs : ((j ⁻¹ᵁ W).ι ≫ v) ≫ i = ((j ∣_ W) ≫ r) ≫ U.ι :=
    outer'.w.symm.trans (Category.assoc _ _ _).symm
  let s := right.flip.lift ((j ⁻¹ᵁ W).ι ≫ v) ((j ∣_ W) ≫ r) hs
  have h₁ : s ≫ (i ⁻¹ᵁ U).ι = (j ⁻¹ᵁ W).ι ≫ v := right.flip.lift_fst _ _ _
  have h₂ : s ≫ (i ∣_ U) = (j ∣_ W) ≫ r := right.flip.lift_snd _ _ _
  have localSq : IsPullback (j ∣_ W) s r (i ∣_ U) :=
    (IsPullback.of_right (h₁.symm ▸ outer'.flip) h₂ right.flip).flip
  have : IsAffine W.toScheme := hW
  have : IsAffine U.toScheme := hU
  have : IsAffine (i ⁻¹ᵁ U).toScheme := hU.preimage i
  have hH : ((Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).obj H).IsQuasicoherent :=
    pullback_open_isQuasicoherent (i ⁻¹ᵁ U).ι H
  have : IsIso (directImageBaseChange localSq.w
      ((Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).obj H)) :=
    directImageBaseChange_isIso_affine localSq _
  have hi : IsIso (directImageBaseChange right.w H) :=
    directImageBaseChange_isIso_open right H
  have hc : IsIso (directImageBaseChange
      (j := j ∣_ W) (p := r ≫ U.ι) (v := s ≫ (i ⁻¹ᵁ U).ι)
        ((localSq.flip.paste_horiz right.flip).flip.w) H) :=
    (directImageBaseChange_paste_isIso_iff localSq.w right.w
      ((localSq.flip.paste_horiz right.flip).flip.w) H).mpr
      (Functor.map_isIso (Scheme.Modules.pullback r) _)
  have ho : IsIso (directImageBaseChange outer.w H) :=
    (directImageBaseChange_isIso_congr _ outer.w hr h₁ H).mp hc
  have hj : IsIso (directImageBaseChange sqW.w ((Scheme.Modules.pullback v).obj H)) :=
    directImageBaseChange_isIso_open sqW _
  exact (directImageBaseChange_paste_isIso_iff sqW.w sq.w outer.w H).mp ho

private theorem isIso_of_open_restrictions {S : Scheme.{u}} {A B : S.Modules} (m : A ⟶ B)
    {basis : Set S.Opens} (hbasis : Opens.IsBasis basis)
    (h : ∀ W ∈ basis, IsIso ((Scheme.Modules.pullback (Scheme.Opens.ι W)).map m)) : IsIso m := by
  let G := SheafOfModules.toSheaf S.ringCatSheaf
  have eBasis : Set.range (Subtype.val : basis → S.Opens) = basis := by simp
  have hG : IsIso (G.map m) := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis (B := (Subtype.val : basis → S.Opens))
      (φ := G.map m) (by rwa [eBasis]) ?_
    intro W
    have := h W.val W.property
    let e := restrictFunctorIsoPullback W.val.ι
    have hr : IsIso ((restrictFunctor W.val.ι).map m) :=
      IsIso.of_isIso_fac_right (e.hom.naturality m)
    have ht : IsIso (((restrictFunctor W.val.ι).map m).app ⊤) := inferInstance
    change IsIso (m.app W.val)
    have ht' : IsIso (m.app (W.val.ι ''ᵁ ⊤)) := ht
    exact W.val.ι_image_top ▸ ht'
  apply (isIso_iff_of_reflects_iso m (Scheme.Modules.toPresheaf S)).mp
  exact (TopCat.Sheaf.forget Ab S.carrier).map_isIso (G.map m)

/-- The inverse image of the direct image of a quasi-coherent sheaf under an
affine morphism is canonically the direct image on the base changed scheme. -/
theorem affineDirectImageBaseChange_isIso {V Z S X : Scheme.{u}}
    {j : V ⟶ S} {v : V ⟶ Z} {p : S ⟶ X} {i : Z ⟶ X} [IsAffineHom i]
    (sq : IsPullback j v p i) (H : Z.Modules) [H.IsQuasicoherent] :
    IsIso (directImageBaseChange sq.w H) := by
  let basis : Set S.Opens :=
    {W | IsAffineOpen W ∧ ∃ U : X.Opens, IsAffineOpen U ∧ W ≤ p ⁻¹ᵁ U}
  have hb : Opens.IsBasis basis := by
    rw [Opens.isBasis_iff_nbhd]
    intro V x hx
    have hAffine {Y : Scheme.{u}} {N : Y.Opens} {y : Y} (hy : y ∈ N) :
        ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ N :=
      Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hy
    have hxTop : p x ∈ (⊤ : X.Opens) := by trivial
    obtain ⟨U, hU, hxU, -⟩ := hAffine hxTop
    have hxVU : x ∈ V ⊓ p ⁻¹ᵁ U := ⟨hx, hxU⟩
    obtain ⟨W, hW, hxW, hWV⟩ := hAffine hxVU
    exact ⟨W, ⟨hW, U, hU, hWV.trans inf_le_right⟩, hxW, hWV.trans inf_le_left⟩
  apply isIso_of_open_restrictions _ hb
  rintro W ⟨hW, U, hU, hWU⟩
  exact affineBaseChange_isIso_on_open sq H hU hW hWU

end AffineLocality

section ActionSquares

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

open private equivariant_actOn
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k] {T : GroupScheme k}
  {X Z S W : SchemeOver k} {a : ModObj T.X X} {b : ModObj T.X Z} {i : Z ⟶ X}

@[reassoc]
private theorem actOn_precomp (j : W ⟶ S) (t : S ⟶ T.X) (x : S ⟶ X) :
    j ≫ actOn a t x = actOn a (j ≫ t) (j ≫ x) := by
  unfold actOn
  rw [← Category.assoc, comp_lift]

private theorem actOn_inv_cancel (t : S ⟶ T.X) (x : S ⟶ X) :
    actOn a t⁻¹ (actOn a t x) = x := by
  let := a
  exact inv_smul_smul t x

private theorem actOn_cancel_inv (t : S ⟶ T.X) (x : S ⟶ X) :
    actOn a t (actOn a t⁻¹ x) = x := by
  let := a
  exact smul_inv_smul t x

private theorem actionPullbackCondition (hi : IsEquivariantMap a b i)
    (j : W ⟶ S) (y : W ⟶ Z) (t : S ⟶ T.X) (x : S ⟶ X) (e : j ≫ x = y ≫ i) :
    j ≫ actOn a t x = actOn b (j ≫ t) y ≫ i := by
  rw [actOn_precomp, e, equivariant_actOn hi]

private theorem actionTest_isPullback (hi : IsEquivariantMap a b i)
    {j : W ⟶ S} {y : W ⟶ Z} {x : S ⟶ X} (sq : IsPullback j y x i)
    (t : S ⟶ T.X) : IsPullback j (actOn b (j ≫ t) y) (actOn a t x) i := by
  refine IsPullback.mk' (actionPullbackCondition hi j y t x sq.w) ?_ ?_
  · intro U f g hj hact
    apply sq.hom_ext hj
    rw [actOn_precomp, actOn_precomp, ← Category.assoc, ← Category.assoc, hj] at hact
    exact (actOn_inv_cancel (a := b) (g ≫ j ≫ t) (f ≫ y)).symm.trans
      ((congrArg (actOn b (g ≫ j ≫ t)⁻¹) hact).trans
      (actOn_inv_cancel (g ≫ j ≫ t) (g ≫ y)))
  · intro U f z h
    have hz : f ≫ x = actOn b (f ≫ t)⁻¹ z ≫ i := by
      rw [← equivariant_actOn hi, ← h, actOn_precomp, actOn_inv_cancel]
    refine ⟨sq.lift f (actOn b (f ≫ t)⁻¹ z) hz, sq.lift_fst _ _ _, ?_⟩
    rw [actOn_precomp, ← Category.assoc, sq.lift_fst, sq.lift_snd, actOn_cancel_inv]

private abbrev productMap (i : Z ⟶ X) : T.X ⊗ Z ⟶ T.X ⊗ X := 𝟙 T.X ⊗ₘ i

private theorem projection_isPullback (i : Z ⟶ X) :
    IsPullback (productMap (T := T) i) (snd T.X Z) (snd T.X X) i := by
  refine IsPullback.mk' (by simp [productMap]) ?_ ?_
  · intro Y f g hj hz
    apply CartesianMonoidalCategory.hom_ext
    · simpa [productMap] using congrArg (· ≫ fst T.X X) hj
    · exact hz
  · intro Y f z hz
    refine ⟨lift (f ≫ fst T.X X) z, ?_, by simp⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp [productMap]
    · simpa [productMap] using hz.symm

private theorem action_isPullback (hi : IsEquivariantMap a b i) :
    IsPullback (productMap (T := T) i) b.smul a.smul i := by
  simpa [productMap, actOn] using
    actionTest_isPullback hi (projection_isPullback (T := T) i) (fst T.X X)

private theorem overPullback_left {A B C D : SchemeOver k}
    {j : A ⟶ B} {v : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    (sq : IsPullback j v p i) : IsPullback j.left v.left p.left i.left :=
  (Over.forget _).map_isPullback sq

end ActionSquares

section Transport

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open private comparePull evalPullIso equivariant_actOn pullCongr_refl pullCongr_trans
  pullCongr_naturality transport_eq_evalPullIso pullback_map_evalPullIso_to
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k] {T : GroupScheme k}
  {X Z S W : SchemeOver k} {a : ModObj T.X X} {b : ModObj T.X Z} {i : Z ⟶ X}

local notation "P" f => Scheme.Modules.pullback (Over.Hom.left f)

@[reassoc]
private theorem comparePull_naturality {V : SchemeOver k} {F H : X.left.Modules}
    (f : W ⟶ V) (g : V ⟶ X) {h : W ⟶ X} (e : f ≫ g = h)
    (m : F ⟶ H) :
    (comparePull F f g e).hom ≫ (P h).map m =
      (P f).map ((P g).map m) ≫ (comparePull H f g e).hom := by
  simp only [comparePull, Iso.trans_hom, Category.assoc, pullCongr_naturality]
  rw [← Category.assoc]
  exact congrArg (· ≫ (pullCongr H e).hom)
    (((Scheme.Modules.pullbackComp f.left g.left).hom.naturality m).symm)

@[reassoc]
private theorem comparePull_inv_naturality {V : SchemeOver k} {F H : X.left.Modules}
    (f : W ⟶ V) (g : V ⟶ X) {h : W ⟶ X} (e : f ≫ g = h)
    (m : F ⟶ H) :
    (comparePull F f g e).inv ≫ (P f).map ((P g).map m) =
      (P h).map m ≫ (comparePull H f g e).inv := by
  apply (cancel_mono (comparePull H f g e).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← comparePull_naturality, Iso.inv_hom_id_assoc]

@[reassoc]
private theorem evalPullIso_naturality {V : SchemeOver k} {F H : X.left.Modules}
    {p q : V ⟶ X} {x y : W ⟶ X}
    (L : Pull p F ≅ Pull q F) (K : Pull p H ≅ Pull q H)
    (m : F ⟶ H) (hm : L.hom ≫ (P q).map m = (P p).map m ≫ K.hom)
    (s : W ⟶ V) (hp : s ≫ p = x) (hq : s ≫ q = y) :
    (evalPullIso L s hp hq).hom ≫ (P y).map m =
      (P x).map m ≫ (evalPullIso K s hp hq).hom := by
  simp only [evalPullIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    comparePull_naturality, ← Functor.map_comp_assoc]
  rw [hm, Functor.map_comp, Category.assoc, comparePull_inv_naturality_assoc]

@[reassoc]
private theorem transport_naturality {F H : X.left.Modules}
    (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (K : Pull (snd T.X X) H ≅ Pull a.smul H) (m : F ⟶ H)
    (hm : L.hom ≫ (P a.smul).map m = (P (snd T.X X)).map m ≫ K.hom)
    (t : W ⟶ T.X) (x : W ⟶ X) :
    (transport a L t x).hom ≫ (P (actOn a t x)).map m =
      (P x).map m ≫ (transport a K t x).hom := by
  rw [transport_eq_evalPullIso, transport_eq_evalPullIso]
  exact evalPullIso_naturality L K m hm (lift t x) (lift_snd _ _) rfl

@[reassoc]
private theorem transport_precomp {F : X.left.Modules}
    (L : Pull (snd T.X X) F ≅ Pull a.smul F) (j : W ⟶ S)
    (t : S ⟶ T.X) (x : S ⟶ X) {x' : W ⟶ X} (e : j ≫ x = x') :
    (P j).map (transport a L t x).hom ≫
      (comparePull F j (actOn a t x) ((actOn_precomp j t x).trans (congrArg (actOn a (j ≫ t)) e))).hom =
    (comparePull F j x e).hom ≫ (transport a L (j ≫ t) x').hom := by
  rw [transport_eq_evalPullIso, transport_eq_evalPullIso]
  refine pullback_map_evalPullIso_to L (lift t x) (lift_snd _ _) rfl j ?_ e _ (lift_snd _ _) rfl
  exact (comp_lift j t x).trans (congrArg (lift (j ≫ t)) e)

private abbrev imageSheaf (i : Z ⟶ X) (H : Z.left.Modules) :=
  (Scheme.Modules.pushforward i.left).obj H

private abbrev imageCounit (i : Z ⟶ X) (H : Z.left.Modules) :
    Pull i (imageSheaf i H) ⟶ H :=
  (Scheme.Modules.pullbackPushforwardAdjunction i.left).counit.app H

private def counitOnFiber {H : Z.left.Modules} {j : W ⟶ S} {x : S ⟶ X} {y : W ⟶ Z}
    (e : j ≫ x = y ≫ i) : Pull j (Pull x (imageSheaf i H)) ⟶ Pull y H :=
  (comparePull (imageSheaf i H) j x e).hom ≫
    (pullComp (imageSheaf i H) y i).inv ≫ (P y).map (imageCounit i H)

@[reassoc]
private theorem counitOnFiber_congr {H : Z.left.Modules} {j : W ⟶ S}
    {x x' : S ⟶ X} {y y' : W ⟶ Z} (e : j ≫ x = y ≫ i) (e' : j ≫ x' = y' ≫ i)
    (hx : x = x') (hy : y = y') :
    (P j).map (pullCongr (imageSheaf i H) hx).hom ≫ counitOnFiber (H := H) e' =
      counitOnFiber e ≫ (pullCongr H hy).hom := by
  subst x' y'
  simp only [pullCongr_refl]
  rw [(P j).map_id, Category.id_comp, Category.comp_id]

private theorem counit_transport {H : Z.left.Modules} (hi : IsEquivariantMap a b i)
    (L : Pull (snd T.X X) (imageSheaf i H) ≅ Pull a.smul (imageSheaf i H))
    (K : Pull (snd T.X Z) H ≅ Pull b.smul H)
    (h : (pullbackLinearizationIso hi L).hom ≫ (P b.smul).map (imageCounit i H) =
      (P (snd T.X Z)).map (imageCounit i H) ≫ K.hom)
    (t : W ⟶ T.X) (y : W ⟶ Z) :
    (pullComp (imageSheaf i H) y i).hom ≫ (transport a L t (y ≫ i)).hom ≫
      (pullCongr (imageSheaf i H) (equivariant_actOn hi)).hom ≫
      (pullComp (imageSheaf i H) (actOn b t y) i).inv ≫
      (P (actOn b t y)).map (imageCounit i H) =
    (P y).map (imageCounit i H) ≫ (transport b K t y).hom := by
  calc
    _ = (transport b (pullbackLinearizationIso hi L) t y).hom ≫
          (P (actOn b t y)).map (imageCounit i H) := by
      rw [← pullbackLinearization_transport_assoc, Iso.hom_inv_id_assoc]
    _ = _ := transport_naturality (a := b) _ K (imageCounit i H) h t y

set_option maxHeartbeats 1000000 in
private theorem counitOnFiber_transport {H : Z.left.Modules}
    (hi : IsEquivariantMap a b i)
    (L : Pull (snd T.X X) (imageSheaf i H) ≅ Pull a.smul (imageSheaf i H))
    (K : Pull (snd T.X Z) H ≅ Pull b.smul H)
    (h : (pullbackLinearizationIso hi L).hom ≫ (P b.smul).map (imageCounit i H) =
      (P (snd T.X Z)).map (imageCounit i H) ≫ K.hom)
    {j : W ⟶ S} {x : S ⟶ X} {y : W ⟶ Z} (e : j ≫ x = y ≫ i) (t : S ⟶ T.X) :
    (P j).map (transport a L t x).hom ≫ counitOnFiber (H := H) (actionPullbackCondition hi j y t x e) =
      counitOnFiber e ≫ (transport b K (j ≫ t) y).hom := by
  let F := imageSheaf i H
  let s := j ≫ t
  let c := imageCounit i H
  let z := actOn b s y
  let d := (actOn_precomp (a := a) j t x).trans (congrArg (actOn a s) e)
  have transCompare :
      (comparePull F j (actOn a t x) (actionPullbackCondition hi j y t x e)).hom =
      (comparePull F j (actOn a t x) d).hom ≫ (pullCongr F (equivariant_actOn hi)).hom := by
    simp only [comparePull, Iso.trans_hom, Category.assoc, pullCongr_trans]
  unfold counitOnFiber
  rw [transCompare, Category.assoc, transport_precomp_assoc L j t x e]
  have ht := counit_transport hi L K h s y
  have ht' := congrArg (fun f : Pull y (Pull i F) ⟶ Pull z H =>
    (pullComp F y i).inv ≫ f) ht
  exact congrArg (fun f : Pull (y ≫ i) F ⟶ Pull z H => (comparePull F j x e).hom ≫ f)
    (((pullComp F y i).inv_hom_id_assoc _).symm.trans ht')

end Transport

section Linearization

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open private evalPullIso comparePull from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k] {T : GroupScheme k}
  {X Z S W : SchemeOver k} {a : ModObj T.X X} {b : ModObj T.X Z} {i : Z ⟶ X}

local notation "P" f => Scheme.Modules.pullback (Over.Hom.left f)
local notation "Q" f => Scheme.Modules.pushforward (Over.Hom.left f)
local notation "adj" f => Scheme.Modules.pullbackPushforwardAdjunction (Over.Hom.left f)

private theorem counitOnFiber_injective [IsAffineHom i.left]
    (H : Z.left.Modules) [H.IsQuasicoherent]
    {j : W ⟶ S} {x : S ⟶ X} {y : W ⟶ Z} (sq : IsPullback j y x i)
    (M : S.left.Modules) :
    Function.Injective (fun f : M ⟶ Pull x (imageSheaf i H) =>
      (P j).map f ≫ counitOnFiber (H := H) sq.w) := by
  let sq' := overPullback_left sq
  let m := directImageBaseChange sq'.w H
  have hm : IsIso m := affineDirectImageBaseChange_isIso sq' H
  have hc : (P j).map m ≫ (adj j).counit.app (Pull y H) = counitOnFiber (H := H) sq.w := by
    rw [directImageBaseChange_counit]
    simp only [counitOnFiber, comparePull, pullComp, pullCongr, pullbackSquareIso, pullbackSquareNatIso,
      Iso.app_hom, Iso.app_inv, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  intro f g e
  apply (cancel_mono m).mp
  apply ((adj j).homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, hc] using e

private theorem linearization_unit_of_eq_one {H : Z.left.Modules}
    (K : Linearization b H) (t : W ⟶ T.X) (y : W ⟶ Z) (h : t = 1)
    (e : actOn b t y = y) :
    (transport b K.iso t y).hom ≫ (pullCongr H e).hom = 𝟙 _ := by
  subst t
  exact (K.unit W y).choose_spec

private def TransportCompositionAt {H : Z.left.Modules} (K : Linearization b H) (s t r : W ⟶ T.X) (y : W ⟶ Z) : Prop :=
  ∀ (e : actOn b s (actOn b t y) = actOn b r y),
    ComposesTo (transport b K.iso t y).hom (transport b K.iso s (actOn b t y)).hom
      (pullCongr H e).hom (transport b K.iso r y).hom

private theorem linearization_mul_at_product {H : Z.left.Modules} (K : Linearization b H)
    (s t : W ⟶ T.X) (y : W ⟶ Z) :
    TransportCompositionAt K s t (s * t) y := fun _ => (K.mul W s t y).choose_spec

private theorem linearization_mul_of_eq_mul {H : Z.left.Modules} (K : Linearization b H)
    (s t r : W ⟶ T.X) (y : W ⟶ Z) (h : r = s * t)
    (e : actOn b s (actOn b t y) = actOn b r y) :
    (transport b K.iso t y).hom ≫ (transport b K.iso s (actOn b t y)).hom ≫
        (pullCongr H e).hom = (transport b K.iso r y).hom := by
  have hc : TransportCompositionAt K s t r y := Eq.mpr (congrArg (fun z => TransportCompositionAt K s t z y) h)
    (linearization_mul_at_product K s t y)
  exact hc e

private theorem imageLinearization_unit [IsAffineHom i.left]
    {H : Z.left.Modules} [H.IsQuasicoherent] (hi : IsEquivariantMap a b i)
    (L : Pull (snd T.X X) (imageSheaf i H) ≅ Pull a.smul (imageSheaf i H))
    (K : Linearization b H)
    (h : (pullbackLinearizationIso hi L).hom ≫ (P b.smul).map (imageCounit i H) =
      (P (snd T.X Z)).map (imageCounit i H) ≫ K.iso.hom)
    (S : SchemeOver k) (x : S ⟶ X) :
    ∃ e : actOn a (1 : S ⟶ T.X) x = x,
      (transport a L 1 x).hom ≫ (pullCongr (imageSheaf i H) e).hom = 𝟙 _ := by
  let := a
  let j := CategoryTheory.Limits.pullback.fst x i
  let y := CategoryTheory.Limits.pullback.snd x i
  have sq : IsPullback j y x i := IsPullback.of_hasPullback x i
  have h1 : j ≫ (1 : S ⟶ T.X) = 1 := MonObj.comp_one j
  have e : actOn a (1 : S ⟶ T.X) x = x := one_smul (S ⟶ T.X) x
  let sq1 := actionTest_isPullback hi sq (1 : S ⟶ T.X)
  have ey' : actOn b (j ≫ (1 : S ⟶ T.X)) y = y := by
    rw [h1]
    exact (K.unit _ y).choose
  have hy' := linearization_unit_of_eq_one K _ y h1 ey'
  refine ⟨e, counitOnFiber_injective H sq _ ?_⟩
  simp only [Functor.map_comp, Category.assoc]
  rw [(P j).map_id, Category.id_comp, counitOnFiber_congr sq1.w sq.w e ey']
  slice_lhs 1 2 => rw [counitOnFiber_transport hi L K.iso h sq.w (1 : S ⟶ T.X)]
  rw [Category.assoc, hy', Category.comp_id]

private theorem imageLinearization_mul [IsAffineHom i.left]
    {H : Z.left.Modules} [H.IsQuasicoherent] (hi : IsEquivariantMap a b i)
    (L : Pull (snd T.X X) (imageSheaf i H) ≅ Pull a.smul (imageSheaf i H))
    (K : Linearization b H)
    (h : (pullbackLinearizationIso hi L).hom ≫ (P b.smul).map (imageCounit i H) =
      (P (snd T.X Z)).map (imageCounit i H) ≫ K.iso.hom)
    (S : SchemeOver k) (s t : S ⟶ T.X) (x : S ⟶ X) :
    ∃ e : actOn a s (actOn a t x) = actOn a (s * t) x, TransportComposition L s t x e := by
  let := a
  let j := CategoryTheory.Limits.pullback.fst x i
  let y := CategoryTheory.Limits.pullback.snd x i
  have sq : IsPullback j y x i := IsPullback.of_hasPullback x i
  let sqT := actionTest_isPullback hi sq t
  let sqST := actionTest_isPullback hi sqT s
  let sqR := actionTest_isPullback hi sq (s * t)
  have e : actOn a s (actOn a t x) = actOn a (s * t) x := (mul_smul s t x).symm
  have hm : j ≫ (s * t) = (j ≫ s) * (j ≫ t) := MonObj.comp_mul j s t
  have ey' : actOn b (j ≫ s) (actOn b (j ≫ t) y) = actOn b (j ≫ (s * t)) y := by
    rw [hm]
    exact (K.mul _ (j ≫ s) (j ≫ t) y).choose
  have hy' := linearization_mul_of_eq_mul K _ _ _ y hm ey'
  refine ⟨e, counitOnFiber_injective H sqR _ ?_⟩
  simp only [Functor.map_comp, Category.assoc]
  rw [counitOnFiber_congr sqST.w sqR.w e ey']
  slice_lhs 2 3 => rw [counitOnFiber_transport hi L K.iso h sqT.w s]
  slice_lhs 1 2 => rw [counitOnFiber_transport hi L K.iso h sq.w t]
  rw [counitOnFiber_transport hi L K.iso h sq.w (s * t)]
  simpa only [Category.assoc] using congrArg (fun f => counitOnFiber (H := H) sq.w ≫ f) hy'

private abbrev projectionSquare (i : Z ⟶ X) :=
  overPullback_left (projection_isPullback (T := T) i)

private abbrev actionSquare (hi : IsEquivariantMap a b i) :=
  overPullback_left (action_isPullback hi)

private abbrev projectionBaseChange (i : Z ⟶ X) (H : Z.left.Modules) :=
  directImageBaseChange (projectionSquare (T := T) i).w H

private abbrev actionBaseChange (hi : IsEquivariantMap a b i) (H : Z.left.Modules) :=
  directImageBaseChange (actionSquare hi).w H

private def imageLinearizationIso [IsAffineHom i.left] (hi : IsEquivariantMap a b i)
    {H : Z.left.Modules} [H.IsQuasicoherent] (K : Linearization b H) :
    Pull (snd T.X X) (imageSheaf i H) ≅ Pull a.smul (imageSheaf i H) := by
  have : IsIso (projectionBaseChange (T := T) i H) :=
    affineDirectImageBaseChange_isIso (projectionSquare (T := T) i) H
  have : IsIso (actionBaseChange hi H) := affineDirectImageBaseChange_isIso (actionSquare hi) H
  exact asIso (projectionBaseChange i H) ≪≫ (Q (productMap i)).mapIso K.iso ≪≫
    (asIso (actionBaseChange hi H)).symm

@[reassoc]
private theorem imageLinearizationIso_comp_actionBaseChange [IsAffineHom i.left]
    (hi : IsEquivariantMap a b i) {H : Z.left.Modules} [H.IsQuasicoherent] (K : Linearization b H) :
    (imageLinearizationIso hi K).hom ≫ actionBaseChange hi H =
      projectionBaseChange i H ≫ (Q (productMap i)).map K.iso.hom := by
  simp [imageLinearizationIso]

private theorem pullbackLinearizationIso_eq_squares (hi : IsEquivariantMap a b i)
    {F : X.left.Modules} (L : Pull (snd T.X X) F ≅ Pull a.smul F) :
    (pullbackLinearizationIso hi L).hom =
      (pullbackSquareIso (projectionSquare (T := T) i).w F).inv ≫
        (P (productMap i)).map L.hom ≫ (pullbackSquareIso (actionSquare hi).w F).hom := by
  simp only [pullbackLinearizationIso, pullbackSquareIso, pullbackSquareNatIso, evalPullIso,
    comparePull, pullComp, pullCongr, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app]

private theorem imageLinearizationIso_counit [IsAffineHom i.left] (hi : IsEquivariantMap a b i)
    {H : Z.left.Modules} [H.IsQuasicoherent] (K : Linearization b H) :
    (pullbackLinearizationIso hi (imageLinearizationIso hi K)).hom ≫ (P b.smul).map (imageCounit i H) =
      (P (snd T.X Z)).map (imageCounit i H) ≫ K.iso.hom := by
  let q := productMap (T := T) i
  let cp := pullbackSquareIso (projectionSquare (T := T) i).w (imageSheaf i H)
  let ca := pullbackSquareIso (actionSquare hi).w (imageSheaf i H)
  let ep := projectionBaseChange (T := T) i H
  let ea := actionBaseChange hi H
  let L := imageLinearizationIso hi K
  let A := adj q
  have hp : (P q).map ep ≫ A.counit.app (Pull (snd T.X Z) H) =
      cp.hom ≫ (P (snd T.X Z)).map (imageCounit i H) :=
    directImageBaseChange_counit (projectionSquare (T := T) i).w H
  have ha : (P q).map ea ≫ A.counit.app (Pull b.smul H) =
      ca.hom ≫ (P b.smul).map (imageCounit i H) :=
    directImageBaseChange_counit (actionSquare hi).w H
  rw [pullbackLinearizationIso_eq_squares]
  change cp.inv ≫ (P q).map L.hom ≫ ca.hom ≫ (P b.smul).map (imageCounit i H) = _
  rw [← ha, ← (P q).map_comp_assoc, imageLinearizationIso_comp_actionBaseChange,
    Functor.map_comp, Category.assoc, A.counit_naturality, reassoc_of% hp, cp.inv_hom_id_assoc]

/-- The canonical linearization on the actual direct image. -/
def directImageLinearization [IsAffineHom i.left] (hi : IsEquivariantMap a b i)
    {H : Z.left.Modules} [H.IsQuasicoherent] (K : Linearization b H) :
    Linearization a (imageSheaf i H) where
  iso := imageLinearizationIso hi K
  unit := imageLinearization_unit hi _ K (imageLinearizationIso_counit hi K)
  mul := imageLinearization_mul hi _ K (imageLinearizationIso_counit hi K)

end Linearization

section Comparisons

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

variable {k : Type u} [Field k] {T : GroupScheme k}
  {X Z : SchemeOver k} {a : ModObj T.X X} {b : ModObj T.X Z} {i : Z ⟶ X}

local notation "P" f => Scheme.Modules.pullback (Over.Hom.left f)
local notation "Q" f => Scheme.Modules.pushforward (Over.Hom.left f)
local notation "adj" f => Scheme.Modules.pullbackPushforwardAdjunction (Over.Hom.left f)

theorem directImageLinearization_map [IsAffineHom i.left] (hi : IsEquivariantMap a b i)
    {H K : Z.left.Modules} [H.IsQuasicoherent] [K.IsQuasicoherent]
    {L : Linearization b H} {M : Linearization b K} {m : H ⟶ K} (hm : IsLinearizedMap L M m) :
    IsLinearizedMap (directImageLinearization hi L) (directImageLinearization hi M) ((Q i).map m) := by
  have : IsIso (actionBaseChange hi K) := affineDirectImageBaseChange_isIso (actionSquare hi) K
  change (imageLinearizationIso hi L).hom ≫ (P a.smul).map ((Q i).map m) =
    (P (snd T.X X)).map ((Q i).map m) ≫ (imageLinearizationIso hi M).hom
  apply (cancel_mono (actionBaseChange hi K)).mp
  change L.iso.hom ≫ (P b.smul).map m = (P (snd T.X Z)).map m ≫ M.iso.hom at hm
  let q := productMap (T := T) i
  let er := projectionBaseChange (T := T) i H
  let em := projectionBaseChange (T := T) i K
  let ed := actionBaseChange hi H
  let ek := actionBaseChange hi K
  let La := imageLinearizationIso hi L
  let Ma := imageLinearizationIso hi M
  have hp : (P (snd T.X X)).map ((Q i).map m) ≫ em =
      er ≫ (Q q).map ((P (snd T.X Z)).map m) :=
    directImageBaseChange_natural (projectionSquare (T := T) i).w m
  have ha : (P a.smul).map ((Q i).map m) ≫ ek = ed ≫ (Q q).map ((P b.smul).map m) :=
    directImageBaseChange_natural (actionSquare hi).w m
  have hL : La.hom ≫ ed = er ≫ (Q q).map L.iso.hom := imageLinearizationIso_comp_actionBaseChange hi L
  have hM : Ma.hom ≫ ek = em ≫ (Q q).map M.iso.hom := imageLinearizationIso_comp_actionBaseChange hi M
  change (La.hom ≫ (P a.smul).map ((Q i).map m)) ≫ ek =
    ((P (snd T.X X)).map ((Q i).map m) ≫ Ma.hom) ≫ ek
  simp only [Category.assoc, ha, hM, reassoc_of% hL, reassoc_of% hp]
  rw [← (Q q).map_comp, hm, (Q q).map_comp]

theorem directImageLinearization_counit [IsAffineHom i.left] (hi : IsEquivariantMap a b i)
    {H : Z.left.Modules} [H.IsQuasicoherent] (L : Linearization b H) :
    IsLinearizedMap (pullbackLinearization hi (directImageLinearization hi L)) L (imageCounit i H) :=
  imageLinearizationIso_counit hi L

theorem directImageLinearization_unit [IsAffineHom i.left] (hi : IsEquivariantMap a b i)
    {F : X.left.Modules} [(Pull i F).IsQuasicoherent] (L : Linearization a F) :
    IsLinearizedMap L (directImageLinearization hi (pullbackLinearization hi L))
      ((adj i).unit.app F) := by
  let G := Pull i F
  let K := pullbackLinearization hi L
  let q := productMap (T := T) i
  let c := (adj i).unit.app F
  let cp := pullbackSquareIso (projectionSquare (T := T) i).w F
  let ca := pullbackSquareIso (actionSquare hi).w F
  let ep := projectionBaseChange (T := T) i G
  let ea := actionBaseChange hi G
  change L.iso.hom ≫ (P a.smul).map c =
      (P (snd T.X X)).map c ≫ (imageLinearizationIso hi K).hom
  have : IsIso ea := affineDirectImageBaseChange_isIso (actionSquare hi) G
  apply (cancel_mono ea).mp
  have hp : (P (snd T.X X)).map c ≫ ep =
      (adj q).unit.app (Pull (snd T.X X) F) ≫ (Q q).map cp.hom :=
    directImageBaseChange_unit (projectionSquare (T := T) i).w F
  have ha : (P a.smul).map c ≫ ea =
      (adj q).unit.app (Pull a.smul F) ≫ (Q q).map ca.hom :=
    directImageBaseChange_unit (actionSquare hi).w F
  have hK : cp.hom ≫ K.iso.hom = (P q).map L.iso.hom ≫ ca.hom := by
    change cp.hom ≫ (pullbackLinearizationIso hi L.iso).hom = _
    rw [pullbackLinearizationIso_eq_squares]
    exact cp.hom_inv_id_assoc _
  change L.iso.hom ≫ (P a.smul).map c ≫ ea =
    ((P (snd T.X X)).map c ≫ (imageLinearizationIso hi K).hom) ≫ ea
  have hN : L.iso.hom ≫ (adj q).unit.app (Pull a.smul F) =
      (adj q).unit.app (Pull (snd T.X X) F) ≫ (Q q).map ((P q).map L.iso.hom) :=
    (adj q).unit.naturality L.iso.hom
  have hLin : (imageLinearizationIso hi K).hom ≫ ea = ep ≫ (Q q).map K.iso.hom :=
    imageLinearizationIso_comp_actionBaseChange hi K
  simp only [Category.assoc, ha, hLin, reassoc_of% hN, reassoc_of% hp]
  rw [← (Q q).map_comp, ← hK, (Q q).map_comp]

private theorem productMap_character (i : Z ⟶ X) (χ : Character T) :
    (productMap i).left.appTop ((fst T.X X).left.appTop (characterFunction χ)) =
      (fst T.X Z).left.appTop (characterFunction χ) := by
  have e : productMap i ≫ fst T.X X = fst T.X Z := by simp [productMap]
  change (((productMap i).left.appTop).hom.comp ((fst T.X X).left.appTop).hom) _ = _
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ← Over.comp_left, e]

private theorem imageLinearizationIso_twist [IsAffineHom i.left] (hi : IsEquivariantMap a b i)
    {H K : Z.left.Modules} [H.IsQuasicoherent] [K.IsQuasicoherent]
    (L : Linearization b H) (M : Linearization b K) (χ : Character T) (e : H ≅ K)
    (he : M.iso.hom = (P (snd T.X Z)).map e.inv ≫ L.iso.hom ≫
      multiply _ ((fst T.X Z).left.appTop (characterFunction χ)) ≫ (P b.smul).map e.hom) :
    (imageLinearizationIso hi M).hom =
      (P (snd T.X X)).map ((Q i).map e.inv) ≫ (imageLinearizationIso hi L).hom ≫
        multiply _ ((fst T.X X).left.appTop (characterFunction χ)) ≫
        (P a.smul).map ((Q i).map e.hom) := by
  let q := productMap (T := T) i
  let c := (fst T.X X).left.appTop (characterFunction χ)
  let d := (fst T.X Z).left.appTop (characterFunction χ)
  let mp := (P (snd T.X X)).map ((Q i).map e.inv)
  let ma := (P a.smul).map ((Q i).map e.hom)
  let epH := projectionBaseChange (T := T) i H
  let epK := projectionBaseChange (T := T) i K
  let eaH := actionBaseChange hi H
  let eaK := actionBaseChange hi K
  have : IsIso eaK := affineDirectImageBaseChange_isIso (actionSquare hi) K
  have hp : mp ≫ epH = epK ≫ (Q q).map ((P (snd T.X Z)).map e.inv) :=
    directImageBaseChange_natural (projectionSquare (T := T) i).w e.inv
  have ha : ma ≫ eaK = eaH ≫ (Q q).map ((P b.smul).map e.hom) :=
    directImageBaseChange_natural (actionSquare hi).w e.hom
  have hscalar : (Q q).map (multiply (Pull b.smul H) d) = multiply ((Q q).obj (Pull b.smul H)) c := by
    have hcd : q.left.appTop c = d := productMap_character i χ
    rw [← hcd, pushforward_multiply]
  apply (cancel_mono eaK).mp
  change (imageLinearizationIso hi M).hom ≫ eaK =
    (mp ≫ (imageLinearizationIso hi L).hom ≫ multiply _ c ≫ ma) ≫ eaK
  have hL : (imageLinearizationIso hi L).hom ≫ eaH = epH ≫ (Q q).map L.iso.hom :=
    imageLinearizationIso_comp_actionBaseChange hi L
  have hM : (imageLinearizationIso hi M).hom ≫ eaK = epK ≫ (Q q).map M.iso.hom :=
    imageLinearizationIso_comp_actionBaseChange hi M
  have he' : M.iso.hom = (P (snd T.X Z)).map e.inv ≫ L.iso.hom ≫
      multiply (Pull b.smul H) d ≫ (P b.smul).map e.hom := he
  rw [hM]
  simp only [Category.assoc, ha, multiply_natural_assoc]
  rw [reassoc_of% hL, reassoc_of% hp]
  change epK ≫ (Q q).map M.iso.hom =
    epK ≫ (Q q).map ((P (snd T.X Z)).map e.inv) ≫ (Q q).map L.iso.hom ≫
      multiply ((Q q).obj (Pull b.smul H)) c ≫ (Q q).map ((P b.smul).map e.hom)
  rw [← hscalar, he']
  simp only [(Q q).map_comp]

end Comparisons

section CoherentClasses

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

open private equivariant_actOn from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k] {T : GroupScheme k}
  {X Z : SchemeOver k} {a : ModObj T.X X} {b : ModObj T.X Z} {i : Z ⟶ X}

local notation "P" f => Scheme.Modules.pullback (Over.Hom.left f)
local notation "Q" f => Scheme.Modules.pushforward (Over.Hom.left f)
local notation "adj" f => Scheme.Modules.pullbackPushforwardAdjunction (Over.Hom.left f)

/-- The coherent direct image under an equivariant closed immersion. -/
def pushCoherent [IsLocallyNoetherian X.left] [IsClosedImmersion i.left]
    (hi : IsEquivariantMap a b i) (H : EquivariantCoherent b) : EquivariantCoherent a := by
  have := H.coherent
  exact ⟨imageSheaf i H.sheaf, closedPushforward_finitePresentation i.left H.sheaf,
    directImageLinearization hi H.lin⟩

/-- The coherent inverse image with the canonical pulled-back linearization. -/
def pullCoherent (hi : IsEquivariantMap a b i) (F : EquivariantCoherent a) : EquivariantCoherent b :=
  ⟨Pull i F.sheaf, @pullback_finitePresentation _ _ i.left F.sheaf F.coherent,
    pullbackLinearization hi F.lin⟩

theorem pullCoherent_isEquivariantPullback
    (hi : IsEquivariantMap a b i) (F : EquivariantCoherent a) :
    IsEquivariantPullback i F (pullCoherent hi F) (Iso.refl _) := by
  intro S t y
  refine ⟨equivariant_actOn hi, ?_⟩
  let A := F.sheaf
  let L := pullbackLinearization hi F.lin
  let z := actOn b t y
  let cp := pullComp A y i
  let ca := pullComp A z i
  change (P y).map (𝟙 (Pull i A)) ≫ cp.hom ≫ (transport a F.lin.iso t (y ≫ i)).hom ≫
    (pullCongr A (equivariant_actOn hi)).hom ≫ ca.inv ≫ (P z).map (𝟙 (Pull i A)) =
      (transport b L.iso t y).hom
  rw [(P y).map_id (Pull i A), (P z).map_id (Pull i A), Category.id_comp, Category.comp_id]
  apply (cancel_mono ca.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (pullbackLinearization_transport hi F.lin.iso t y).symm

theorem pushCoherent_isEquivariantPushforward [IsLocallyNoetherian X.left] [IsClosedImmersion i.left]
    (hi : IsEquivariantMap a b i) (H : EquivariantCoherent b) :
    IsEquivariantPushforward i H (pushCoherent hi H) (Iso.refl _) := by
  have := H.coherent
  intro S t y
  refine ⟨equivariant_actOn hi, ?_⟩
  let F := imageSheaf i H.sheaf
  let L := (directImageLinearization hi H.lin).iso
  let e := pullComp F (actOn b t y) i
  let c := imageCounit i H.sheaf
  change (pullComp F y i).hom ≫ (transport a L t (y ≫ i)).hom ≫
    (pullCongr F (equivariant_actOn hi)).hom ≫ e.inv ≫
      (P (actOn b t y)).map (((adj i).homEquiv F H.sheaf).symm (𝟙 F)) =
    (P y).map (((adj i).homEquiv F H.sheaf).symm (𝟙 F)) ≫ (transport b H.lin.iso t y).hom
  rw [Adjunction.homEquiv_symm_id, ← pullbackLinearization_transport_assoc hi L t y,
    Iso.hom_inv_id_assoc]
  exact transport_naturality _ _ c (directImageLinearization_counit hi H.lin) t y

theorem pushCoherent_unit [IsLocallyNoetherian X.left] [IsClosedImmersion i.left]
    (hi : IsEquivariantMap a b i) (F : EquivariantCoherent a) :
    IsEquivariantOnTests F.lin (pushCoherent hi (pullCoherent hi F)).lin
      ((adj i).unit.app F.sheaf) := by
  have : (Pull i F.sheaf).IsFinitePresentation := (pullCoherent hi F).coherent
  intro S t x
  exact transport_naturality _ _ _ (directImageLinearization_unit hi F.lin) t x

theorem pushCoherent_map [IsLocallyNoetherian X.left] [IsClosedImmersion i.left]
    (hi : IsEquivariantMap a b i) {H K : EquivariantCoherent b}
    {m : H.sheaf ⟶ K.sheaf} (hm : EquivariantHom m) :
    EquivariantHom (F := pushCoherent hi H) (H := pushCoherent hi K) ((Q i).map m) := by
  have := H.coherent
  have := K.coherent
  exact directImageLinearization_map hi (L := H.lin) (M := K.lin) hm

theorem pushCoherent_isTwist [IsLocallyNoetherian X.left] [IsClosedImmersion i.left]
    (hi : IsEquivariantMap a b i) {χ : Character T} {H K : EquivariantCoherent b}
    (h : IsTwist χ H K) : IsTwist χ (pushCoherent hi H) (pushCoherent hi K) := by
  have := H.coherent
  have := K.coherent
  obtain ⟨e, he⟩ := h
  refine ⟨(Q i).mapIso e, ?_⟩
  exact imageLinearizationIso_twist hi H.lin K.lin χ e he

private theorem classOf_twist {H K : EquivariantCoherent a} {χ : Character T}
    (h : IsTwist χ H K) : classOf K = eChar χ • classOf H := by
  have hm : Finsupp.single K 1 - eChar χ • Finsupp.single H 1 ∈ relationSubmodule a :=
    Submodule.subset_span (Or.inr ⟨χ, H, K, h, rfl⟩)
  have he := LinearMap.mem_ker.mp (show _ ∈ LinearMap.ker (relationSubmodule a).mkQ by
    rw [Submodule.ker_mkQ]
    exact hm)
  simpa only [classOf, LinearMap.map_sub, LinearMap.map_smul, sub_eq_zero] using he

/-- The character-ring-linear map on coherent classes induced by closed direct image. -/
def pushClasses [IsLocallyNoetherian X.left] [IsClosedImmersion i.left]
    (hi : IsEquivariantMap a b i) : GZero b →ₗ[CharacterRing T] GZero a := by
  refine liftClassMap (fun H => classOf (pushCoherent hi H)) ?_ ?_
  · intro H K L f g w hf hg hs
    exact classOf_exact ((ShortComplex.mk f g w).map (Q i)).zero
      (pushCoherent_map hi hf) (pushCoherent_map hi hg) (closedPushforward_shortExact i.left _ hs)
  · intro χ H K h
    exact classOf_twist (pushCoherent_isTwist hi h)

@[simp]
theorem pushClasses_classOf [IsLocallyNoetherian X.left] [IsClosedImmersion i.left]
    (hi : IsEquivariantMap a b i) (H : EquivariantCoherent b) :
    pushClasses hi (classOf H) = classOf (pushCoherent hi H) := by
  unfold pushClasses
  rw [liftClassMap_classOf]

/-- The closed map on equivariant coherent classes used in localization. -/
theorem closedImage : ClosedImage.{u} := by
  intro k _ T X Z a b i _ hX _ _ _ hi he
  let : LocallyOfFiniteType X.hom := hX
  let : IsClosedImmersion i.left := hi
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let D : ClosedImageData i a b :=
    { pushCoherent := fun H => (pushCoherent he H).coherent
      pushLinearization := fun H => (pushCoherent he H).lin
      pullCoherent := fun F => (pullCoherent he F).coherent
      pullLinearization := fun F => (pullCoherent he F).lin
      pushClasses := pushClasses he }
  exact ⟨D, pullCoherent_isEquivariantPullback he, pushCoherent_isEquivariantPushforward he,
    pushCoherent_unit he, fun _ h => pushCoherent_map he h,
    fun f g w _ _ h => closedPushforward_shortExact i.left (ShortComplex.mk f g w) h,
    fun _ _ _ h => pushCoherent_isTwist he h, pushClasses_classOf he⟩

end CoherentClasses

end

end LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage
