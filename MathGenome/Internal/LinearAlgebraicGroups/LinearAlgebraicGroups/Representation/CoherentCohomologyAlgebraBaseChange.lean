import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.CoherentCohomologyAlgebraBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Order.Sum.Order

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings Simplicial

noncomputable section

universe u

namespace LinearAlgebraicGroups.Representation.CoherentCohomologyAlgebraBaseChange

open Specs.FlagCohomology
open Specs.CoherentCohomologyAlgebraBaseChange

open private pullSection pullSection_comp pullSection_open pullSection_naturality pullbackUnit_comp_app
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

section AffineOpen

variable {X Y : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

/-- Sections on an affine open can be taken after pulling back to the
spectrum of the ring of its regular functions. -/
private def affineOpenSections (F : X.Modules) :
    F.val.obj (op U) ≅
      (moduleSpecΓFunctor (R := Γ(X, U))).obj ((Scheme.Modules.pullback hU.fromSpec).obj F) := by
  let i := hU.fromSpec
  have h : (⊤ : (Spec Γ(X, U)).Opens) ≤ i ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  let w := pullSection i F U ⊤ h
  have hw : Function.Bijective w := by
    have hi : i ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
      rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
    let H (W : X.Opens) (p : (⊤ : (Spec Γ(X, U)).Opens) ≤ i ⁻¹ᵁ W) :
        Prop := Function.Bijective (pullSection i F W ⊤ p)
    have h₀ : ∀ p, H (i ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) p := by
      intro p
      dsimp only [H]
      exact pullSection_open i F (⊤ : (Spec Γ(X, U)).Opens)
    exact (congrArg (fun W => ∀ p, H W p) hi).mp h₀ h
  let l : F.val.obj (op U) →ₗ[Γ(X, U)]
      (moduleSpecΓFunctor (R := Γ(X, U))).obj ((Scheme.Modules.pullback i).obj F) :=
    { toFun := w
      map_add' := w.map_add
      map_smul' := by
        intro r s
        have hr : i.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
          rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc]
          simp only [← Functor.map_comp]
          have he : (eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h).op = 𝟙 _ :=
            Subsingleton.elim _ _
          rw [he, (Spec Γ(X, U)).presheaf.map_id, Category.comp_id]
        exact (w.map_smulₛₗ r s).trans (by
          change (i.appLE U ⊤ h) r • w s = ((Scheme.ΓSpecIso Γ(X, U)).inv r) • w s
          exact congrArg (fun (a : Γ(Spec Γ(X, U), ⊤)) => a • w s)
            (congrArg (fun (g : Γ(X, U) ⟶ Γ(Spec Γ(X, U), ⊤)) => g r) hr)) }
  exact (LinearEquiv.ofBijective l hw).toModuleIso

private theorem affineOpenSections_apply (F : X.Modules) (s : F.val.obj (op U)) :
    (affineOpenSections hU F).hom s =
      pullSection hU.fromSpec F U ⊤ hU.fromSpec_preimage_self.ge s := rfl


private theorem pullSection_preimage (f : Y ⟶ X) (F : X.Modules) (U : X.Opens)
    (s : F.val.obj (op U)) :
    pullSection f F U (f ⁻¹ᵁ U) le_rfl s =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app U s := by
  change ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE le_rfl).op _ = _
  rw [show (homOfLE (le_rfl : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U)).op = 𝟙 _ from Subsingleton.elim _ _,
    ((Scheme.Modules.pullback f).obj F).presheaf.map_id]
  rfl

private theorem pullSection_congr_open {S : Scheme.{u}} {f g : S ⟶ X} (w : f = g)
    (F : X.Modules) (U : X.Opens) (V : S.Opens)
    (p : V ≤ f ⁻¹ᵁ U) (q : V ≤ g ⁻¹ᵁ U) (s : F.val.obj (op U)) :
    ((pullbackCongr w).hom.app F).app V (pullSection f F U V p s) =
      pullSection g F U V q s := by
  subst g
  rfl

include hU in
set_option maxHeartbeats 700000 in
private theorem affineOpenPullback (f : Y ⟶ X) (hV : IsAffineOpen (f ⁻¹ᵁ U))
    (F : X.Modules) [F.IsQuasicoherent] :
    let a := (f.app U).hom
    let M := F.val.obj (op U)
    let G := (Scheme.Modules.pullback f).obj F
    ∃ e : G.val.obj (op (f ⁻¹ᵁ U)) ≅ (ModuleCat.extendScalars.{u,u,u} a).obj M,
      ∀ s : M, e.hom (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app U s) =
        (ModuleCat.extendRestrictScalarsAdj a).unit.app M s := by
  let V := f ⁻¹ᵁ U
  let i := hU.fromSpec
  let j := hV.fromSpec
  let φ := f.app U
  let g := Spec.map φ
  have w : g ≫ i = j ≫ f := by
    change Spec.map (f.app U) ≫ i = j ≫ f
    rw [← f.appLE_eq_app]
    exact hU.SpecMap_appLE_fromSpec f hV le_rfl
  let G := (Scheme.Modules.pullback f).obj F
  let M := (Scheme.Modules.pullback i).obj F
  haveI : M.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
      ((restrictFunctorIsoPullback i).app F)
      (isQuasicoherent_restrictFunctor i F)
  let q := (pullbackComp g i).app F ≪≫ (pullbackCongr w).app F ≪≫
    ((pullbackComp j f).app F).symm
  let Γ' := moduleSpecΓFunctor (R := Γ(Y, V))
  let E := ModuleCat.extendScalars.{u,u,u} φ.hom
  obtain ⟨e, he⟩ := EquivariantAffineModules.affineSectionBaseChange φ M
  refine ⟨affineOpenSections hV G ≪≫ (Γ'.mapIso q).symm ≪≫ e ≪≫
    E.mapIso (affineOpenSections hU F).symm, ?_⟩
  intro s
  have hu : ⊤ ≤ i ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have hv : ⊤ ≤ j ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have hg : (⊤ : (Spec Γ(Y, V)).Opens) ≤ g ⁻¹ᵁ ⊤ := by simp
  let t := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app U s
  have hq :
      q.hom.app ⊤ (Specs.EquivariantAffineModules.pullSection g M
        ((affineOpenSections hU F).hom s)) = (affineOpenSections hV G).hom t := by
    let b := ((pullbackComp j f).hom.app F).app (⊤ : (Spec Γ(Y, V)).Opens)
    haveI : IsIso b := inferInstanceAs (IsIso
      (((Scheme.Modules.toPresheaf (Spec Γ(Y, V))).map ((pullbackComp j f).hom.app F)).app (op ⊤)))
    apply (ConcreteCategory.bijective_of_isIso b).injective
    have hg' (z : Γ(M, ⊤)) : Specs.EquivariantAffineModules.pullSection g M z =
        pullSection g M ⊤ ⊤ hg z := by
      exact (pullSection_preimage g M ⊤ z).symm
    rw [affineOpenSections_apply, affineOpenSections_apply, hg']
    have ha := pullSection_comp g i F hu hg s
    have hb := pullSection_comp j f F (le_rfl : V ≤ f ⁻¹ᵁ U) hv s
    rw [pullSection_preimage] at hb
    change b (((pullbackComp j f).inv.app F).app ⊤
      (((pullbackCongr w).hom.app F).app ⊤
        (((pullbackComp g i).hom.app F).app ⊤
          (pullSection g M ⊤ ⊤ hg (pullSection i F U ⊤ hu s))))) = _
    have hc (z : Γ((Scheme.Modules.pullback (j ≫ f)).obj F, ⊤)) :
        b (((pullbackComp j f).inv.app F).app ⊤ z) = z :=
      ConcreteCategory.congr_hom
        (congrArg (fun t => t.app (⊤ : (Spec Γ(Y, V)).Opens))
          (((pullbackComp j f).app F).inv_hom_id)) z
    rw [hc, ha, hb]
    exact pullSection_congr_open w F U ⊤ _ _ s
  have ht : (Γ'.map q.inv) ((affineOpenSections hV G).hom t) =
      Specs.EquivariantAffineModules.pullSection g M ((affineOpenSections hU F).hom s) := by
    have h := congrArg (fun z => (Γ'.map q.inv) z) hq.symm
    change _ = ((Γ'.map q.hom) ≫ (Γ'.map q.inv)) _ at h
    rw [← Γ'.map_comp, q.hom_inv_id, Γ'.map_id] at h
    exact h
  change (E.map (affineOpenSections hU F).inv)
      (e.hom ((Γ'.map q.inv) ((affineOpenSections hV G).hom t))) = _
  rw [ht, he]
  have hn := (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.naturality
    (affineOpenSections hU F).inv
  have hs := ConcreteCategory.congr_hom hn ((affineOpenSections hU F).hom s)
  change (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _
      ((affineOpenSections hU F).inv ((affineOpenSections hU F).hom s)) = _ at hs
  rw [show (affineOpenSections hU F).inv ((affineOpenSections hU F).hom s) = s from
    ConcreteCategory.congr_hom (affineOpenSections hU F).hom_inv_id s] at hs
  exact hs.symm

end AffineOpen


private theorem pullback_isQuasicoherent {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj F).IsQuasicoherent := by
  obtain ⟨I, U, pres, hU, _⟩ := F.exists_isOpenCover_presentation
  let V (i : I) := f ⁻¹ᵁ (U i)
  let G := (Scheme.Modules.pullback f).obj F
  have hV : IsOpenCover V := f.iSup_preimage_eq_top hU.iSup_eq_top
  let Q : G.QuasicoherentData.{u} :=
    { I := I
      X := V
      coversTop := (Opens.coversTop_iff _ V).mpr hV
      presentation := fun i => ?_ }
  · exact Q.isQuasicoherent
  ·
    let g := f ∣_ U i
    let L := Scheme.Modules.pullback g
    haveI : PreservesColimitsOfSize.{u,u} L := inferInstance
    haveI : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward g).IsRightAdjoint
    have e := asIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
    let P := (pres i).map L e.symm
    let B := (overFunctorEquiv (V i)).app G ≪≫
      (restrictFunctorIsoPullback (V i).ι).app G ≪≫
      (pullbackComp (V i).ι f).app F ≪≫
      (pullbackCongr (morphismRestrict_ι f (U i)).symm).app F ≪≫
      ((pullbackComp g (U i).ι).app F).symm ≪≫
      L.mapIso ((restrictFunctorIsoPullback (U i).ι).app F).symm
    let Q := P.ofIsIso B.inv
    let C := (overEquiv (V i)).inverse
    haveI : PreservesColimitsOfSize.{u,u} C := inferInstance
    let eu := (overEquiv (V i)).unitIso.app
      (SheafOfModules.unit (Y.ringCatSheaf.over (V i)))
    let er := (overEquiv (V i)).inverse.mapIso
      ((overFunctorEquiv (V i)).app (SheafOfModules.unit Y.ringCatSheaf) ≪≫
        Scheme.Modules.restrictUnitIso (V i).ι)
    let unitIso : SheafOfModules.unit (Y.ringCatSheaf.over (V i)) ≅
        C.obj (SheafOfModules.unit (V i).toScheme.ringCatSheaf) := eu ≪≫ er
    exact (Q.map C unitIso).ofIsIso ((overEquiv (V i)).unitIso.app (G.over (V i))).inv

open Specs.OrderedCechComparison
  (pullbackCover SheafCech cechPullback cechPullback_apply pullbackToIntersection
   tupleOpen_pullback derivedMapOfLift)
open private extendProductIso extendProductIso_hom_proj productModuleIso cech_homology_adjunction
  tupleOpen_isAffine_of_finite_intersections intersectionAcyclic_of_isAffine flatCohomologyMap_bridge
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

section LocalScalarExtension

set_option quotPrecheck false

open private affineOpenRegularPushout groundRingHomOpen_pullback
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

variable {k : Type u} [Field k] (R : TestAlgebra k) (X : SchemeOver k)
local notation "Y" => ((extendScheme R).obj X)
local notation "p" => extensionProjection R X
local notation "E" => extendToAlgebra (k := k) (K := R)

set_option maxHeartbeats 700000 in
private theorem localScalarExtension (F : X.left.Modules) [F.IsQuasicoherent]
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    let G := (Scheme.Modules.pullback p).obj F
    ∃ e : (localSections (X := Y) G (p ⁻¹ᵁ U)) ≅ ((E).obj (localSections (X := X) F U)),
      ∀ s : localSections (X := X) F U,
        e.hom (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).app U s) =
          (1 : R) ⊗ₜ[k,algebraMap k R] s := by
  haveI : IsAffineHom p := MorphismProperty.pullback_fst _ _ inferInstance
  let V := p ⁻¹ᵁ U
  let A := Γ(X.left, U)
  let B := Γ((Y).left, V)
  let M := F.val.obj (op U)
  let kA := groundRingHomOpen X U
  let rB := groundRingHomOpen Y V
  let aB := ((p).app U).hom
  let rk := algebraMap k R
  letI : Algebra k R := rk.toAlgebra
  letI : Algebra k A := kA.toAlgebra
  letI : Algebra R B := rB.toAlgebra
  letI : Algebra A B := aB.toAlgebra
  letI : Algebra k B := (rB.comp rk).toAlgebra
  letI : Module k M := Module.compHom M kA
  haveI : IsScalarTower k A M := IsScalarTower.of_compHom k A M
  haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq'
    (groundRingHomOpen_pullback rk p (extensionProjection_over R X) U).symm
  haveI : Algebra.IsPushout k R A B :=
    CommRingCat.isPushout_iff_isPushout.mp (affineOpenRegularPushout R X U hU)
  obtain ⟨e, he⟩ := affineOpenPullback hU p (hU.preimage p) F
  let b := Algebra.IsPushout.cancelBaseChange k R A B M
  let S := ModuleCat.restrictScalars.{u} rB
  refine ⟨(S).mapIso e ≪≫ b.toModuleIso, fun s => ?_⟩
  change b (e.hom (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).app U s)) = _
  rw [he]
  exact Algebra.IsPushout.cancelBaseChange_tmul k R A B M s


section CechScalarExtension

variable {I : Type u} [LinearOrder I] [Fintype I] (W : I → X.left.Opens)
  (F : X.left.Modules) [F.IsQuasicoherent]

local notation "G" => ((Scheme.Modules.pullback p).obj F)
local notation "V" => pullbackCover p W
local notation "C" => SheafCech W F
local notation "D" => SheafCech V G
local notation "A" => ModuleCat.extendRestrictScalarsAdj (algebraMap k R)
local notation "S" => ModuleCat.restrictScalars (algebraMap k R)
local notation "α" => ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F)
local notation "t" => cechPullback (algebraMap k R) p (extensionProjection_over R X) W α
local notation "EC" => (((E).mapHomologicalComplex (.up ℕ)).obj C)

set_option maxHeartbeats 800000 in
private theorem cechScalarExtension
    (hW : ∀ (n : ℕ) (e : Fin (n + 1) ↪o I), IsAffineOpen (tupleOpen W e)) :
    ∃ b : EC ≅ D, ∀ n, (t).f n = (A).homEquiv _ _ (b.hom.f n) := by
  classical
  let T (n : ℕ) := Fin (n + 1) ↪o I
  let M (n : ℕ) (i : T n) := localSections (X := X) F (tupleOpen W i)
  haveI (n : ℕ) : Finite (T n) :=
    Finite.of_injective (fun e : T n => (e : Fin (n + 1) → I)) DFunLike.coe_injective
  choose e he using fun n i => localScalarExtension R X F (tupleOpen W i) (hW n i)
  let v (n : ℕ) (i : T n) :=
    (e n i).symm ≪≫ (coefficientPresheaf G).mapIso
      (eqToIso (tupleOpen_pullback p W i)).op
  let b (n : ℕ) : (EC).X n ≅ (D).X n :=
    extendProductIso (R := R) (M n) ≪≫ productModuleIso (v n)
  have hb (n : ℕ) : (t).f n = (A).homEquiv _ _ (b n).hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change (t).f n x i = (b n).hom ((1 : R) ⊗ₜ[k,algebraMap k R] x) i
    rw [cechPullback_apply]
    have h₁ := ConcreteCategory.congr_hom (extendProductIso_hom_proj (R := R) (M n) i)
      ((1 : R) ⊗ₜ[k,algebraMap k R] x)
    change (extendProductIso (R := R) (M n)).hom ((1 : R) ⊗ₜ[k,algebraMap k R] x) i =
      (E).map (ModuleCat.ofHom (LinearMap.proj i)) ((1 : R) ⊗ₜ[k,algebraMap k R] x) at h₁
    rw [ModuleCat.ExtendScalars.map_tmul] at h₁
    change (extendProductIso (R := R) (M n)).hom ((1 : R) ⊗ₜ[k,algebraMap k R] x) i =
      (1 : R) ⊗ₜ[k,algebraMap k R] (x i : M n i) at h₁
    change (G).presheaf.map (pullbackToIntersection p W i).op
      ((α).app (tupleOpen W i) (x i)) =
      (v n i).hom ((extendProductIso (R := R) (M n)).hom
        ((1 : R) ⊗ₜ[k,algebraMap k R] x) i)
    rw [h₁, ← he n i (x i)]
    have h₂ := ConcreteCategory.congr_hom (e n i).hom_inv_id ((α).app (tupleOpen W i) (x i))
    change (e n i).inv ((e n i).hom ((α).app (tupleOpen W i) (x i))) = _ at h₂
    change _ = ((coefficientPresheaf G).mapIso (eqToIso
      (tupleOpen_pullback p W i)).op).hom ((e n i).inv ((e n i).hom _))
    rw [h₂]
    rfl
  have hc (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
      (b i).hom ≫ (D).d i j = (EC).d i j ≫ (b j).hom := by
    apply ((A).homEquiv _ _).injective
    rw [(A).homEquiv_naturality_right, ← hb i]
    change ((t).f i) ≫ (S).map ((D).d i j) = (A).homEquiv _ _ ((E).map ((C).d i j) ≫ (b j).hom)
    rw [(A).homEquiv_naturality_left, ← hb j]
    exact (t).comm i j
  exact ⟨HomologicalComplex.Hom.isoOfComponents b hc, hb⟩

end CechScalarExtension

end LocalScalarExtension

set_option maxHeartbeats 1000000 in
theorem baseChange : BaseChange.{u} := by
  intro k _ X hX R F _ n
  classical
  obtain ⟨I, inst, W, hW, hAff⟩ := hX
  let : Fintype I := inst
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hp : Flat (extensionProjection R X) := FlatCohomology.flatScalarExtension k R X
  let f := extensionProjection R X
  let w := extensionProjection_over R X
  let G := (Scheme.Modules.pullback f).obj F
  let α := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F
  let V := pullbackCover f W
  have hV : (⨆ i, V i) = ⊤ := f.iSup_preimage_eq_top hW
  have hf : IsAffineHom f := MorphismProperty.pullback_fst _ _ inferInstance
  have hAW (i : ℕ) (e : Fin (i + 1) ↪o I) : IsAffineOpen (tupleOpen W e) :=
    tupleOpen_isAffine_of_finite_intersections W hAff e
  have hAV {i : ℕ} (e : Fin (i + 1) ↪o I) : IsAffineOpen (tupleOpen V e) := by
    change IsAffineOpen (Specs.OrderedCechComparison.tupleOpen (pullbackCover f W) e)
    rw [tupleOpen_pullback]
    exact (hAW i e).preimage f
  let p := intersectionAcyclic_of_isAffine W (hAW _) F inferInstance
  let q := intersectionAcyclic_of_isAffine V hAV G (pullback_isQuasicoherent f F)
  obtain ⟨c, _, _, natural⟩ := LinearAlgebraicGroups.OrderedCechComparison.orderedCechComparison.{u}
  obtain ⟨d, hd⟩ := cechScalarExtension R X W F hAW
  let cX := c X W hW F p n
  let cY := c ((extendScheme R).obj X) V hV G q n
  let cH := extendCohomologyIso (SheafCech W F) n ≪≫
    HomologicalComplex.homologyMapIso d n
  let E := extendToAlgebra (k := k) (K := R)
  let b := E.mapIso cX ≪≫ cH ≪≫ cY.symm
  obtain ⟨m, hm⟩ := flatCohomologyMap_bridge (algebraMap k R) f w α n
  let JX := injectiveResolution F
  let JY := injectiveResolution G
  obtain ⟨l, hl⟩ := (hm JX JY).1
  have h := natural (X := X) (Y := (extendScheme R).obj X) W hW
    (algebraMap k R) f w α p q JX JY l hl n
  have hmap : m = derivedMapOfLift (algebraMap k R) f w JX JY l n :=
    (hm JX JY).2 l hl
  let A := ModuleCat.extendRestrictScalarsAdj (algebraMap k R)
  let S := ModuleCat.restrictScalars.{u} (algebraMap k R)
  change derivedMapOfLift (algebraMap k R) f w JX JY l n ≫ S.map cY.hom = _ at h
  rw [← hmap] at h
  refine ⟨b, ?_⟩
  change IsCohomologyMap (algebraMap k R) f w α n (A.homEquiv _ _ b.hom)
  suffices H : A.homEquiv _ _ b.hom = m by
    exact H.symm ▸ hm
  apply (cancel_mono (S.map cY.hom)).mp
  rw [h]
  change A.homEquiv _ _ (E.map cX.hom ≫ cH.hom ≫ cY.inv) ≫ S.map cY.hom = _
  erw [A.homEquiv_naturality_left, A.homEquiv_naturality_right, Category.assoc, Category.assoc,
    ← S.map_comp, cY.inv_hom_id]
  erw [S.map_id, Category.comp_id]
  exact congrArg (cX.hom ≫ ·) (cech_homology_adjunction d.hom _ hd n)

section Naturality

open FlatCohomology (onCochains restrict restrictHomology sections sectionsLift IsLift)
open private homology_of_lifts_eq restrictHomology_natural sectionsPushforwardComplex_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.FlatPullback

variable {A B : Type u} [CommRing A] [CommRing B]
  {X : SchemeOverRing A} {Y : SchemeOverRing B}

set_option maxHeartbeats 600000 in
private theorem cohomologyMap_natural (φ : A →+* B) (p : Y.left ⟶ X.left) [Flat p]
    (w : p ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {F F' : X.left.Modules} {G G' : Y.left.Modules}
    (f : F ⟶ F') (g : G ⟶ G')
    {α : F ⟶ (pushforward p).obj G} {α' : F' ⟶ (pushforward p).obj G'}
    (h : f ≫ α' = α ≫ (pushforward p).map g) (n : ℕ)
    {m : (cohomology X n).obj F ⟶ (restrict φ).obj ((cohomology Y n).obj G)}
    {m' : (cohomology X n).obj F' ⟶ (restrict φ).obj ((cohomology Y n).obj G')}
    (hm : IsCohomologyMap φ p w α n m) (hm' : IsCohomologyMap φ p w α' n m') :
    (cohomology X n).map f ≫ m' = m ≫ (restrict φ).map ((cohomology Y n).map g) := by
  let P := pushforward p
  let I := injectiveResolution F
  let I' := injectiveResolution F'
  let J := injectiveResolution G
  let J' := injectiveResolution G'
  let r := InjectiveResolution.desc f I' I
  let s := InjectiveResolution.desc g J' J
  obtain ⟨⟨l, hl⟩, hlm⟩ := hm I J
  obtain ⟨⟨l', hl'⟩, hlm'⟩ := hm' I' J'
  let t₁ := r ≫ l'
  let t₂ := l ≫ (onCochains P).map s
  change IsLift p α I J l at hl
  change IsLift p α' I' J' l' at hl'
  have ht₁ : IsLift p (f ≫ α') I J' t₁ := by
    change I.ι.f 0 ≫ r.f 0 ≫ l'.f 0 = (f ≫ α') ≫ P.map (J'.ι.f 0)
    rw [← Category.assoc, InjectiveResolution.desc_commutes_zero, Category.assoc, hl',
      Category.assoc]
  have ht₂ : IsLift p (f ≫ α') I J' t₂ := by
    change I.ι.f 0 ≫ l.f 0 ≫ P.map (s.f 0) = (f ≫ α') ≫ P.map (J'.ι.f 0)
    rw [← Category.assoc]
    change I.ι.f 0 ≫ l.f 0 = α ≫ P.map (J.ι.f 0) at hl
    rw [hl, Category.assoc, ← P.map_comp, InjectiveResolution.desc_commutes_zero,
      P.map_comp, ← Category.assoc, ← h]
  have hJ : P.PreservesInjectiveObjects := FlatCohomology.flatPushforwardPreservesInjectives p
  have hi := homology_of_lifts_eq φ p w (f ≫ α') I J' n ht₁ ht₂
  have h₁ := hlm l hl
  have h₂ := hlm' l' hl'
  let RX := onCochains (sections X)
  let RY := onCochains (sections Y)
  let S := restrict φ
  have hr : (cohomology X n).map f ≫ (I'.isoRightDerivedObj (sections X) n).hom =
      (I.isoRightDerivedObj (sections X) n).hom ≫ HomologicalComplex.homologyMap (RX.map r) n :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality _ _ _ _
      (InjectiveResolution.desc_commutes_zero f I' I) _ n
  have hs : (J.isoRightDerivedObj (sections Y) n).inv ≫ (cohomology Y n).map g =
        HomologicalComplex.homologyMap (RY.map s) n ≫ (J'.isoRightDerivedObj (sections Y) n).inv := by
    have h' := InjectiveResolution.isoRightDerivedObj_hom_naturality _ _ _ _
      (InjectiveResolution.desc_commutes_zero g J' J) (sections Y) n
    change (cohomology Y n).map g ≫ (J'.isoRightDerivedObj (sections Y) n).hom =
      (J.isoRightDerivedObj (sections Y) n).hom ≫ HomologicalComplex.homologyMap (RY.map s) n at h'
    apply (cancel_mono (J'.isoRightDerivedObj (sections Y) n).hom).mp
    simp only [Category.assoc, h', Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hleft : sectionsLift φ p w t₁ = RX.map r ≫ sectionsLift φ p w l' := by
    unfold sectionsLift
    change RX.map (r ≫ l') ≫ _ = RX.map r ≫ RX.map l' ≫ _
    rw [RX.map_comp, Category.assoc]
  have hright : sectionsLift φ p w t₂ = sectionsLift φ p w l ≫ (onCochains S).map (RY.map s) := by
    unfold sectionsLift
    change RX.map (l ≫ (onCochains P).map s) ≫ _ = (RX.map l ≫ _) ≫ _
    rw [RX.map_comp, Category.assoc, sectionsPushforwardComplex_natural, Category.assoc]
  change m = (I.isoRightDerivedObj (sections X) n).hom ≫
    HomologicalComplex.homologyMap (sectionsLift φ p w l) n ≫
    (restrictHomology φ (RY.obj J.cocomplex) n).hom ≫
    S.map (J.isoRightDerivedObj (sections Y) n).inv at h₁
  change m' = (I'.isoRightDerivedObj (sections X) n).hom ≫
    HomologicalComplex.homologyMap (sectionsLift φ p w l') n ≫
    (restrictHomology φ (RY.obj J'.cocomplex) n).hom ≫
    S.map (J'.isoRightDerivedObj (sections Y) n).inv at h₂
  let i := I.isoRightDerivedObj (sections X) n
  let j := J.isoRightDerivedObj (sections Y) n
  let j' := J'.isoRightDerivedObj (sections Y) n
  let u := restrictHomology φ (RY.obj J.cocomplex) n
  let u' := restrictHomology φ (RY.obj J'.cocomplex) n
  let H := fun {K L : CochainComplex (ModuleCat.{u} A) ℕ} (a : K ⟶ L) =>
    HomologicalComplex.homologyMap a n
  have hT : H (sectionsLift φ p w t₁) = H (RX.map r) ≫ H (sectionsLift φ p w l') := by
    rw [hleft]
    exact HomologicalComplex.homologyMap_comp ..
  have hT' : H (sectionsLift φ p w t₂) ≫ u'.hom =
      H (sectionsLift φ p w l) ≫ u.hom ≫ S.map (HomologicalComplex.homologyMap (RY.map s) n) := by
    rw [hright]
    change HomologicalComplex.homologyMap
      (sectionsLift φ p w l ≫ (onCochains S).map (RY.map s)) n ≫ u'.hom = _
    rw [HomologicalComplex.homologyMap_comp, Category.assoc]
    exact congrArg (H (sectionsLift φ p w l) ≫ ·) (restrictHomology_natural φ (RY.map s) n)
  have hh : (S.map (HomologicalComplex.homologyMap (RY.map s) n)) ≫ S.map j'.inv =
      S.map j.inv ≫ S.map ((cohomology Y n).map g) := by
    rw [← S.map_comp, ← S.map_comp]
    exact congrArg S.map hs.symm
  calc
    (cohomology X n).map f ≫ m' =
        i.hom ≫ H (sectionsLift φ p w t₁) ≫ u'.hom ≫ S.map j'.inv := by
      rw [h₂, reassoc_of% hr, hT]
      exact (Category.assoc _ _ _).symm
    _ = i.hom ≫ H (sectionsLift φ p w t₂) ≫ u'.hom ≫ S.map j'.inv :=
      congrArg (fun a => i.hom ≫ a ≫ u'.hom ≫ S.map j'.inv) hi
    _ = m ≫ S.map ((cohomology Y n).map g) := by
      rw [h₁, ← Category.assoc (H (sectionsLift φ p w t₂)), hT']
      simp only [Category.assoc]
      exact congrArg (fun a => i.hom ≫ H (sectionsLift φ p w l) ≫ u.hom ≫ a) hh


theorem baseChangeNaturality : BaseChangeNaturality.{u} := by
  intro k _ X R F G a n bF bG hF hG
  let p := extensionProjection R X
  let b := Scheme.Modules.pullbackPushforwardAdjunction p
  let A := ModuleCat.extendRestrictScalarsAdj (algebraMap k R)
  have : Flat p := FlatCohomology.flatScalarExtension k R X
  apply (A.homEquiv _ _).injective
  rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right]
  exact cohomologyMap_natural (algebraMap k R) p (extensionProjection_over R X)
    a ((Scheme.Modules.pullback p).map a) (b.unit.naturality a) n hF hG

end Naturality

section FlatTower

private theorem pushforwardCongr_refl {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Y.Modules) :
    (pushforwardCongr (rfl : f = f)).hom.app F = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.Hom.id_app,
    eqToHom_refl, op_id]
  exact F.presheaf.map_id _

private theorem pushforwardCongr_symm_comp {X Y : Scheme.{u}} {f g : Y ⟶ X}
    (h : f = g) (F : Y.Modules) :
    (pushforwardCongr h).hom.app F ≫ (pushforwardCongr h.symm).hom.app F = 𝟙 _ := by
  subst g
  simp only [pushforwardCongr_refl, Category.id_comp]

private theorem pullbackUnit_tower {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {h : Z ⟶ X} (w : g ≫ f = h) (F : X.Modules) :
    let α := (pullbackPushforwardAdjunction f).unit.app F
    let β := (pullbackPushforwardAdjunction g).homEquiv _ _
      (((pullbackComp g f).app F ≪≫ (pullbackCongr w).app F).hom)
    α ≫ (pushforward f).map β ≫ (pushforwardComp g f).hom.app _ ≫
        (pushforwardCongr w).hom.app _ =
      (pullbackPushforwardAdjunction h).unit.app F := by
  subst h
  have hh : ((pullbackCongr (rfl : g ≫ f = g ≫ f)).app F).hom = 𝟙 _ := rfl
  have hp := pushforwardCongr_refl (g ≫ f)
  dsimp only [Iso.trans_hom]
  rw [hh, Category.comp_id, Adjunction.homEquiv_unit, hp, Category.comp_id]
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  exact (pullbackUnit_comp_app g f F U s).symm

private theorem cohomologyMap_transport {A B : Type u} [CommRing A] [CommRing B]
    {X : SchemeOverRing A} {Y : SchemeOverRing B} {φ ψ : A →+* B} (e : φ = ψ)
    {f g : Y.left ⟶ X.left} (h : f = g)
    (wf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (wg : g ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom ψ))
    {F : X.left.Modules} {G : Y.left.Modules}
    {α : F ⟶ (pushforward f).obj G} {β : F ⟶ (pushforward g).obj G}
    (w : α ≫ (pushforwardCongr h).hom.app G = β)
    (n : ℕ) {m : (cohomology X n).obj F ⟶ (ModuleCat.restrictScalars φ).obj ((cohomology Y n).obj G)}
    (hm : FlatCohomology.IsCohomologyMap φ f wf α n m) :
    FlatCohomology.IsCohomologyMap ψ g wg β n
      (m ≫ (ModuleCat.restrictScalarsCongr e).hom.app _) := by
  subst ψ g
  have hw := pushforwardCongr_refl f G
  rw [hw, Category.comp_id] at w
  subst β
  have hr : (ModuleCat.restrictScalarsCongr (rfl : φ = φ)).hom.app
      ((cohomology Y n).obj G) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    ext x : 1
    rfl
  rw [hr, Category.comp_id]
  exact hm

private theorem cohomologyMap_comp_apply {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {X : SchemeOverRing A} {Y : SchemeOverRing B} {Z : SchemeOverRing C}
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (e : ψ.comp φ = χ)
    (f : Y.left ⟶ X.left) (g : Z.left ⟶ Y.left) (p : Z.left ⟶ X.left)
    [Flat f] [Flat g] (hp : g ≫ f = p)
    (wf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (wg : g ≫ Y.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom ψ))
    (wp : p ≫ X.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom χ))
    {F : X.left.Modules} {G : Y.left.Modules} {H : Z.left.Modules}
    (α : F ⟶ (pushforward f).obj G) (β : G ⟶ (pushforward g).obj H)
    (γ : F ⟶ (pushforward p).obj H)
    (h : α ≫ (pushforward f).map β ≫ (pushforwardComp g f).hom.app H ≫
      (pushforwardCongr hp).hom.app H = γ)
    (n : ℕ) {m₁ m₂ m₃} (hm₁ : IsCohomologyMap φ f wf α n m₁)
    (hm₂ : IsCohomologyMap ψ g wg β n m₂) (hm₃ : IsCohomologyMap χ p wp γ n m₃)
    (x : (cohomology X n).obj F) : m₂ (m₁ x) = m₃ x := by
  have hc := FlatCohomology.cohomologyMapComp φ ψ f g wf wg α β n (m₁ := m₁) (m₂ := m₂)
    (by exact hm₁) (by exact hm₂)
  have ht := cohomologyMap_transport e hp (FlatCohomology.comp_over φ ψ f g wf wg) wp
    (by simpa only [Category.assoc] using h) n hc
  have he := FlagCohomology.inducedCohomologyMap_unique χ p wp γ n
    (by exact ht) hm₃
  exact ConcreteCategory.congr_hom he x

/-- The flat case of the tower law uses the actual map on injective resolutions
for the second pullback. -/
theorem flatBaseChangeTower : FlatBaseChangeTower.{u} := by
  intro k _ X R S j q _ hq wq F n bR bS m hR hS hm x
  letI : Flat (extensionProjection R X) := FlatCohomology.flatScalarExtension k R X
  refine cohomologyMap_comp_apply (X := X) (Y := (extendScheme R).obj X)
    (Z := (extendScheme S).obj X) (algebraMap k R) j.hom.toRingHom (algebraMap k S)
    j.hom.comp_algebraMap (extensionProjection R X) q (extensionProjection S X) hq
    (extensionProjection_over R X) wq (extensionProjection_over S X)
    ((pullbackPushforwardAdjunction (extensionProjection R X)).unit.app F) (towerCoefficient F q hq)
    ((pullbackPushforwardAdjunction (extensionProjection S X)).unit.app F)
    (pullbackUnit_tower (extensionProjection R X) q hq F) n
    (m₁ := (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ bR)
    (m₂ := m) (m₃ := (ModuleCat.extendRestrictScalarsAdj (algebraMap k S)).homEquiv _ _ bS) hR hm hS x

end FlatTower

section CechComposition

set_option quotPrecheck false

open FlatCohomology (onCochains restrict restrictHomology comp_over)
open private restrictCompComplex restrictHomology_comp restrictHomology_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.FlatPullback
open private homologyTo from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
  {X : SchemeOverRing A} {Y : SchemeOverRing B} {Z : SchemeOverRing D}
  (φ : A →+* B) (ψ : B →+* D) (f : Y.left ⟶ X.left) (g : Z.left ⟶ Y.left)
  (wf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
  (wg : g ≫ Y.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom ψ))
  {I : Type u} [LinearOrder I] (U : I → X.left.Opens)
  {F : X.left.Modules} {G : Y.left.Modules} {H : Z.left.Modules}
  (α : F ⟶ (pushforward f).obj G) (β : G ⟶ (pushforward g).obj H)

local notation "V" => pullbackCover f U
local notation "W" => pullbackCover g V
local notation "γ" => α ≫ (pushforward f).map β ≫ (pushforwardComp g f).hom.app H

set_option maxHeartbeats 600000 in
private theorem cechPullback_comp :
    cechPullback (ψ.comp φ) (g ≫ f) (comp_over φ ψ f g wf wg) U γ =
      cechPullback φ f wf U α ≫
        (onCochains (restrict φ)).map (cechPullback ψ g wg V β) ≫
        restrictCompComplex φ ψ (SheafCech W H) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  let U₀ := Specs.OrderedCechComparison.tupleOpen U i
  let V₀ := Specs.OrderedCechComparison.tupleOpen V i
  let e₁ := (pullbackToIntersection f U i).op
  let e₂ := (pullbackToIntersection g V i).op
  let e₃ := (pullbackToIntersection (g ≫ f) U i).op
  let s := α.app U₀ (x i)
  change H.presheaf.map e₃ (β.app (f ⁻¹ᵁ U₀) s) =
    H.presheaf.map e₂ (β.app V₀ (G.presheaf.map e₁ s))
  have hn := β.mapPresheaf.naturality_apply e₁ s
  change β.app V₀ (G.presheaf.map e₁ s) =
    ((pushforward g).obj H).presheaf.map e₁ (β.app (f ⁻¹ᵁ U₀) s) at hn
  rw [Scheme.Modules.pushforward_obj_presheaf_map] at hn
  rw [hn]
  symm
  exact (ConcreteCategory.congr_hom
    ((H.presheaf.map_comp _ _).symm.trans (congrArg H.presheaf.map (Subsingleton.elim _ e₃)))) _

set_option maxHeartbeats 600000 in
private theorem cechPullback_homology_comp (n : ℕ) :
    homologyTo (restrict (ψ.comp φ))
      (cechPullback (ψ.comp φ) (g ≫ f) (comp_over φ ψ f g wf wg) U γ) n =
    homologyTo (restrict φ) (cechPullback φ f wf U α) n ≫
      (restrict φ).map (homologyTo (restrict ψ) (cechPullback ψ g wg V β) n) ≫
      (ModuleCat.restrictScalarsComp φ ψ).inv.app ((SheafCech W H).homology n) := by
  let L := SheafCech W H
  let a := cechPullback φ f wf U α
  let b := cechPullback ψ g wg V β
  rw [cechPullback_comp]
  change HomologicalComplex.homologyMap
      (a ≫ (onCochains (restrict φ)).map b ≫ restrictCompComplex φ ψ L) n ≫
      (restrictHomology (ψ.comp φ) L n).hom = _
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc]
  rw [restrictHomology_comp φ ψ L n,
    reassoc_of% restrictHomology_natural φ b n]
  simp only [homologyTo, Functor.map_comp, Category.assoc]
  rfl

end CechComposition



open Specs.OrderedCechComparison (sheafCechFunctor IntersectionAcyclic
  orderedCochains coface differential tupleOpen_le sectionAugmentation
  resolutionDouble extendDouble doubleComponentIso intEmbedding ComparisonFamily)

section Connecting

private theorem affineOpenSections_exact {Z : Scheme.{u}} (U : Z.Opens) (hU : IsAffineOpen U)
    (S : ShortComplex Z.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] (hS : S.ShortExact) :
    Function.Injective (S.f.app U) ∧ Function.Exact (S.f.app U) (S.g.app U) ∧
      Function.Surjective (S.g.app U) := by
  let i := hU.fromSpec
  let R := restrictFunctor i
  let e := restrictFunctorIsoPullback i
  let : (Scheme.Modules.pullback i).PreservesHomology := FlatCohomology.flatPullbackExact i
  let : PreservesFiniteLimits (Scheme.Modules.pullback i) :=
    Functor.preservesFiniteLimits_of_preservesHomology (Scheme.Modules.pullback i)
  let K := S.map R
  have hK : K.ShortExact := ShortComplex.shortExact_of_iso
    (S.mapNatIso e.symm) (hS.map_of_exact (Scheme.Modules.pullback i))
  let : K.X₁.IsQuasicoherent := isQuasicoherent_restrictFunctor i S.X₁
  let : K.X₂.IsQuasicoherent := isQuasicoherent_restrictFunctor i S.X₂
  let : K.X₃.IsQuasicoherent := isQuasicoherent_restrictFunctor i S.X₃
  have he := EquivariantAffineModules.affineSectionsExact K hK
  have htop : i ''ᵁ (⊤ : (Spec Γ(Z, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let P (W : Z.Opens) := Function.Injective (S.f.app W) ∧
    Function.Exact (S.f.app W) (S.g.app W) ∧ Function.Surjective (S.g.app W)
  exact (congrArg P htop).mp (show P (i ''ᵁ ⊤) from he)

private theorem cechShortExact {A : Type u} [CommRing A] {X : SchemeOverRing A}
    {I : Type u} [LinearOrder I] (U : I → X.left.Opens)
    (hU : ∀ (n : ℕ) (e : Fin (n + 1) ↪o I), IsAffineOpen (tupleOpen U e))
    (S : ShortComplex X.left.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] (hS : S.ShortExact) : (S.map (sheafCechFunctor U)).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let D := (S.map (sheafCechFunctor U)).map (HomologicalComplex.eval _ _ n)
  have hf (x : D.X₁) (e : Fin (n + 1) ↪o I) :
      D.f x e = S.f.app (tupleOpen U e) (x e) := rfl
  have hg (x : D.X₂) (e : Fin (n + 1) ↪o I) :
      D.g x e = S.g.app (tupleOpen U e) (x e) := rfl
  have h (e : Fin (n + 1) ↪o I) := affineOpenSections_exact _ (hU n e) S hS
  change D.ShortExact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.moduleCat_exact_iff D).mpr
    intro x hx
    have hz (e : Fin (n + 1) ↪o I) : S.g.app (tupleOpen U e) (x e) = 0 := by
      rw [← hg, hx]
      rfl
    choose y hy using fun e => ((h e).2.1 (x e)).mp (hz e)
    exact ⟨y, funext fun e => (hf y e).trans (hy e)⟩
  · apply (ModuleCat.mono_iff_injective D.f).mpr
    intro x y hxy
    funext e
    exact (h e).1 ((hf x e).symm.trans ((congrFun hxy e).trans (hf y e)))
  · apply (ModuleCat.epi_iff_surjective D.g).mpr
    intro y
    choose x hx using fun e => (h e).2.2 (y e)
    exact ⟨x, funext fun e => (hg x e).trans (hx e)⟩

open HomologicalComplex
open FlatCohomology (restrict onCochains)
open private homologyTo cyclesTo cyclesTo_iCycles homologyπ_homologyTo
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison

private theorem homologyTo_cyclesMk {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {K : CochainComplex (ModuleCat.{u} A) ℕ}
    {L : CochainComplex (ModuleCat.{u} B) ℕ} (m : K ⟶ (onCochains (restrict φ)).obj L)
    (n : ℕ) (x : K.X n) (hx : K.d n (n + 1) x = 0)
    (hy : L.d n (n + 1) (m.f n x) = 0) :
    homologyTo (restrict φ) m n (K.homologyπ n (K.cyclesMk x (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hx)) =
      L.homologyπ n (L.cyclesMk (m.f n x) (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hy) := by
  have h : cyclesTo (restrict φ) m n (K.cyclesMk x (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hx) =
      L.cyclesMk (m.f n x) (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hy := by
    apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
    have e := ConcreteCategory.congr_hom (cyclesTo_iCycles (restrict φ) m n)
      (K.cyclesMk x (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hx)
    change L.iCycles n (cyclesTo (restrict φ) m n (K.cyclesMk x (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hx)) =
      m.f n (K.iCycles n (K.cyclesMk x (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hx)) at e
    rw [e]
    exact congrArg (m.f n) (K.i_cyclesMk x (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hx) |>.trans
      (L.i_cyclesMk (m.f n x) (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hy).symm
  have e := ConcreteCategory.congr_hom (homologyπ_homologyTo (restrict φ) m n)
    (K.cyclesMk x (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hx)
  change _ = L.homologyπ n (cyclesTo (restrict φ) m n (K.cyclesMk x (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hx)) at e
  exact e.trans (congrArg (L.homologyπ n) h)

private theorem homologyTo_δ_naturality {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {K : ShortComplex (CochainComplex (ModuleCat.{u} A) ℕ)}
    {L : ShortComplex (CochainComplex (ModuleCat.{u} B) ℕ)}
    (hK : K.ShortExact) (hL : L.ShortExact)
    (m : K ⟶ L.map (onCochains (restrict φ))) (n : ℕ) :
    hK.δ n (n + 1) rfl ≫ homologyTo (restrict φ) m.τ₁ (n + 1) =
      homologyTo (restrict φ) m.τ₃ n ≫ (restrict φ).map (hL.δ n (n + 1) rfl) := by
  let i := n
  let j := n + 1
  let k := n + 1 + 1
  let : Mono K.f := hK.mono_f
  let : Epi K.g := hK.epi_g
  apply (cancel_epi (K.X₃.homologyπ i)).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let x₃ := K.X₃.iCycles i z
  have hx₃ : K.X₃.d i j x₃ = 0 := by
    exact ConcreteCategory.congr_hom (K.X₃.iCycles_d i j) z
  have hz : K.X₃.cyclesMk x₃ j ((ComplexShape.up ℕ).next_eq' rfl) hx₃ = z := by
    apply (ModuleCat.mono_iff_injective (K.X₃.iCycles i)).mp inferInstance
    exact K.X₃.i_cyclesMk x₃ j ((ComplexShape.up ℕ).next_eq' rfl) hx₃
  obtain ⟨x₂, hx₂⟩ := (ModuleCat.epi_iff_surjective (K.g.f i)).mp inferInstance x₃
  have h₀ : K.g.f j (K.X₂.d i j x₂) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← K.g.comm, ConcreteCategory.comp_apply, hx₂, hx₃]
  obtain ⟨x₁, hx₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact K).mp hK j).exact _ h₀
  let y₁ := m.τ₁.f j x₁
  let y₂ := m.τ₂.f i x₂
  let y₃ := m.τ₃.f i x₃
  have hy₃ : L.X₃.d i j y₃ = 0 := by
    have e := ConcreteCategory.congr_hom (m.τ₃.comm i j) x₃
    change L.X₃.d i j y₃ = m.τ₃.f j (K.X₃.d i j x₃) at e
    rw [hx₃, map_zero] at e
    exact e
  have hy₂ : L.g.f i y₂ = y₃ := by
    have e := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom m.comm₂₃ i) x₂
    change L.g.f i y₂ = m.τ₃.f i (K.g.f i x₂) at e
    rw [hx₂] at e
    exact e
  have hy₁ : L.f.f j y₁ = L.X₂.d i j y₂ := by
    have e := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom m.comm₁₂ j) x₁
    change L.f.f j y₁ = m.τ₂.f j (K.f.f j x₁) at e
    have hd := ConcreteCategory.congr_hom (m.τ₂.comm i j) x₂
    change L.X₂.d i j y₂ = m.τ₂.f j (K.X₂.d i j x₂) at hd
    change K.f.f j x₁ = K.X₂.d i j x₂ at hx₁
    rw [e, hx₁, ← hd]
  have h₁ := ShortComplex.ShortExact.d_eq_zero_of_f_eq_d_apply hK i j x₂ x₁ hx₁ k
  have h₂ := ShortComplex.ShortExact.d_eq_zero_of_f_eq_d_apply hL i j y₂ y₁ hy₁ k
  have d₁ := hK.δ_apply i j rfl x₃ hx₃ x₂ hx₂ x₁ hx₁ k ((ComplexShape.up ℕ).next_eq' rfl)
  have d₂ := hL.δ_apply i j rfl y₃ hy₃ y₂ hy₂ y₁ hy₁ k ((ComplexShape.up ℕ).next_eq' rfl)
  change hK.δ i j rfl (K.X₃.homologyπ i (K.X₃.cyclesMk x₃ j ((ComplexShape.up ℕ).next_eq' rfl) hx₃)) =
    K.X₁.homologyπ j (K.X₁.cyclesMk x₁ k ((ComplexShape.up ℕ).next_eq' rfl) h₁) at d₁
  change hL.δ i j rfl (L.X₃.homologyπ i (L.X₃.cyclesMk y₃ j ((ComplexShape.up ℕ).next_eq' rfl) hy₃)) =
    L.X₁.homologyπ j (L.X₁.cyclesMk y₁ k ((ComplexShape.up ℕ).next_eq' rfl) h₂) at d₂
  change homologyTo (restrict φ) m.τ₁ j (hK.δ i j rfl (K.X₃.homologyπ i z)) =
    hL.δ i j rfl (homologyTo (restrict φ) m.τ₃ i (K.X₃.homologyπ i z))
  rw [← hz, d₁, homologyTo_cyclesMk φ m.τ₁ j x₁ h₁ h₂,
    homologyTo_cyclesMk φ m.τ₃ i x₃ hx₃ hy₃]
  exact d₂.symm

open Specs.OrderedCechComparison (pullbackCover cechPullback derivedMapOfLift)
open LinearAlgebraicGroups.OrderedCechComparison
  (orderedCechComparisonIso cechPullback_comm)
open private orderedCechComparisonIso_eq resolutionAugmentations resolutionComparison_spec
  resolutionComparison_pullback resolutionComparison_coefficients
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison

private theorem canonicalResolutionComparison : IsResolutionComparison orderedCechComparisonIso.{u} := by
  intro A _ X I _ _ U hU F hF J n
  change Specs.OrderedCechComparison.IsComparisonFromResolution U J n
    (orderedCechComparisonIso X U hU F hF n)
  rw [orderedCechComparisonIso_eq X U hU F hF J n]
  exact resolutionComparison_spec U J (resolutionAugmentations U J hU hF) n

private theorem cohomologyMap_cech {A B : Type u} [CommRing A] [CommRing B]
    {X : SchemeOverRing A} {Y : SchemeOverRing B} (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens)
    (hU : (⨆ i, U i) = ⊤) {F : X.left.Modules} {G : Y.left.Modules}
    (hF : IntersectionAcyclic U F) (hG : IntersectionAcyclic (pullbackCover f U) G)
    (α : F ⟶ (pushforward f).obj G) (n : ℕ) {m} (hm : IsCohomologyMap φ f w α n m) :
    m ≫ (restrict φ).map
      (orderedCechComparisonIso Y (pullbackCover f U) (f.iSup_preimage_eq_top hU) G hG n).hom =
    (orderedCechComparisonIso X U hU F hF n).hom ≫
      homologyTo (restrict φ) (cechPullback φ f w U α) n := by
  let J := injectiveResolution F
  let K := injectiveResolution G
  obtain ⟨⟨l, hl⟩, hlm⟩ := hm J K
  rw [show m = derivedMapOfLift φ f w J K l n from hlm l hl,
    orderedCechComparisonIso_eq X U hU F hF J n,
    orderedCechComparisonIso_eq Y (pullbackCover f U) (f.iSup_preimage_eq_top hU) G hG K n]
  exact resolutionComparison_pullback U φ f w α J K (resolutionAugmentations U J hU hF)
    (resolutionAugmentations (pullbackCover f U) K (f.iSup_preimage_eq_top hU) hG) l hl n

private theorem cechConnecting_pullback {A B : Type u} [CommRing A] [CommRing B]
    {X : SchemeOverRing A} {Y : SchemeOverRing B} (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens)
    (hU : (⨆ i, U i) = ⊤) {S : ShortComplex X.left.Modules} {T : ShortComplex Y.left.Modules}
    (α : S ⟶ T.map (pushforward f))
    (h₁ : IntersectionAcyclic U S.X₁) (h₃ : IntersectionAcyclic U S.X₃)
    (g₁ : IntersectionAcyclic (pullbackCover f U) T.X₁)
    (g₃ : IntersectionAcyclic (pullbackCover f U) T.X₃)
    (s : (S.map (sheafCechFunctor U)).ShortExact)
    (t : (T.map (sheafCechFunctor (pullbackCover f U))).ShortExact)
    (n : ℕ) {m₁ m₃} (hm₁ : IsCohomologyMap φ f w α.τ₁ (n + 1) m₁)
    (hm₃ : IsCohomologyMap φ f w α.τ₃ n m₃) :
    cechConnecting X U hU S h₁ h₃ orderedCechComparisonIso s n ≫ m₁ = m₃ ≫
      (restrict φ).map (cechConnecting Y (pullbackCover f U) (f.iSup_preimage_eq_top hU)
        T g₁ g₃ orderedCechComparisonIso t n) := by
  let V := pullbackCover f U
  let hV := f.iSup_preimage_eq_top hU
  let R := restrict φ
  let K := S.map (sheafCechFunctor U)
  let L := T.map (sheafCechFunctor V)
  let p : K ⟶ L.map (onCochains R) :=
    { τ₁ := cechPullback φ f w U α.τ₁
      τ₂ := cechPullback φ f w U α.τ₂
      τ₃ := cechPullback φ f w U α.τ₃
      comm₁₂ := (cechPullback_comm φ f w U α.τ₁ α.τ₂ S.f T.f α.comm₁₂.symm).symm
      comm₂₃ := (cechPullback_comm φ f w U α.τ₂ α.τ₃ S.g T.g α.comm₂₃.symm).symm }
  let e₁ := orderedCechComparisonIso X U hU S.X₁ h₁ (n + 1)
  let e₃ := orderedCechComparisonIso X U hU S.X₃ h₃ n
  let u₁ := orderedCechComparisonIso Y V hV T.X₁ g₁ (n + 1)
  let u₃ := orderedCechComparisonIso Y V hV T.X₃ g₃ n
  have ht₁ : m₁ ≫ R.map u₁.hom = e₁.hom ≫ homologyTo R p.τ₁ (n + 1) :=
    cohomologyMap_cech φ f w U hU h₁ g₁ α.τ₁ (n + 1) hm₁
  have ht₃ : m₃ ≫ R.map u₃.hom = e₃.hom ≫ homologyTo R p.τ₃ n :=
    cohomologyMap_cech φ f w U hU h₃ g₃ α.τ₃ n hm₃
  have hd := homologyTo_δ_naturality φ s t p n
  apply (cancel_mono (R.map u₁.hom)).mp
  change (e₃.hom ≫ s.δ n (n + 1) rfl ≫ e₁.inv) ≫ m₁ ≫ R.map u₁.hom =
    (m₃ ≫ R.map (u₃.hom ≫ t.δ n (n + 1) rfl ≫ u₁.inv)) ≫ R.map u₁.hom
  have hcancel : R.map u₁.inv ≫ R.map u₁.hom = 𝟙 _ := by
    rw [← R.map_comp, u₁.inv_hom_id, R.map_id]
  simp only [Functor.map_comp, Category.assoc, ht₁, Iso.inv_hom_id_assoc, hcancel,
    reassoc_of% ht₃]
  exact congrArg (e₃.hom ≫ ·) hd

open private intersectionAcyclic_of_isAffine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

/-- Pullback on the actual derived cohomology commutes with the connecting maps
computed on a cover and its inverse image. -/
theorem matchedCechConnecting : MatchedCechConnecting.{u} := by
  refine ⟨orderedCechComparisonIso, canonicalResolutionComparison, ?_⟩
  intro A B _ _ X Y φ f w I _ _ U hU hAff hAff' S _ _ _ hS T _ _ _ hT α
  let V := pullbackCover f U
  let h₁ := intersectionAcyclic_of_isAffine U (hAff _) S.X₁ inferInstance
  let h₃ := intersectionAcyclic_of_isAffine U (hAff _) S.X₃ inferInstance
  let g₁ := intersectionAcyclic_of_isAffine V (hAff' _) T.X₁ inferInstance
  let g₃ := intersectionAcyclic_of_isAffine V (hAff' _) T.X₃ inferInstance
  refine ⟨h₁, h₃, g₁, g₃, cechShortExact U hAff S hS, cechShortExact V hAff' T hT, ?_⟩
  intro n m₁ m₃ hm₁ hm₃
  exact cechConnecting_pullback φ f w U hU α h₁ h₃ g₁ g₃ _ _ n hm₁ hm₃

end Connecting

open HomologicalComplex
open FlatCohomology (restrict)
open LinearAlgebraicGroups.OrderedCechComparison (orderedCechComparisonIso)
open Specs.OrderedCechComparison (pullbackCover)
open private intersectionAcyclic_of_isAffine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private orderedCechComparisonIso_eq resolutionAugmentations resolutionComparison_coefficients
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison

private theorem isAffineDiagonal {A : Type u} [CommRing A] (X : SchemeOverRing A)
    (hX : HasFiniteAffineCover X) : IsAffineHom (pullback.diagonal (terminal.from X.left)) := by
  classical
  obtain ⟨I, _, U, hU, hAff⟩ := hX
  have hs (i : I) : IsAffineOpen (U i) := by
    simpa using hAff {i} (Finset.singleton_nonempty i)
  have hp (i j : I) : IsAffineOpen (U i ⊓ U j) := by
    have h : (⨅ a ∈ (↑({i, j} : Finset I) : Set I), U a) = U i ⊓ U j := by
      apply le_antisymm
      · exact le_inf
          (iInf_le_of_le i (iInf_le _ (Finset.mem_insert_self i {j})))
          (iInf_le_of_le j (iInf_le _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))))
      · refine le_iInf fun a => le_iInf fun ha => ?_
        rcases Finset.mem_insert.mp ha with rfl | hj
        · exact inf_le_left
        · rw [Finset.mem_singleton.mp hj]
          exact inf_le_right
    rw [← h]
    exact hAff {i, j} (Finset.insert_nonempty i {j})
  let W := X.left.openCoverOfIsOpenCover U (show IsOpenCover U from hU)
  let : ∀ i, IsAffine (W.X i) := hs
  have h (i j : W.I₀) : IsAffine (pullback (W.f i) (W.f j)) := by
    let P := U i ⊓ U j
    let : IsAffine P := hp i j
    have hP := IsOpenImmersion.isPullback (X.left.homOfLE (inf_le_left : P ≤ U i))
      (X.left.homOfLE (inf_le_right : P ≤ U j)) (U i).ι (U j).ι (by simp) (by ext; simp)
    exact IsAffine.of_isIso hP.isoPullback.inv
  have : IsAffine (⊤_ Scheme.{u}) := inferInstance
  let := HasAffineProperty.isLocal_affineProperty @IsAffineHom
  exact (HasAffineProperty.diagonal_iff (P := @IsAffineHom)).mp
    (AffineTargetMorphismProperty.diagonal_of_openCover_source
      (terminal.from X.left) W h)

section SumCover

variable {A : Type u} [CommRing A] {X : SchemeOverRing A}
  {I J : Type u} [LinearOrder I] [LinearOrder J] (U : I → X.left.Opens) (V : J → X.left.Opens)

private def coverSum : I ⊕ₗ J → X.left.Opens := fun z => Sum.elim U V (ofLex z)

private def coverInl : I ↪o I ⊕ₗ J := OrderEmbedding.ofStrictMono _ Sum.Lex.inl_strictMono
private def coverInr : J ↪o I ⊕ₗ J := OrderEmbedding.ofStrictMono _ Sum.Lex.inr_strictMono

private theorem coverSum_isCover (hU : (⨆ i, U i) = ⊤) : (⨆ i, coverSum U V i) = ⊤ := by
  apply top_unique
  rw [← hU]
  exact iSup_le fun i => le_iSup (coverSum U V) (coverInl i)

private theorem coverSum_tupleAffine [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (n : ℕ) (e : Fin (n + 1) ↪o (I ⊕ₗ J)) : IsAffineOpen (tupleOpen (coverSum U V) e) := by
  apply IsAffineOpen.iInf
  intro i
  cases h : ofLex (e i) with
  | inl j => exact (show IsAffineOpen (Sum.elim U V (ofLex (e i))) by rw [h]; exact hU j)
  | inr j => exact (show IsAffineOpen (Sum.elim U V (ofLex (e i))) by rw [h]; exact hV j)

end SumCover

section Subcover

variable {A : Type u} [CommRing A] {X : SchemeOverRing A}
  {I J : Type u} [LinearOrder I] [LinearOrder J] (e : I ↪o J) (V : J → X.left.Opens)

/-- The projection onto the coordinates indexed by an ordered subfamily. -/
private def cechRestrictIndex : sheafCechFunctor V ⟶ sheafCechFunctor (V ∘ e) where
  app F := by
    let P := coefficientPresheaf F
    let a (n : ℕ) : (SheafCech V F).X n ⟶ (SheafCech (V ∘ e) F).X n :=
      ModuleCat.ofHom <| LinearMap.pi fun i => LinearMap.proj (i.trans e)
    have h (d d' : SemiSimplexCategory) (l : d ⟶ d') :
        (orderedCochains V P).map l ≫ a d'.len = a d.len ≫ (orderedCochains (V ∘ e) P).map l := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext i
      change P.map (homOfLE (tupleOpen_le V (i.trans e) (SemiSimplexCategory.homEquiv l))).op
        (x ((SemiSimplexCategory.homEquiv l).trans (i.trans e))) =
        P.map (homOfLE (tupleOpen_le (V ∘ e) i (SemiSimplexCategory.homEquiv l))).op
          (x (((SemiSimplexCategory.homEquiv l).trans i).trans e))
      rfl
    refine Hom.mk a fun n m hnm => ?_
    change n + 1 = m at hnm
    subst m
    change a n ≫ (Specs.OrderedCechComparison.cechComplex (V ∘ e) P).d n (n + 1) =
      (Specs.OrderedCechComparison.cechComplex V P).d n (n + 1) ≫ a (n + 1)
    simp only [Specs.OrderedCechComparison.cechComplex, CochainComplex.of_d, differential,
      Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    exact Finset.sum_congr rfl fun i _ => congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
      (h _ _ (coface i)).symm
  naturality {F G} f := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private theorem sectionAugmentation_restrictIndex (F : X.left.Modules) :
    sectionAugmentation V F ≫ ((cechRestrictIndex e V).app F).f 0 =
      sectionAugmentation (V ∘ e) F := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

open LinearAlgebraicGroups.OrderedCechComparison (coefficientComplexAugmentation)
open private extendDoubleMap extendDoubleMap_f intEmbedding_at intEmbedding_not_negative
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison

set_option maxHeartbeats 600000 in
private theorem comparison_restrictIndex [Fintype I] [Fintype J]
    (hV : (⨆ i, V i) = ⊤) (hU : (⨆ i, (V ∘ e) i) = ⊤)
    (F : X.left.Modules) (hF : IntersectionAcyclic V F)
    (hF' : IntersectionAcyclic (V ∘ e) F) (c : ComparisonFamily.{u})
    (hc : IsResolutionComparison c) (n : ℕ) :
    (c X V hV F hF n).hom ≫ homologyMap ((cechRestrictIndex e V).app F) n =
      (c X (V ∘ e) hU F hF' n).hom := by
  let U := V ∘ e
  let L := injectiveResolution F
  let G := ((sectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj L.cocomplex
  let cV := c X V hV F hF n
  let cU := c X U hU F hF' n
  let K := resolutionDouble V L.cocomplex
  let K' := resolutionDouble U L.cocomplex
  let D := extendDouble K
  let D' := extendDouble K'
  let T := cechRestrictIndex e V
  let s := T.app F
  let m : K ⟶ K' := (HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map
    ((NatTrans.mapHomologicalComplex T (.up ℕ)).app L.cocomplex)
  let M := extendDoubleMap (K := K) (L := K') (𝟭 (ModuleCat.{u} A)) m
  obtain ⟨t, ht, _⟩ := CechFirstQuadrantTotalization.totalMapExists (𝟭 (ModuleCat.{u} A)) D D' M
  obtain ⟨a, b, qa, qb, ha, hb, h⟩ := hc X V hV F hF L n
  obtain ⟨a', b', qa', qb', ha', hb', h'⟩ := hc X U hU F hF' L n
  have hs (p q : ℕ) : (m.f p).f q = (T.app (L.cocomplex.X q)).f p := rfl
  have ht' (p q r : ℤ) (hr : p + q = r) :
      D.ιTotal (.up ℤ) p q r hr ≫ t.f r = (M.f p).f q ≫ D'.ιTotal (.up ℤ) p q r hr :=
    ht p q r hr
  have hm (p q : ℕ) : (doubleComponentIso K p q).inv ≫ (M.f (p : ℤ)).f (q : ℤ) =
      (m.f p).f q ≫ (doubleComponentIso K' p q).inv := by
    apply (cancel_mono (doubleComponentIso K' p q).hom).mp
    have hh := extendDoubleMap_f (K := K) (L := K') (𝟭 (ModuleCat.{u} A)) m p q
    change (M.f (p : ℤ)).f (q : ℤ) ≫ (doubleComponentIso K' p q).hom =
      (doubleComponentIso K p q).hom ≫ (m.f p).f q at hh
    simp only [Category.assoc, hh, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hrow : a ≫ t = a' := by
    apply HomologicalComplex.hom_ext
    intro j
    by_cases hj : j < 0
    · exact (G.isZero_extend_X intEmbedding j (intEmbedding_not_negative j hj)).eq_of_src _ _
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j)
      rw [HomologicalComplex.comp_f, ha q, ha' q]
      change ((G.extendXIso intEmbedding (intEmbedding_at q)).hom ≫
        sectionAugmentation V (L.cocomplex.X q) ≫ (doubleComponentIso K 0 q).inv ≫
        D.ιTotal (.up ℤ) 0 (q : ℤ) (q : ℤ) (zero_add _)) ≫ t.f (q : ℤ) =
        (G.extendXIso intEmbedding (intEmbedding_at q)).hom ≫
        sectionAugmentation U (L.cocomplex.X q) ≫ (doubleComponentIso K' 0 q).inv ≫
        D'.ιTotal (.up ℤ) 0 (q : ℤ) (q : ℤ) (zero_add _)
      have hm0 := hm 0 q
      change (doubleComponentIso K 0 q).inv ≫ (M.f 0).f (q : ℤ) =
        (m.f 0).f q ≫ (doubleComponentIso K' 0 q).inv at hm0
      have hAug := sectionAugmentation_restrictIndex e V (L.cocomplex.X q)
      change sectionAugmentation V (L.cocomplex.X q) ≫ (T.app (L.cocomplex.X q)).f 0 =
        sectionAugmentation U (L.cocomplex.X q) at hAug
      simp only [Category.assoc, ht' 0 (q : ℤ), reassoc_of% hm0, hs, reassoc_of% hAug]
  have hcol : b ≫ t = extendMap s intEmbedding ≫ b' := by
    apply HomologicalComplex.hom_ext
    intro j
    by_cases hj : j < 0
    · exact ((SheafCech V F).isZero_extend_X intEmbedding j
        (intEmbedding_not_negative j hj)).eq_of_src _ _
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j)
      have hn := HomologicalComplex.congr_hom (T.naturality (L.ι.f 0)) p
      change ((sheafCechFunctor V).map (L.ι.f 0)).f p ≫ (T.app (L.cocomplex.X 0)).f p =
        s.f p ≫ ((sheafCechFunctor U).map (L.ι.f 0)).f p at hn
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hb p, hb' p,
        extendMap_f s _ (intEmbedding_at p)]
      let o := (SheafCech V F).extendXIso intEmbedding (intEmbedding_at p)
      let o' := (SheafCech U F).extendXIso intEmbedding (intEmbedding_at p)
      change (o.hom ≫ ((sheafCechFunctor V).map (L.ι.f 0)).f p ≫
        (doubleComponentIso K p 0).inv ≫ D.ιTotal (.up ℤ) (p : ℤ) 0 (p : ℤ) (add_zero _)) ≫
        t.f (p : ℤ) = (o.hom ≫ s.f p ≫ o'.inv) ≫ o'.hom ≫
        ((sheafCechFunctor U).map (L.ι.f 0)).f p ≫ (doubleComponentIso K' p 0).inv ≫
        D'.ιTotal (.up ℤ) (p : ℤ) 0 (p : ℤ) (add_zero _)
      have hm0 := hm p 0
      change (doubleComponentIso K p 0).inv ≫ (M.f (p : ℤ)).f 0 =
        (m.f p).f 0 ≫ (doubleComponentIso K' p 0).inv at hm0
      simp only [Category.assoc, ht' (p : ℤ) 0, reassoc_of% hm0, hs,
        reassoc_of% hn, Iso.inv_hom_id_assoc]
  let iV := (SheafCech V F).extendHomologyIso intEmbedding (intEmbedding_at n)
  let iU := (SheafCech U F).extendHomologyIso intEmbedding (intEmbedding_at n)
  let iG := G.extendHomologyIso intEmbedding (intEmbedding_at n)
  let r := L.isoRightDerivedObj (sectionsFunctor X) n
  have hs' : iV.inv ≫ homologyMap (extendMap s intEmbedding) (n : ℤ) =
      homologyMap s n ≫ iU.inv := by
    apply (cancel_mono iU.hom).mp
    have he := extendHomologyIso_hom_naturality s intEmbedding (intEmbedding_at n)
    change homologyMap (extendMap s intEmbedding) (n : ℤ) ≫ iU.hom =
      iV.hom ≫ homologyMap s n at he
    simp only [Category.assoc, he, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change cV.hom ≫ iV.inv ≫ homologyMap b (n : ℤ) = r.hom ≫ iG.inv ≫ homologyMap a (n : ℤ) at h
  change cU.hom ≫ iU.inv ≫ homologyMap b' (n : ℤ) = r.hom ≫ iG.inv ≫ homologyMap a' (n : ℤ) at h'
  change cV.hom ≫ homologyMap s n = cU.hom
  let : QuasiIso b' := qb'
  apply (cancel_mono (iU.inv ≫ homologyMap b' (n : ℤ))).mp
  calc
    _ = cV.hom ≫ iV.inv ≫ homologyMap (b ≫ t) (n : ℤ) := by
      simp only [hcol, homologyMap_comp, Category.assoc, reassoc_of% hs']
    _ = r.hom ≫ iG.inv ≫ homologyMap (a ≫ t) (n : ℤ) := by
      have h₁ := congrArg (· ≫ homologyMap t (n : ℤ)) h
      simpa only [homologyMap_comp, Category.assoc] using h₁
    _ = cU.hom ≫ iU.inv ≫ homologyMap b' (n : ℤ) := by
      rw [hrow]
      exact h'.symm
    _ = _ := rfl

end Subcover

section CoverIndependence

open private singletonTuple tupleOpen_singleton
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison

private theorem cechConnecting_restrictIndex {A : Type u} [CommRing A] {X : SchemeOverRing A}
    {I J : Type u} [LinearOrder I] [Fintype I] [LinearOrder J] [Fintype J]
    (e : I ↪o J) (V : J → X.left.Opens) (hV : (⨆ j, V j) = ⊤)
    (hU : (⨆ i, (V ∘ e) i) = ⊤) (S : ShortComplex X.left.Modules)
    (h₁ : IntersectionAcyclic V S.X₁) (h₃ : IntersectionAcyclic V S.X₃)
    (g₁ : IntersectionAcyclic (V ∘ e) S.X₁) (g₃ : IntersectionAcyclic (V ∘ e) S.X₃)
    (s : (S.map (sheafCechFunctor V)).ShortExact)
    (t : (S.map (sheafCechFunctor (V ∘ e))).ShortExact) (n : ℕ) :
    cechConnecting X V hV S h₁ h₃ orderedCechComparisonIso s n =
      cechConnecting X (V ∘ e) hU S g₁ g₃ orderedCechComparisonIso t n := by
  let U := V ∘ e
  let v₁ := orderedCechComparisonIso X V hV S.X₁ h₁ (n + 1)
  let v₃ := orderedCechComparisonIso X V hV S.X₃ h₃ n
  let u₁ := orderedCechComparisonIso X U hU S.X₁ g₁ (n + 1)
  let u₃ := orderedCechComparisonIso X U hU S.X₃ g₃ n
  let r := S.mapNatTrans (cechRestrictIndex e V)
  have h₁' : v₁.hom ≫ homologyMap r.τ₁ (n + 1) = u₁.hom :=
    comparison_restrictIndex e V hV hU S.X₁ h₁ g₁ _ canonicalResolutionComparison (n + 1)
  have h₃' : v₃.hom ≫ homologyMap r.τ₃ n = u₃.hom :=
    comparison_restrictIndex e V hV hU S.X₃ h₃ g₃ _ canonicalResolutionComparison n
  have hr : v₁.inv ≫ u₁.hom = homologyMap r.τ₁ (n + 1) := by
    rw [← h₁', Iso.inv_hom_id_assoc]
  have hd := HomologicalComplex.HomologySequence.δ_naturality r s t n (n + 1) rfl
  apply (cancel_mono u₁.hom).mp
  change (v₃.hom ≫ s.δ n (n + 1) rfl ≫ v₁.inv) ≫ u₁.hom =
    (u₃.hom ≫ t.δ n (n + 1) rfl ≫ u₁.inv) ≫ u₁.hom
  simp only [Category.assoc, hr, Iso.inv_hom_id, Category.comp_id, hd, reassoc_of% h₃']

private theorem cechConnecting_eq_of_covers {A : Type u} [CommRing A] {X : SchemeOverRing A}
    (hX : HasFiniteAffineCover X) {I J : Type u} [LinearOrder I] [Fintype I]
    [LinearOrder J] [Fintype J] (U : I → X.left.Opens) (V : J → X.left.Opens)
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤)
    (hU' : ∀ i, IsAffineOpen (U i)) (hV' : ∀ j, IsAffineOpen (V j))
    (S : ShortComplex X.left.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] (hS : S.ShortExact)
    (h₁ : IntersectionAcyclic U S.X₁) (h₃ : IntersectionAcyclic U S.X₃)
    (g₁ : IntersectionAcyclic V S.X₁) (g₃ : IntersectionAcyclic V S.X₃)
    (s : (S.map (sheafCechFunctor U)).ShortExact)
    (t : (S.map (sheafCechFunctor V)).ShortExact) (n : ℕ) :
    cechConnecting X U hU S h₁ h₃ orderedCechComparisonIso s n =
      cechConnecting X V hV S g₁ g₃ orderedCechComparisonIso t n := by
  let : IsAffineHom (pullback.diagonal (terminal.from X.left)) := isAffineDiagonal X hX
  let : Fintype (I ⊕ₗ J) := inferInstanceAs (Fintype (I ⊕ J))
  let W := coverSum U V
  let hW := coverSum_isCover U V hU
  have hW' (i : ℕ) (e : Fin (i + 1) ↪o (I ⊕ₗ J)) : IsAffineOpen (tupleOpen W e) :=
    coverSum_tupleAffine U V hU' hV' i e
  let r₁ := intersectionAcyclic_of_isAffine W (hW' _) S.X₁ inferInstance
  let r₃ := intersectionAcyclic_of_isAffine W (hW' _) S.X₃ inferInstance
  let r := cechShortExact W hW' S hS
  have hl := cechConnecting_restrictIndex (coverInl : I ↪o I ⊕ₗ J) W hW hU S r₁ r₃ h₁ h₃ r s n
  have hr := cechConnecting_restrictIndex (coverInr : J ↪o I ⊕ₗ J) W hW hV S r₁ r₃ g₁ g₃ r t n
  exact hl.symm.trans hr

private theorem coverAffine (A : Type u) [CommRing A] (X : SchemeOverRing A)
    {I : Type u} [LinearOrder I] (U : I → X.left.Opens)
    (hU : ∀ (n : ℕ) (e : Fin (n + 1) ↪o I), IsAffineOpen (tupleOpen U e)) (i : I) :
    IsAffineOpen (U i) := by
  have h := hU 0 (singletonTuple i)
  change IsAffineOpen (Specs.OrderedCechComparison.tupleOpen U (singletonTuple i)) at h
  rwa [tupleOpen_singleton] at h

end CoverIndependence

section LongExactSequence

private theorem cohomologyMap_cech_coefficients {A : Type u} [CommRing A] {X : SchemeOverRing A}
    {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens) (hU : (⨆ i, U i) = ⊤)
    {F G : X.left.Modules} (a : F ⟶ G) (hF : IntersectionAcyclic U F)
    (hG : IntersectionAcyclic U G) (n : ℕ) :
    (cohomology X n).map a ≫ (orderedCechComparisonIso X U hU G hG n).hom =
      (orderedCechComparisonIso X U hU F hF n).hom ≫ homologyMap ((sheafCechFunctor U).map a) n := by
  let J := injectiveResolution F
  let K := injectiveResolution G
  rw [orderedCechComparisonIso_eq X U hU F hF J n, orderedCechComparisonIso_eq X U hU G hG K n]
  exact resolutionComparison_coefficients U J K
    (resolutionAugmentations U J hU hF) (resolutionAugmentations U K hU hG) a n

private theorem functionExact_of_isos {A : Type u} [CommRing A] {M N P M' N' P' : ModuleCat.{u} A}
    {f : M ⟶ N} {g : N ⟶ P} {f' : M' ⟶ N'} {g' : N' ⟶ P'}
    (eM : M ≅ M') (eN : N ≅ N') (eP : P ≅ P')
    (hf : f ≫ eN.hom = eM.hom ≫ f') (hg : g ≫ eP.hom = eN.hom ≫ g')
    (h : Function.Exact f' g') : Function.Exact f g := by
  intro y
  have e (x : M) : eN.hom (f x) = f' (eM.hom x) := ConcreteCategory.congr_hom hf x
  have e' : eP.hom (g y) = g' (eN.hom y) := ConcreteCategory.congr_hom hg y
  constructor
  · intro hy
    obtain ⟨x', hx'⟩ := (h (eN.hom y)).mp (by rw [← e', hy, map_zero])
    let x := eM.inv x'
    have hxx' : eM.hom x = x' := ConcreteCategory.congr_hom eM.inv_hom_id x'
    exact ⟨x, eN.toLinearEquiv.injective ((e x).trans (hxx' ▸ hx'))⟩
  · rintro ⟨x, rfl⟩
    apply eP.toLinearEquiv.injective
    change eP.hom (g (f x)) = eP.hom 0
    rw [← show g' (eN.hom (f x)) = eP.hom (g (f x)) from
      (ConcreteCategory.congr_hom hg (f x)).symm, e,
      (h (f' (eM.hom x))).mpr ⟨_, rfl⟩, map_zero]

private theorem cechConnecting_longExact {A : Type u} [CommRing A] {X : SchemeOverRing A}
    {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens) (hU : (⨆ i, U i) = ⊤)
    (S : ShortComplex X.left.Modules) (h₁ : IntersectionAcyclic U S.X₁)
    (h₂ : IntersectionAcyclic U S.X₂) (h₃ : IntersectionAcyclic U S.X₃)
    (s : (S.map (sheafCechFunctor U)).ShortExact) :
    IsLongExactSequence X S (cechConnecting X U hU S h₁ h₃ orderedCechComparisonIso s) := by
  let K := S.map (sheafCechFunctor U)
  let e₁ n := orderedCechComparisonIso X U hU S.X₁ h₁ n
  let e₂ n := orderedCechComparisonIso X U hU S.X₂ h₂ n
  let e₃ n := orderedCechComparisonIso X U hU S.X₃ h₃ n
  let d := cechConnecting X U hU S h₁ h₃ orderedCechComparisonIso s
  have hf (n : ℕ) : (cohomology X n).map S.f ≫ (e₂ n).hom =
      (e₁ n).hom ≫ homologyMap K.f n := cohomologyMap_cech_coefficients U hU S.f h₁ h₂ n
  have hg (n : ℕ) : (cohomology X n).map S.g ≫ (e₃ n).hom =
      (e₂ n).hom ≫ homologyMap K.g n := cohomologyMap_cech_coefficients U hU S.g h₂ h₃ n
  have hd (n : ℕ) : d n ≫ (e₁ (n + 1)).hom = (e₃ n).hom ≫ s.δ n (n + 1) rfl := by
    change ((e₃ n).hom ≫ s.δ n (n + 1) rfl ≫ (e₁ (n + 1)).inv) ≫ (e₁ (n + 1)).hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨?_, ?_, ?_, ?_⟩
  · let : Mono K.f := s.mono_f
    let : Mono (homologyMap K.f 0) := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel K.f 0 (by simp)
    have hmono : Mono ((cohomology X 0).map S.f ≫ (e₂ 0).hom) := by
      rw [hf]
      infer_instance
    have : Mono ((cohomology X 0).map S.f) := mono_of_mono _ (e₂ 0).hom
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  · intro n
    exact functionExact_of_isos (e₁ n) (e₂ n) (e₃ n) (hf n) (hg n)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (s.homology_exact₂ n))
  · intro n
    exact functionExact_of_isos (e₂ n) (e₃ n) (e₁ (n + 1)) (hg n) (hd n)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (s.homology_exact₃ n (n + 1) rfl))
  · intro n
    exact functionExact_of_isos (e₃ n) (e₁ (n + 1)) (e₂ (n + 1)) (hd n) (hf (n + 1))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (s.homology_exact₁ n (n + 1) rfl))

open private tupleOpen_isAffine_of_finite_intersections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

private theorem exists_connectingMaps {A : Type u} [CommRing A] (X : SchemeOverRing A)
    (hX : HasFiniteAffineCover X) (S : ShortComplex X.left.Modules) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (hS : S.ShortExact) :
    ∃ d : ConnectingMaps X S, IsLongExactSequence X S d ∧
      ComputesConnectingUsingCech orderedCechComparisonIso X S d := by
  classical
  have H := hX
  obtain ⟨I, hI, U, hU, hAff⟩ := H
  let : Fintype I := hI
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hU' (n : ℕ) (e : Fin (n + 1) ↪o I) : IsAffineOpen (tupleOpen U e) :=
    tupleOpen_isAffine_of_finite_intersections U hAff e
  let h₁ := intersectionAcyclic_of_isAffine U (hU' _) S.X₁ inferInstance
  let h₂ := intersectionAcyclic_of_isAffine U (hU' _) S.X₂ inferInstance
  let h₃ := intersectionAcyclic_of_isAffine U (hU' _) S.X₃ inferInstance
  let s := cechShortExact U hU' S hS
  refine ⟨_, cechConnecting_longExact U hU S h₁ h₂ h₃ s, ?_⟩
  intro J _ _ V hV hV'
  let g₁ := intersectionAcyclic_of_isAffine V (hV' _) S.X₁ inferInstance
  let g₃ := intersectionAcyclic_of_isAffine V (hV' _) S.X₃ inferInstance
  let t := cechShortExact V hV' S hS
  exact ⟨g₁, g₃, t, fun n => cechConnecting_eq_of_covers hX U V hU hV
    (coverAffine A X U hU') (coverAffine A X V hV') S hS h₁ h₃ g₁ g₃ s t n⟩

private theorem connectingNaturality : ConnectingNaturality orderedCechComparisonIso.{u} := by
  intro A B _ _ X Y φ f _ w hX S T α d e hd he n m₁ m₃ hm₁ hm₃
  classical
  obtain ⟨I, hI, U, hU, hAff⟩ := hX
  let : Fintype I := hI
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  let V := pullbackCover f U
  let hV := f.iSup_preimage_eq_top hU
  have hU' (i : ℕ) (e : Fin (i + 1) ↪o I) : IsAffineOpen (tupleOpen U e) :=
    tupleOpen_isAffine_of_finite_intersections U hAff e
  have hV' (i : ℕ) (e : Fin (i + 1) ↪o I) : IsAffineOpen (tupleOpen V e) := by
    change IsAffineOpen (Specs.OrderedCechComparison.tupleOpen V e)
    rw [Specs.OrderedCechComparison.tupleOpen_pullback f U e]
    exact (hU' i e).preimage f
  obtain ⟨h₁, h₃, s, hs⟩ := hd U hU hU'
  obtain ⟨g₁, g₃, t, ht⟩ := he V hV hV'
  rw [hs n, ht n]
  exact cechConnecting_pullback φ f w U hU α h₁ h₃ g₁ g₃ s t n hm₁ hm₃

private theorem connectingBaseChange : BaseChangeConnecting orderedCechComparisonIso.{u} := by
  intro k _ X hX R S Y T d e hd he n b₁ b₃ hb₁ hb₃
  let p := extensionProjection R X
  let P := pushforward p
  let a := (Scheme.Modules.pullbackPushforwardAdjunction p).unit
  let α : S ⟶ T.map P :=
    { τ₁ := a.app S.X₁
      τ₂ := a.app S.X₂
      τ₃ := a.app S.X₃
      comm₁₂ := (a.naturality S.f).symm
      comm₂₃ := (a.naturality S.g).symm }
  let : IsAffineHom p := MorphismProperty.pullback_fst _ _ inferInstance
  let A := ModuleCat.extendRestrictScalarsAdj (algebraMap k R)
  apply (A.homEquiv _ _).injective
  rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right]
  exact connectingNaturality (algebraMap k R) p (extensionProjection_over R X) hX α hd he n hb₁ hb₃


end LongExactSequence

section LinearizedConnecting

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.EquivariantAffineModules (Pull)
open private actionProductIso actionProductIso_hom_snd
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus

private theorem affinePullback_hasFiniteAffineCover {A B : Type u} [CommRing A] [CommRing B]
    {X : SchemeOverRing A} {Y : SchemeOverRing B} (f : Y.left ⟶ X.left) [IsAffineHom f]
    (hX : HasFiniteAffineCover X) : HasFiniteAffineCover Y := by
  obtain ⟨I, hI, U, hU, hAff⟩ := hX
  refine ⟨I, hI, fun i => f ⁻¹ᵁ U i, f.iSup_preimage_eq_top hU, fun s hs => ?_⟩
  have he := map_finset_inf f.base.frameHom s U
  simp only [Finset.inf_eq_iInf] at he
  change f ⁻¹ᵁ (⨅ i ∈ (s : Set I), U i) = _ at he
  exact (congrArg IsAffineOpen he).mp ((hAff s hs).preimage f)

private theorem over_cohomologyMap_exists {k : Type u} [Field k] {X Y : SchemeOver k}
    (f : Y ⟶ X) [Flat f.left] {F : X.left.Modules} {G : Y.left.Modules}
    (c : Pull f F ⟶ G) (n : ℕ) : ∃ m, IsOverCohomologyMap f c n m := by
  let α := (pullbackPushforwardAdjunction f.left).homEquiv F G c
  have hw : f.left ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    rw [show Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _ from Spec.map_id _, Category.comp_id]
    exact Over.w f
  obtain ⟨m, hm⟩ := flatCohomologyMap_bridge (X := X) (Y := Y) (RingHom.id k) f.left hw α n
  let e := ModuleCat.restrictScalarsId'App (RingHom.id k) rfl ((cohomology Y n).obj G)
  refine ⟨m ≫ e.hom, ?_⟩
  change IsCohomologyMap (RingHom.id k) f.left hw α n ((m ≫ e.hom) ≫ e.inv)
  simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using hm

private theorem over_connectingNaturality {k : Type u} [Field k] {X Y : SchemeOver k}
    (f : Y ⟶ X) [IsAffineHom f.left] [Flat f.left] (hX : HasFiniteAffineCover X)
    {S : ShortComplex X.left.Modules} {T : ShortComplex Y.left.Modules}
    (c : S.map (Scheme.Modules.pullback f.left) ⟶ T)
    {d : ConnectingMaps X S} {e : ConnectingMaps Y T}
    (hd : ComputesConnectingUsingCech orderedCechComparisonIso X S d)
    (he : ComputesConnectingUsingCech orderedCechComparisonIso Y T e) :
    ConnectsForOverMap f c.τ₁ c.τ₃ d e := by
  refine ⟨fun n => ⟨over_cohomologyMap_exists f c.τ₁ (n + 1), over_cohomologyMap_exists f c.τ₃ n⟩, ?_⟩
  intro n m₁ m₃ hm₁ hm₃
  let A := pullbackPushforwardAdjunction f.left
  let α : S ⟶ T.map (pushforward f.left) :=
    { τ₁ := A.homEquiv _ _ c.τ₁
      τ₂ := A.homEquiv _ _ c.τ₂
      τ₃ := A.homEquiv _ _ c.τ₃
      comm₁₂ := by
        change A.homEquiv _ _ c.τ₁ ≫ (pushforward f.left).map T.f = S.f ≫ A.homEquiv _ _ c.τ₂
        rw [← A.homEquiv_naturality_right, ← A.homEquiv_naturality_left]
        exact congrArg (A.homEquiv _ _) c.comm₁₂
      comm₂₃ := by
        change A.homEquiv _ _ c.τ₂ ≫ (pushforward f.left).map T.g = S.g ≫ A.homEquiv _ _ c.τ₃
        rw [← A.homEquiv_naturality_right, ← A.homEquiv_naturality_left]
        exact congrArg (A.homEquiv _ _) c.comm₂₃ }
  let φ := RingHom.id k
  have w : f.left ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [show Spec.map (CommRingCat.ofHom φ) = 𝟙 _ from Spec.map_id _, Category.comp_id]
    exact Over.w f
  let i₁ := ModuleCat.restrictScalarsId'App φ rfl ((cohomology Y (n + 1)).obj T.X₁)
  let i₃ := ModuleCat.restrictScalarsId'App φ rfl ((cohomology Y n).obj T.X₃)
  have h := connectingNaturality φ f.left w hX α hd he n
    (m₁ := m₁ ≫ i₁.inv) (m₃ := m₃ ≫ i₃.inv) hm₁ hm₃
  apply (cancel_mono i₁.inv).mp
  rw [Category.assoc, Category.assoc, ModuleCat.restrictScalarsId'App_inv_naturality φ rfl]
  exact h.trans (Category.assoc _ _ _)

private theorem linearizedConnecting : LinearizedConnecting orderedCechComparisonIso.{u} := by
  intro k _ H _ X hX a S _ _ _ hS l₁ l₂ l₃ hf hg
  let Y := H.X ⊗ X
  let p : Y ⟶ X := snd H.X X
  let q : Y ⟶ X := a.smul
  have pb := Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (fst H.X X) (snd H.X X)) (tensorProductIsBinaryProduct H.X X)
  let : IsAffineHom p.left := MorphismProperty.of_isPullback pb (show IsAffineHom H.X.hom from inferInstance)
  let : Flat p.left := MorphismProperty.of_isPullback pb (show Flat H.X.hom from inferInstance)
  let u := actionProductIso a
  let : IsIso u.hom.left := inferInstanceAs (IsIso ((Over.forget _).map u.hom))
  have w : u.hom.left ≫ p.left = q.left := congrArg Over.Hom.left (actionProductIso_hom_snd a)
  let : IsAffineHom q.left := w ▸ inferInstanceAs (IsAffineHom (u.hom.left ≫ p.left))
  let : Flat q.left := w ▸ inferInstanceAs (Flat (u.hom.left ≫ p.left))
  let hY : HasFiniteAffineCover Y := affinePullback_hasFiniteAffineCover p.left hX
  let Q := Scheme.Modules.pullback q.left
  let T := S.map Q
  let : Q.PreservesHomology := FlatCohomology.flatPullbackExact q.left
  let : PreservesFiniteLimits Q := Functor.preservesFiniteLimits_of_preservesHomology Q
  let : T.X₁.IsQuasicoherent := pullback_isQuasicoherent q.left S.X₁
  let : T.X₂.IsQuasicoherent := pullback_isQuasicoherent q.left S.X₂
  let : T.X₃.IsQuasicoherent := pullback_isQuasicoherent q.left S.X₃
  obtain ⟨d, hd, cd⟩ := exists_connectingMaps X hX S hS
  obtain ⟨e, he, ce⟩ := exists_connectingMaps Y hY T (hS.map_of_exact Q)
  let τ : S.map (Scheme.Modules.pullback p.left) ⟶ T :=
    { τ₁ := l₁.iso.hom
      τ₂ := l₂.iso.hom
      τ₃ := l₃.iso.hom
      comm₁₂ := hf
      comm₂₃ := hg }
  exact ⟨d, e, hd, he, cd, ce,
    over_connectingNaturality p hX τ cd ce, over_connectingNaturality q hX (𝟙 T) cd ce⟩

end LinearizedConnecting

/-- The actual derived global sections have a long exact sequence whose
connecting arrows commute with affine pullback and scalar extension. -/
theorem cohomologyConnecting : CohomologyConnecting.{u} :=
  ⟨orderedCechComparisonIso, canonicalResolutionComparison, @exists_connectingMaps,
    connectingNaturality, connectingBaseChange, linearizedConnecting⟩

section ArbitraryTower

open FlatCohomology (comp_over)
open private homologyTo from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison

private theorem cechCohomology_comp_apply {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {X : SchemeOverRing A} {Y : SchemeOverRing B} {Z : SchemeOverRing C}
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (e : ψ.comp φ = χ)
    (f : Y.left ⟶ X.left) (g : Z.left ⟶ Y.left) (p : Z.left ⟶ X.left) (hp : g ≫ f = p)
    (wf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (wg : g ≫ Y.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom ψ))
    (wp : p ≫ X.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom χ))
    {F : X.left.Modules} {G : Y.left.Modules} {H : Z.left.Modules}
    (α : F ⟶ (pushforward f).obj G) (β : G ⟶ (pushforward g).obj H)
    (γ : F ⟶ (pushforward p).obj H)
    (h : γ ≫ (pushforwardCongr hp.symm).hom.app H =
      α ≫ (pushforward f).map β ≫ (pushforwardComp g f).hom.app H)
    {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens) (hU : (⨆ i, U i) = ⊤)
    (hF : IntersectionAcyclic U F) (hG : IntersectionAcyclic (pullbackCover f U) G)
    (hH : IntersectionAcyclic (pullbackCover g (pullbackCover f U)) H)
    (n : ℕ) {aR aS} (hR : IsCohomologyMap φ f wf α n aR) (hS : IsCohomologyMap χ p wp γ n aS)
    (x : (cohomology X n).obj F) :
    let V := pullbackCover f U
    let W := pullbackCover g V
    let cR := orderedCechComparisonIso Y V (f.iSup_preimage_eq_top hU) G hG n
    let cS := orderedCechComparisonIso Z W (g.iSup_preimage_eq_top (f.iSup_preimage_eq_top hU)) H hH n
    cS.inv (homologyTo (restrict ψ) (cechPullback ψ g wg V β) n (cR.hom (aR x))) = aS x := by
  let V := pullbackCover f U
  let W := pullbackCover g V
  let α' := α ≫ (pushforward f).map β ≫ (pushforwardComp g f).hom.app H
  let wf' := comp_over φ ψ f g wf wg
  let aS' := aS ≫ (ModuleCat.restrictScalarsCongr e.symm).hom.app ((cohomology Z n).obj H)
  have haS' : IsCohomologyMap (ψ.comp φ) (g ≫ f) wf' α' n aS' :=
    cohomologyMap_transport e.symm hp.symm wp wf' h n (by exact hS)
  have hcR := cohomologyMap_cech φ f wf U hU hF hG α n hR
  have hcS := cohomologyMap_cech (ψ.comp φ) (g ≫ f) wf' U hU hF hH α' n haS'
  let cX := orderedCechComparisonIso X U hU F hF n
  let cR := orderedCechComparisonIso Y V (f.iSup_preimage_eq_top hU) G hG n
  let cS := orderedCechComparisonIso Z W (g.iSup_preimage_eq_top (f.iSup_preimage_eq_top hU)) H hH n
  let tR := homologyTo (restrict φ) (cechPullback φ f wf U α) n
  let tS := homologyTo (restrict (ψ.comp φ)) (cechPullback (ψ.comp φ) (g ≫ f) wf' U α') n
  let t := homologyTo (restrict ψ) (cechPullback ψ g wg V β) n
  have ht := cechPullback_homology_comp φ ψ f g wf wg U α β n
  change cS.inv (t (cR.hom (aR x))) = aS x
  apply cS.toLinearEquiv.injective
  change cS.hom (cS.inv (t (cR.hom (aR x)))) = cS.hom (aS x)
  have hi := ConcreteCategory.congr_hom cS.inv_hom_id (t (cR.hom (aR x)))
  change cS.hom (cS.inv (t (cR.hom (aR x)))) = _ at hi
  rw [hi]
  have hr := ConcreteCategory.congr_hom hcR x
  have hs := ConcreteCategory.congr_hom hcS x
  have hh := ConcreteCategory.congr_hom ht (cX.hom x)
  change cR.hom (aR x) = tR (cX.hom x) at hr
  change cS.hom (aS x) = tS (cX.hom x) at hs
  change tS (cX.hom x) = t (tR (cX.hom x)) at hh
  exact (congrArg t hr).trans (hh.symm.trans hs.symm)

private theorem pullbackUnit_tower_symm {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {h : Z ⟶ X} (w : g ≫ f = h) (F : X.Modules) :
    let H := (Scheme.Modules.pullback h).obj F
    let α := (pullbackPushforwardAdjunction f).unit.app F
    let β := (pullbackPushforwardAdjunction g).homEquiv _ _
      (((pullbackComp g f).app F ≪≫ (pullbackCongr w).app F).hom)
    (pullbackPushforwardAdjunction h).unit.app F ≫ (pushforwardCongr w.symm).hom.app H =
      α ≫ (pushforward f).map β ≫ (pushforwardComp g f).hom.app H := by
  intro H α β
  have h := pullbackUnit_tower f g w F
  change α ≫ (pushforward f).map β ≫ (pushforwardComp g f).hom.app H ≫
    (pushforwardCongr w).hom.app H = _ at h
  rw [← h, Category.assoc, Category.assoc, Category.assoc,
    pushforwardCongr_symm_comp w H, Category.comp_id]

set_option maxHeartbeats 600000 in
/-- The tower comparison for an arbitrary morphism of test algebras. -/
theorem baseChangeTower : BaseChangeTower.{u} := by
  refine ⟨orderedCechComparisonIso, canonicalResolutionComparison, ?_⟩
  intro k _ X R S j q hq wq F _ I _ _ U hU hAff n bR bS hbR hbS
  letI : IsAffineHom (extensionProjection R X) := MorphismProperty.pullback_fst _ _ inferInstance
  letI : IsAffineHom (extensionProjection S X) := MorphismProperty.pullback_fst _ _ inferInstance
  have hAV {i : ℕ} (e : Fin (i + 1) ↪o I) :
      IsAffineOpen (Specs.OrderedCechComparison.tupleOpen (pullbackCover (extensionProjection R X) U) e) := by
    rw [tupleOpen_pullback]
    exact (hAff i e).preimage (extensionProjection R X)
  have hAW {i : ℕ} (e : Fin (i + 1) ↪o I) :
      IsAffineOpen (Specs.OrderedCechComparison.tupleOpen
        (pullbackCover q (pullbackCover (extensionProjection R X) U)) e) := by
    change IsAffineOpen (Specs.OrderedCechComparison.tupleOpen
      (pullbackCover (q ≫ extensionProjection R X) U) e)
    rw [tupleOpen_pullback, hq]
    exact (hAff i e).preimage (extensionProjection S X)
  have hF : IntersectionAcyclic U F := intersectionAcyclic_of_isAffine U (hAff _) F inferInstance
  have hG := intersectionAcyclic_of_isAffine (pullbackCover (extensionProjection R X) U) hAV
    ((Scheme.Modules.pullback (extensionProjection R X)).obj F)
    (pullback_isQuasicoherent (extensionProjection R X) F)
  have hH := intersectionAcyclic_of_isAffine (pullbackCover q (pullbackCover (extensionProjection R X) U)) hAW
    ((Scheme.Modules.pullback (extensionProjection S X)).obj F)
    (pullback_isQuasicoherent (extensionProjection S X) F)
  refine ⟨hG, hH, ?_⟩
  refine cechCohomology_comp_apply (X := X) (Y := (extendScheme R).obj X) (Z := (extendScheme S).obj X)
    (algebraMap k R) j.hom.toRingHom (algebraMap k S) j.hom.comp_algebraMap
    (extensionProjection R X) q (extensionProjection S X) hq
    (extensionProjection_over R X) wq (extensionProjection_over S X)
    ((pullbackPushforwardAdjunction (extensionProjection R X)).unit.app F) (towerCoefficient F q hq)
    ((pullbackPushforwardAdjunction (extensionProjection S X)).unit.app F)
    (pullbackUnit_tower_symm (extensionProjection R X) q hq F) U hU hF hG hH n
    (aR := (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ bR)
    (aS := (ModuleCat.extendRestrictScalarsAdj (algebraMap k S)).homEquiv _ _ bS) hbR hbS

end ArbitraryTower

end LinearAlgebraicGroups.Representation.CoherentCohomologyAlgebraBaseChange
