import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactGenerators
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.MoritaCriterion
import Mathlib.CategoryTheory.Adjunction.Additive
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedBimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.MoritaUnit
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open scoped DirectSum

universe u v w z vA t s j o m

namespace DerivedFormalization.DGBimodule

open Specs.DerivedFormalization.DG
open BalancedTensor (tmul left)
open BimoduleAdjunction (asMixed ModuleEquiv restrictLifted ordinaryHom ordinaryTensor)
open CoefficientLift (liftModule liftCategory)
open CoefficientLiftComparison (CUp)
open DerivedBimoduleAdjunction
open MoritaCriterion
open MoritaUnit (MoritaUnitAt MoritaUnitTransition MorphismQuasiIsomorphisms toComplexHom)
open HomComplex (component gradedHom homotopyClass)
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open CompactRepresentables (IsCompact LocalizationMapAdditive coproductHomMap)

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.checkUnivs false
set_option linter.style.haveILetI false

section Ambient

variable {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,z} k}
variable (X Y : RightDGModuleModel B)
variable {X' Y' : RightDGModuleModel (liftCategory.{u,v,z,max z t} B)}
variable (ex : liftModule.{u,v,z,max z t} X = X') (ey : liftModule.{u,v,z,max z t} Y = Y')

/-- The coefficient lift identifies the Hom complex through conjugation in each degree. -/
private def liftHomComplexIso :
    CUp.{u,max v z,t} (HomComplex.homComplex X Y) ≅ HomComplex.homComplex X' Y' := by
  let C := CUp.{u,max v z,t} (HomComplex.homComplex X Y)
  let E := HomComplex.homComplex (liftModule.{u,v,z,max z t} X) (liftModule.{u,v,z,max z t} Y)
  let eTerm (n : ℤ) : C.X n ≅ E.X n := by
    change ModuleCat.of k (ULift.{t} (gradedHom X Y n)) ≅
      ModuleCat.of k (gradedHom (liftModule.{u,v,z,max z t} X) (liftModule.{u,v,z,max z t} Y) n)
    exact (ULift.moduleEquiv.trans (DG.CoefficientLift.gradedEquiv.{u,v,z,max z t} X Y n)).toModuleIso
  let e : C ≅ E := Hom.isoOfComponents eTerm (fun i n _ => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change E.d i n (DG.CoefficientLift.gradedEquiv.{u,v,z,max z t} X Y i x.down) =
      DG.CoefficientLift.gradedEquiv.{u,v,z,max z t} X Y n ((HomComplex.homComplex X Y).d i n x.down)
    exact (DG.CoefficientLift.gradedEquiv_comm_d.{u,v,z,max z t} i n x.down).symm)
  exact e ≪≫ eqToIso (congrArg₂ (fun P Q => HomComplex.homComplex P Q) ex ey)

private theorem liftHomComplexIso_apply
    (eX : ModuleEquiv (asMixed X) (restrictLifted (asMixed X')))
    (eY : ModuleEquiv (asMixed Y) (restrictLifted (asMixed Y')))
    (hx : ∀ c i (x : (X.complex c).X i), HEq (eX.degree c i x) (ULift.up.{max z t} x))
    (hy : ∀ c i (y : (Y.complex c).X i), HEq (eY.degree c i y) (ULift.up.{max z t} y))
    (r : ℤ) (g : gradedHom X Y r) (c : B.Obj) (i n : ℤ) (h : i+r=n)
    (x : (X.complex c).X i) :
    component ((liftHomComplexIso X Y ex ey).hom.f r (ULift.up g)) c i n h
      (eX.degree c i x) = eY.degree c n (component g c i n h x) := by
  subst X'
  subst Y'
  rw [eq_of_heq (hx c i x), eq_of_heq (hy c n (component g c i n h x))]
  simp only [liftHomComplexIso, eqToIso_refl, Iso.trans_refl]
  rfl

private theorem ambientMorphismComparison :
    AmbientMorphismQuasiIsomorphisms.{u,v,w,z,vA,t} := by
  intro k _ A B T model a b
  dsimp only
  let e := liftHomComplexIso.{u,v,z,max vA w t} (T.obj a) (T.obj b)
    (model.comparisonLaws.obj_eq a).symm (model.comparisonLaws.obj_eq b).symm
  have he := liftHomComplexIso_apply (T.obj a) (T.obj b)
    (model.comparisonLaws.obj_eq a).symm (model.comparisonLaws.obj_eq b).symm (model.comparison a) (model.comparison b)
    (model.comparisonLaws.term_up a) (model.comparisonLaws.term_up b)
  refine ⟨e, he, ?_⟩
  have hf : liftCochainMap.{u,vA,max v z,max w t} (T.map a b) ≫ e.hom =
      toComplexHom (model.bimodule.map a b) := by
    apply HomologicalComplex.hom_ext
    intro r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply RightDGModule.GradedHom.ext
    intro c i n h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (model.comparison a |>.degree c i).surjective x
    change component (e.hom.f r (ULift.up ((T.map a b).f r f.down))) c i n h
      ((model.comparison a).degree c i y) =
      component ((model.bimodule.map a b).f r f) c i n h ((model.comparison a).degree c i y)
    rw [he]
    exact model.comparisonLaws.left_action c r i n (by omega) f.down y
  exact ⟨hf, hf ▸ (quasiIso_iff_comp_right _ e.hom).symm⟩

end Ambient

open private coproductHomMap_of coproductHomMap_injective coproductHomMap_surjective_of_iso
  coproductHomMap_surjective_of_cover realizedSum_surjective shiftZeroIso
  cellDerivedEquiv cellDerivedEquiv_natural from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables
open private localizedAcyclicIsZero from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactGenerators
open private representable_kProjective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective

section Categorical

variable {C E : Type*} [Category* C] [Category* E] [Preadditive C] [Preadditive E]

private theorem compact_of_iso {P R : C} (e : P ≅ R) (hP : IsCompact.{j} P) :
    IsCompact.{j} R := by
  intro I Y c hc
  exact ⟨coproductHomMap_injective _ hc, coproductHomMap_surjective_of_iso c e (hP c hc).2⟩

private theorem compact_left_adjoint {F : C ⥤ E} {G : E ⥤ C} (adj : F ⊣ G)
    [F.Additive] [G.IsEquivalence] {P : C} (hP : IsCompact.{j} P) :
    IsCompact.{j} (F.obj P) := by
  classical
  intro I Y c hc
  let d : Cofan (fun i => G.obj (Y i)) := Cofan.mk (G.obj c.pt) (fun i => G.map (c.inj i))
  have hc' : IsColimit (Cofan.mk c.pt c.inj) :=
    hc.ofIsoColimit (Cofan.ext (Iso.refl _) (by simp))
  have hd : IsColimit d := isColimitCofanMkObjOfIsColimit G Y c.inj hc'
  refine ⟨coproductHomMap_injective _ hc, ?_⟩
  let A := DirectSum.map (fun i => (adj.homAddEquiv P (Y i)).symm.toAddMonoidHom)
  have square : (coproductHomMap (F.obj P) c).comp A =
      (adj.homAddEquiv P c.pt).symm.toAddMonoidHom.comp (coproductHomMap P d) := by
    apply DirectSum.addHom_ext
    intro i f
    change coproductHomMap (F.obj P) c (A (DirectSum.of _ i f)) =
      (adj.homEquiv P c.pt).symm (coproductHomMap P d (DirectSum.of _ i f))
    rw [show A (DirectSum.of _ i f) =
      DirectSum.of (fun i => F.obj P ⟶ Y i) i ((adj.homEquiv P (Y i)).symm f) from
      DirectSum.map_of _ _ _, coproductHomMap_of, coproductHomMap_of]
    exact (adj.homEquiv_naturality_right_symm f (c.inj i)).symm
  intro g
  obtain ⟨f, hf⟩ := (hP d hd).2 (adj.homEquiv P c.pt g)
  refine ⟨A f, ?_⟩
  change ((coproductHomMap (F.obj P) c).comp A) f = g
  rw [square]
  change (adj.homEquiv P c.pt).symm (coproductHomMap P d f) = g
  rw [hf, Equiv.symm_apply_apply]

omit [Preadditive C] in
private theorem hom_subsingleton_of_iso_source {X X' Y : C} (e : X ≅ X')
    (h : Subsingleton (X ⟶ Y)) : Subsingleton (X' ⟶ Y) :=
  ⟨fun f g => (cancel_epi e.hom).mp (h.elim (e.hom ≫ f) (e.hom ≫ g))⟩

end Categorical

section NativeRepresentables

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w,w} k}
variable (h : HomotopyCategoryLaws A)

set_option hygiene false in
local notation "D" => RightDGModule.D A h
set_option hygiene false in
local notation "Q₀" => RightDGModule.Q A h
local instance : (Q₀).EssSurj := Localization.essSurj (Q₀) (RightDGModule.quasiIsomorphisms A)

variable [S : Preadditive D] (hadd : LocalizationMapAdditive h S)

include hadd

private theorem nativeRepresentableCompact (a : A.Obj) :
    IsCompact.{max v w} ((Q₀).obj (Yoneda.representable (A := A) a)) := by
  intro I Y c hc
  let M (i : I) := (Q₀).objPreimage (Y i)
  let b := DG.IndexedSums.nativeSum M
  obtain ⟨hd⟩ := RightDGModule.nativeExistingDerivedCoproduct.{u,v,w,max v w} h b
  let d := DerivedCoproducts.derivedCofan h b
  let e := (RightDGModule.toHomotopyCategory A ⋙ Q₀).mapIso
    (shiftZeroIso (Yoneda.representable (A := A) a))
  refine ⟨coproductHomMap_injective _ hc, coproductHomMap_surjective_of_iso c e ?_⟩
  exact coproductHomMap_surjective_of_cover _ hc (d := d) hd id
    (fun i => (Q₀).objObjPreimageIso (Y i)) (fun i _ => ⟨i, rfl⟩)
    (realizedSum_surjective (S := S) h hadd a b)

private theorem nativeCellsDetectZero (Y : D)
    (hY : ∀ (a : A.Obj) (n : ℤ),
      Subsingleton ((Q₀).obj (SemiFree.cell (A := A) a n) ⟶ Y)) : IsZero Y := by
  let M := (Q₀).objPreimage Y
  let e := (Q₀).objObjPreimageIso Y
  have hM : Module.acyclic M := by
    intro a n
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    apply ModuleCat.isZero_iff_subsingleton.mpr
    have hs : Subsingleton ((Q₀).obj (SemiFree.cell (A := A) a n) ⟶ (Q₀).obj M) :=
      ⟨fun f g => (cancel_mono e.hom).mp ((hY a n).elim (f ≫ e.hom) (g ≫ e.hom))⟩
    exact (cellDerivedEquiv (S := S) a n M h hadd).toEquiv.subsingleton_congr.mp hs
  have hz := localizedAcyclicIsZero.{u,v,w} (S := S) h hadd M hM
  change IsZero ((Q₀).obj M) at hz
  exact hz.of_iso e.symm

private theorem quasiIso_of_localizedIso {M N : RightDGModuleModel A} (f : M ⟶ N)
    (hf : IsIso ((Q₀).map (homotopyClass f))) : Module.quasiIsomorphism f := by
  intro a
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  let eM := cellDerivedEquiv (S := S) a n M h hadd
  let eN := cellDerivedEquiv (S := S) a n N h hadd
  let g := (Q₀).map (homotopyClass f)
  letI : IsIso g := hf
  let ePost : ((Q₀).obj (SemiFree.cell (A := A) a n) ⟶ (Q₀).obj M) ≃
      ((Q₀).obj (SemiFree.cell (A := A) a n) ⟶ (Q₀).obj N) :=
    { toFun := fun f => f ≫ g
      invFun := fun f => f ≫ inv g
      left_inv := fun f => by simp
      right_inv := fun f => by simp }
  let e := (eM.toEquiv.symm.trans ePost).trans eN.toEquiv
  have he (x : (M.complex a).homology n) : e x = homologyMap (f.app a) n x := by
    change eN (eM.symm x ≫ (Q₀).map (homotopyClass f)) = _
    rw [cellDerivedEquiv_natural (S := S) a n M h hadd f (eM.symm x)]
    rw [show cellDerivedEquiv (S := S) a n M h hadd (eM.symm x) = x from eM.apply_symm_apply x]
  have hEq : (fun x => homologyMap (f.app a) n x) = e := funext fun x => (he x).symm
  change Function.Bijective (fun x => homologyMap (f.app a) n x)
  rw [hEq]
  exact e.bijective

end NativeRepresentables

section RepresentableUnit

variable {k : Type u} [CommRing k]
variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {T : BalancedTensor.bimodule A B} (model : SignedModels.{u,v,w,z} T)

open KProjective (isKProjective)
open Yoneda (representable)

set_option hygiene false in
local notation "F₀" => ordinaryTensor.{u,v,w,z} model.tensor
set_option hygiene false in
local notation "G₀" => ordinaryHom.{u,v,w,z} model.hom

private theorem strictRepresentableUnit (b : A.Obj)
    (e : (F₀).obj (representable (A := A) b) ≅ T.obj b)
    (he : ∀ (c : B.Obj) (a : A.Obj) (i j n : ℤ) (h : i+j=n)
        (f : (A.hom a b).X i) (x : ((T.obj a).complex c).X j),
        (e.hom.app c).f n
          (model.tensor.degree (representable b) c n (tmul T (representable b) c a i j n h f x)) =
          left T c i j n h f x)
    (a : A.Obj) :
    ((model.adjunction.homEquiv (representable b) (T.obj b)) e.hom).app a ≫
        (model.hom.objectwise (T.obj b) a).inv = toComplexHom (T.map a b) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply RightDGModule.GradedHom.ext
  intro c j n h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hm := model.laws.apply_tmul (representable b) (T.obj b) 0
    (HomComplex.ofStrict e.hom) a c i j n i n (by omega) (add_zero i) (by omega) f x
  rw [← model.laws.homEquiv] at hm
  exact hm.trans (he c a i j n (by omega) f x)

variable (hA : HomotopyCategoryLaws A) (hB : HomotopyCategoryLaws B)
variable (d : DerivedAdjunctionData.{u,v,w,z} model.tensor model.hom hA hB)

set_option backward.isDefEq.respectTransparency false in
/-- Compare the two transposes on a projective representative using the
resolution augmentation and the natural square of the descended Hom. -/
private theorem derivedHomEquiv_onProjective (hr : DerivedAdjunctionData.Realizes.{u,v,w,z} d model.adjunction)
    (hc : DerivedAdjunctionData.ComputesRepresentatives.{u,v,w,z} d)
    (P : RightDGModuleModel A) (hP : isKProjective P) (N : RightDGModuleModel B)
    (f : (F₀).obj P ⟶ N) :
    letI := Derived.homotopyCategory A hA
    letI := Derived.homotopyCategory B hB
    letI := derivedCategoryInstance A hA
    letI := derivedCategoryInstance B hB
    let QA : HomComplex.homotopyCategory A ⥤ Derived.derivedCategory A hA := Derived.quotient A hA
    let QB : HomComplex.homotopyCategory B ⥤ Derived.derivedCategory B hB := Derived.quotient B hB
    d.adjunction.homEquiv (QA.obj P) (QB.obj N)
      ((d.onProjective P hP).hom ≫ QB.map (homotopyClass f)) ≫ (d.onInput N).hom =
      QA.map (homotopyClass (model.adjunction.homEquiv P N f)) := by
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  let QA : HomComplex.homotopyCategory A ⥤ Derived.derivedCategory A hA := Derived.quotient A hA
  let QB : HomComplex.homotopyCategory B ⥤ Derived.derivedCategory B hB := Derived.quotient B hB
  change (d.adjunction.homEquiv (QA.obj P) (QB.obj N))
    ((d.onProjective P hP).hom ≫ QB.map (homotopyClass f)) ≫ (d.onInput N).hom =
    QA.map (homotopyClass (model.adjunction.homEquiv P N f))
  let r := (DerivedAdjunctionData.resolutionAdjunction.{u,v,w,z} d)
  let H := (DerivedAdjunctionData.hom.{u,v,w,z} d).homotopy
  let F := (DerivedAdjunctionData.tensorH.{u,v,w,z} d)
  let G := (DerivedAdjunctionData.hom.{u,v,w,z} d).derived
  let adj := (DerivedAdjunctionData.homotopyAdjunction.{u,v,w,z} d)
  let σ := (DerivedAdjunctionData.hom.{u,v,w,z} d).square
  let p := r.counit.app P
  let β := eqToHom ((DerivedAdjunctionData.tensorObj.{u,v,w,z} d) P) ≫ homotopyClass f
  have hPcompare : ((DerivedAdjunctionData.onProjective.{u,v,w,z} d) P hP).hom ≫ (QB).map (homotopyClass f) =
      (QB).map (F.map p ≫ β) := by
    simp only [DerivedAdjunctionData.onProjective, Iso.trans_hom, eqToIso.hom,
      β, p, F, r, Functor.map_comp, eqToHom_map, Category.assoc]
    have hs := hc.1 P hP
    change (d.tensorSquare.app ⟨P, hP⟩).hom = QB.map (F.map p) at hs
    rw [hs]
  have hσ : σ.inv.app (F.obj ((DerivedAdjunctionData.resolution.{u,v,w,z} d).obj ((QA).obj P))) ≫
        G.map ((QB).map (F.map p ≫ β)) ≫ σ.hom.app N =
      (QA).map (H.map (F.map p ≫ β)) := by
    have hn := σ.inv.naturality (F.map p ≫ β)
    change (QA).map (H.map (F.map p ≫ β)) ≫ σ.inv.app N =
      σ.inv.app (F.obj ((DerivedAdjunctionData.resolution.{u,v,w,z} d).obj ((QA).obj P))) ≫
        G.map ((QB).map (F.map p ≫ β)) at hn
    rw [← Category.assoc, ← hn, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hunit : adj.unit.app P ≫ H.map (eqToHom ((DerivedAdjunctionData.tensorObj.{u,v,w,z} d) P)) ≫
      eqToHom ((DerivedAdjunctionData.hom.{u,v,w,z} d).obj ((F₀).obj P)) =
      homotopyClass (model.adjunction.unit.app P) := by
    rw [eqToHom_map, eqToHom_trans]
    exact eq_of_heq ((comp_eqToHom_heq _ _).trans (hr.2.2.1 P))
  have hmap : H.map (homotopyClass f) ≫ eqToHom ((DerivedAdjunctionData.hom.{u,v,w,z} d).obj N) =
      eqToHom ((DerivedAdjunctionData.hom.{u,v,w,z} d).obj ((F₀).obj P)) ≫ homotopyClass ((G₀).map f) := by
    apply eq_of_heq
    let g : (show HomComplex.homotopyCategory A from (G₀).obj ((F₀).obj P)) ⟶
        (show HomComplex.homotopyCategory A from (G₀).obj N) := homotopyClass ((G₀).map f)
    let e := (DerivedAdjunctionData.hom.{u,v,w,z} d).obj ((F₀).obj P)
    exact (comp_eqToHom_heq _ _).trans
      (((DerivedAdjunctionData.hom.{u,v,w,z} d).map f).trans (eqToHom_comp_heq g e).symm)
  have hβ : adj.unit.app P ≫ H.map β ≫ eqToHom ((DerivedAdjunctionData.hom.{u,v,w,z} d).obj N) =
      homotopyClass ((model.adjunction.homEquiv P N) f) := by
    rw [Adjunction.homEquiv_unit]
    change _ = (RightDGModule.toHomotopyCategory A).map
      (model.adjunction.unit.app P ≫ (G₀).map f)
    rw [Functor.map_comp]
    simp only [Functor.map_comp, Category.assoc]
    rw [hmap]
    rw [← Category.assoc (H.map (eqToHom ((DerivedAdjunctionData.tensorObj.{u,v,w,z} d) P))),
      ← Category.assoc, hunit]
    rfl
  have hstep : adj.unit.app ((DerivedAdjunctionData.resolution.{u,v,w,z} d).obj ((QA).obj P)) ≫ H.map (F.map p ≫ β) =
      p ≫ adj.unit.app P ≫ H.map β := by
    simp only [Functor.map_comp, ← Category.assoc]
    exact congrArg (fun g => g ≫ H.map β) (adj.unit.naturality p).symm
  rw [Adjunction.homEquiv_unit, hPcompare, hr.2.2.2.2.1]
  let θ : H.obj N ⟶ (show HomComplex.homotopyCategory A from (G₀).obj N) :=
    eqToHom (d.hom.obj N)
  have hθ : (d.onInput N).hom = σ.hom.app N ≫ QA.map θ := by
    simp only [DerivedAdjunctionData.onInput, Iso.trans_hom, eqToIso.hom, θ, eqToHom_map]
    rfl
  rw [hθ]
  change ((r.unit.app (QA.obj P) ≫ QA.map
    (adj.unit.app (d.resolution.obj (QA.obj P))) ≫
    σ.inv.app (F.obj (d.resolution.obj (QA.obj P)))) ≫
    G.map (QB.map (F.map p ≫ β))) ≫
      (σ.hom.app N ≫ QA.map θ) = _
  have hσ' := congrArg (fun g => g ≫ QA.map θ) hσ
  simp only [Category.assoc] at hσ' ⊢
  rw [hσ', ← QA.map_comp_assoc, hstep, QA.map_comp_assoc]
  have htriangle : r.unit.app (QA.obj P) ≫ QA.map p = 𝟙 (QA.obj P) :=
    r.right_triangle_components P
  rw [reassoc_of% htriangle]
  refine (QA.map_comp (adj.unit.app P ≫ H.map β) θ).symm.trans ?_
  exact congrArg (fun g => QA.map g) ((Category.assoc (adj.unit.app P) (H.map β) θ).trans hβ)

end RepresentableUnit

set_option backward.isDefEq.respectTransparency false in
private theorem criterion (unitAt : MoritaUnitAt.{u,v,w,z,j}) :
    MoritaCriterionAt.{u,v,w,z} := by
  intro k _ A B T model hA hB
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  intro S d hadd hr hc hex hproj
  let DA := Derived.derivedCategory A hA
  let DB := Derived.derivedCategory B hB
  letI : Category DA := derivedCategoryInstance A hA
  letI : Category DB := derivedCategoryInstance B hB
  let F : DA ⥤ DB := d.tensor
  let G : DB ⥤ DA := d.hom.derived
  let adj : F ⊣ G := d.adjunction
  let QA : HomComplex.homotopyCategory A ⥤ DA := Derived.quotient A hA
  let QB : HomComplex.homotopyCategory B ⥤ DB := Derived.quotient B hB
  rcases hex with ⟨cA, cB, ts, gs, hts, hgs, fs, gs', hF, hG, hAdj, hgs', hfs'⟩
  letI : HasShift DA ℤ := cA.shiftD
  letI : HasShift DB ℤ := cB.shiftD
  letI : Preadditive DA := cA.addD
  letI : Preadditive DB := cB.addD
  letI : HasZeroObject DA := cA.zeroD
  letI : HasZeroObject DB := cB.zeroD
  letI : ∀ n : ℤ, (shiftFunctor DA n).Additive := cA.addShiftD
  letI : ∀ n : ℤ, (shiftFunctor DB n).Additive := cB.addShiftD
  letI : Pretriangulated DA := cA.trianglesD
  letI : Pretriangulated DB := cB.trianglesD
  letI : F.CommShift ℤ := fs
  letI : G.CommShift ℤ := gs'
  letI : F.IsTriangulated := hF
  letI : G.IsTriangulated := hG
  have hS : S = cB.addD := Subsingleton.elim _ _
  subst S
  have hex : d.IsExact := ⟨cA, cB, ts, gs, hts, hgs, fs, gs', hF, hG, hAdj, hgs', hfs'⟩
  have haddA : LocalizationMapAdditive hA cA.addD := by
    let SA : Preadditive DA := RightDGModule.derivedPreadditive.{u,max v z,w} A hA
    letI : Preadditive DA := cA.addD
    letI : HasBinaryBiproducts DA :=
      @Pretriangulated.instHasBinaryBiproducts DA _ cA.zeroD cA.shiftD cA.addD
        cA.addShiftD cA.trianglesD
    have hS : SA = cA.addD :=
      @Subsingleton.elim _ (@subsingleton_preadditive_of_hasBinaryBiproducts DA _ _ _) _ _
    rw [← hS]
    intro M N f g
    exact (RightDGModule.derivedLocalization_additive.{u,max v z,w} A hA).map_add (f := f) (g := g)
  let R (a : A.Obj) := Yoneda.representable (A := A) a
  have hre (a : A.Obj) := hr.2.2.2.2.2.2 a
  let repIso (a : A.Obj) : F.obj (QA.obj (R a)) ≅ QB.obj (T.obj a) :=
    Classical.choice (hre a)
  let shiftIso (a : A.Obj) (n : ℤ) :
      F.obj (QA.obj (ShiftCone.shift (R a) n)) ≅ QB.obj (ShiftCone.shift (T.obj a) n) :=
    F.mapIso (cA.onShift (R a) n) ≪≫
    (F.commShiftIso n).app (QA.obj (R a)) ≪≫
    (shiftFunctor _ n).mapIso (repIso a) ≪≫ (cB.onShift (T.obj a) n).symm
  constructor
  · intro hEquiv
    letI : F.IsEquivalence := hEquiv
    letI : G.IsEquivalence := Adjunction.isEquivalence_right_of_isEquivalence_left (L := F) (R := G) adj
    letI : IsIso adj.unit := Adjunction.instIsIsoFunctorUnitOfIsEquivalence_1 adj
    refine ⟨?_, ?_, ?_⟩
    · intro a
      have hR : IsCompact.{max v w z} (QA.obj (R a)) :=
        nativeRepresentableCompact.{u,max v z,w} hA (S := cA.addD) haddA a
      change IsCompact.{max v w z} (QB.obj (T.obj a))
      exact compact_of_iso (C := DB) (repIso a) (compact_left_adjoint (F := F) (G := G) adj hR)
    · intro a b
      obtain ⟨e, he, _⟩ := hc.2 b
      have hP : KProjective.isKProjective (R b) := representable_kProjective b
      let η := (model.adjunction.homEquiv (R b) (T.obj b)) e.hom
      have hη : IsIso (QA.map (homotopyClass η)) := by
        rw [← derivedHomEquiv_onProjective.{u,v,w,z} model hA hB d hr hc (R b) hP (T.obj b) e.hom]
        rw [Adjunction.homEquiv_unit]
        let eF := (d.onProjective (R b) hP) ≪≫
          QB.mapIso ((RightDGModule.toHomotopyCategory B).mapIso e)
        let eUnit := asIso (adj.unit.app (QA.obj (R b)))
        exact ((eUnit ≪≫ G.mapIso eF) ≪≫ d.onInput (T.obj b)).isIso_hom
      have hq := quasiIso_of_localizedIso.{u,max v z,w} hA (S := cA.addD) haddA η hη a
      rw [← strictRepresentableUnit.{u,v,w,z} model b e he a]
      letI : QuasiIso (η.app a) := hq
      infer_instance
    · intro Y hy
      apply IsZero.of_full_of_faithful_of_isZero G
      apply nativeCellsDetectZero.{u,max v z,w} hA (S := cA.addD) haddA
      intro a n
      apply (adj.homEquiv _ _).subsingleton_congr.mp
      exact hom_subsingleton_of_iso_source (shiftIso a (-n)).symm (hy a (-n))
  · rintro ⟨hcompact, hq, hdetect⟩
    have hunit := (unitAt model hA hB cB.addD d hadd hr hc hex hproj hcompact hq).2.2
    have hzero (Y : Derived.derivedCategory B hB) (hy : IsZero (G.obj Y)) : IsZero Y := by
      apply hdetect Y
      intro a n
      apply hom_subsingleton_of_iso_source (shiftIso a n)
      apply (adj.homEquiv _ _).subsingleton_congr.mpr
      exact ⟨fun f g => hy.eq_of_tgt f g⟩
    have hreflect {X Y : Derived.derivedCategory B hB} (f : X ⟶ Y)
        (hf : IsIso (G.map f)) : IsIso f := by
      obtain ⟨Z, g, h, ht⟩ := distinguished_cocone_triangle f
      have hZ : IsZero (G.obj Z) :=
        Triangle.isZero₃_of_isIso₁ _ (G.map_distinguished _ ht) hf
      exact (Triangle.isZero₃_iff_isIso₁ _ ht).1 (hzero Z hZ)
    letI : ∀ X, IsIso (adj.unit.app X) := hunit
    letI : ∀ Y, IsIso (adj.counit.app Y) := fun Y => by
      apply hreflect
      have h := adj.right_triangle_components Y
      haveI : IsIso (adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y)) :=
        h ▸ inferInstanceAs (IsIso (𝟙 (G.obj Y)))
      exact IsIso.of_isIso_comp_left (adj.unit.app (G.obj Y)) _
    exact adj.toEquivalence.isEquivalence_functor

/-- Conditional proof with the ordered upstream premises. -/
theorem moritaCriterionAt_conditional.{base,coeff,leftObj,rightObj,leftCoeff,bound,larger,idx}
    (_adequateNativeProjectivityTransition : AdequateNativeProjectivityTransition.{base,coeff,leftObj,leftCoeff,rightObj,bound})
    (_ambientDerivedAdjunction : AmbientDerivedAdjunction.{base,coeff,leftObj,leftCoeff,rightObj,bound})
    (_ambientDerivedAdjunctionComparison : AmbientDerivedAdjunctionComparison.{base,coeff,leftObj,leftCoeff,rightObj,bound,larger})
    (_ambientExactDerivedAdjunction : AmbientExactDerivedAdjunction.{base,coeff,leftObj,leftCoeff,rightObj,bound})
    (_ambientProjectivityTransition : AmbientProjectivityTransition.{base,coeff,leftObj,leftCoeff,rightObj,bound,larger})
    (_derivedAdjunctionAt : DerivedAdjunctionAt.{base,coeff,leftObj,rightObj})
    (_exactDerivedAdjunctionAt : ExactDerivedAdjunctionAt.{base,coeff,leftObj,rightObj})
    (_homShiftConeComparison : HomShiftConeComparison.{base,coeff,leftObj,rightObj})
    (_nativeDerivedAdjunctionCompatibility : NativeDerivedAdjunctionCompatibility.{base,coeff,leftObj,rightObj})
    (_nativeHomDescent : NativeHomDescent.{base,coeff,leftObj,leftCoeff,rightObj})
    (_nativeHomPreservesQuasiIsomorphisms : NativeHomPreservesQuasiIsomorphisms.{base,coeff,leftObj,leftCoeff,rightObj})
    (_tensorPreservesKProjectives : TensorPreservesKProjectives.{base,coeff,leftObj,rightObj})
    (unitAt : MoritaUnitAt.{base,coeff,leftObj,rightObj,idx})
    (_moritaUnitTransition : MoritaUnitTransition.{base,coeff,leftObj,leftCoeff,rightObj,bound,larger}) :
    MoritaCriterionAt.{base,coeff,leftObj,rightObj} :=
  criterion.{base,coeff,leftObj,rightObj,idx} unitAt

/-- Conditional proof with the ordered upstream premises. -/
theorem ambientMorphismQuasiIsomorphisms_conditional.{base,coeff,leftObj,rightObj,leftCoeff,bound,larger,idx}
    (_adequateNativeProjectivityTransition : AdequateNativeProjectivityTransition.{base,coeff,leftObj,leftCoeff,rightObj,bound})
    (_ambientDerivedAdjunction : AmbientDerivedAdjunction.{base,coeff,leftObj,leftCoeff,rightObj,bound})
    (_ambientDerivedAdjunctionComparison : AmbientDerivedAdjunctionComparison.{base,coeff,leftObj,leftCoeff,rightObj,bound,larger})
    (_ambientExactDerivedAdjunction : AmbientExactDerivedAdjunction.{base,coeff,leftObj,leftCoeff,rightObj,bound})
    (_ambientProjectivityTransition : AmbientProjectivityTransition.{base,coeff,leftObj,leftCoeff,rightObj,bound,larger})
    (_derivedAdjunctionAt : DerivedAdjunctionAt.{base,coeff,leftObj,rightObj})
    (_exactDerivedAdjunctionAt : ExactDerivedAdjunctionAt.{base,coeff,leftObj,rightObj})
    (_homShiftConeComparison : HomShiftConeComparison.{base,coeff,leftObj,rightObj})
    (_nativeDerivedAdjunctionCompatibility : NativeDerivedAdjunctionCompatibility.{base,coeff,leftObj,rightObj})
    (_nativeHomDescent : NativeHomDescent.{base,coeff,leftObj,leftCoeff,rightObj})
    (_nativeHomPreservesQuasiIsomorphisms : NativeHomPreservesQuasiIsomorphisms.{base,coeff,leftObj,leftCoeff,rightObj})
    (_tensorPreservesKProjectives : TensorPreservesKProjectives.{base,coeff,leftObj,rightObj})
    (_moritaUnitAt : MoritaUnitAt.{base,coeff,leftObj,rightObj,idx})
    (_moritaUnitTransition : MoritaUnitTransition.{base,coeff,leftObj,leftCoeff,rightObj,bound,larger}) :
    AmbientMorphismQuasiIsomorphisms.{base,coeff,leftObj,rightObj,leftCoeff,bound} :=
  ambientMorphismComparison.{base,coeff,leftObj,rightObj,leftCoeff,bound}

end

end DerivedFormalization.DGBimodule

universe v8_closure_b9fea9267599ab0b_u0 v8_closure_b9fea9267599ab0b_u1 v8_closure_b9fea9267599ab0b_u2 v8_closure_b9fea9267599ab0b_u3 v8_closure_b9fea9267599ab0b_u4 v8_closure_b9fea9267599ab0b_u5
theorem _root_.«DerivedFormalization».«DGBimodule».«ambientMorphismQuasiIsomorphisms» : _root_.«Specs».«DerivedFormalization».«DG».«MoritaCriterion».«AmbientMorphismQuasiIsomorphisms».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3, v8_closure_b9fea9267599ab0b_u4, v8_closure_b9fea9267599ab0b_u5} :=
  @_root_.«DerivedFormalization».«DGBimodule».«ambientMorphismQuasiIsomorphisms_conditional».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3, v8_closure_b9fea9267599ab0b_u4, v8_closure_b9fea9267599ab0b_u5, 0, 0} (@_root_.«DerivedFormalization».«DGBimodule».«adequateNativeProjectivityTransition».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u4, v8_closure_b9fea9267599ab0b_u3, v8_closure_b9fea9267599ab0b_u5}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientDerivedAdjunction».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u4, v8_closure_b9fea9267599ab0b_u3, v8_closure_b9fea9267599ab0b_u5}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientDerivedAdjunctionComparison».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u4, v8_closure_b9fea9267599ab0b_u3, v8_closure_b9fea9267599ab0b_u5, 0}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientExactDerivedAdjunction».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u4, v8_closure_b9fea9267599ab0b_u3, v8_closure_b9fea9267599ab0b_u5}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientProjectivityTransition».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u4, v8_closure_b9fea9267599ab0b_u3, v8_closure_b9fea9267599ab0b_u5, 0}) (@_root_.«DerivedFormalization».«DGBimodule».«derivedAdjunctionAt».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«exactDerivedAdjunctionAt».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«homShiftConeComparison».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeDerivedAdjunctionCompatibility».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeHomDescent».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u4, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeHomPreservesQuasiIsomorphisms».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u4, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«tensorPreservesKProjectives».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«moritaUnitAt».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3, 0}) (@_root_.«DerivedFormalization».«DGBimodule».«moritaUnitTransition».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u4, v8_closure_b9fea9267599ab0b_u3, v8_closure_b9fea9267599ab0b_u5, 0})
theorem _root_.«DerivedFormalization».«DGBimodule».«moritaCriterionAt» : _root_.«Specs».«DerivedFormalization».«DG».«MoritaCriterion».«MoritaCriterionAt».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3} :=
  @_root_.«DerivedFormalization».«DGBimodule».«moritaCriterionAt_conditional».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3, 0, 0, 0, 0} (@_root_.«DerivedFormalization».«DGBimodule».«adequateNativeProjectivityTransition».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, 0, v8_closure_b9fea9267599ab0b_u3, 0}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientDerivedAdjunction».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, 0, v8_closure_b9fea9267599ab0b_u3, 0}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientDerivedAdjunctionComparison».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, 0, v8_closure_b9fea9267599ab0b_u3, 0, 0}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientExactDerivedAdjunction».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, 0, v8_closure_b9fea9267599ab0b_u3, 0}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientProjectivityTransition».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, 0, v8_closure_b9fea9267599ab0b_u3, 0, 0}) (@_root_.«DerivedFormalization».«DGBimodule».«derivedAdjunctionAt».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«exactDerivedAdjunctionAt».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«homShiftConeComparison».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeDerivedAdjunctionCompatibility».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeHomDescent».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, 0, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeHomPreservesQuasiIsomorphisms».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, 0, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«tensorPreservesKProjectives».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«moritaUnitAt».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, v8_closure_b9fea9267599ab0b_u3, 0}) (@_root_.«DerivedFormalization».«DGBimodule».«moritaUnitTransition».{v8_closure_b9fea9267599ab0b_u0, v8_closure_b9fea9267599ab0b_u1, v8_closure_b9fea9267599ab0b_u2, 0, v8_closure_b9fea9267599ab0b_u3, 0, 0})
