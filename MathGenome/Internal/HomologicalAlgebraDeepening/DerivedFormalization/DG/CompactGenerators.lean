import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CompactGenerators
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoproducts
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyShift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedCellAttachment
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeResolution
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Telescope
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.CompactGenerators
open Specs.DerivedFormalization.DG.CompactRepresentables
open Specs.DerivedFormalization.DG.DerivedTriangles
open Specs.DerivedFormalization.DG.DerivedKProjective
  (derivedCategoryInstance replacementIso)
open Specs.DerivedFormalization.DG.IndexedSemiFree (Presentation)
open private colimitInclusions_exhaustive zeroModule from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeResolution
open private isIso_of_degreewise_isIso from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Telescope

namespace DerivedFormalization.RightDGModule

noncomputable section

universe u v w t j

set_option linter.style.haveILetI false

section Filtration

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {M : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M)

/-- The inclusions into the filtered module form a cocone on the stage sequence. -/
private def filtrationCocone :
    Cocone (Functor.ofSequence fun l => (F.extension l).inclusion) where
  pt := M
  ι := NatTrans.ofSequence F.into fun l => by
    rw [Functor.ofSequence_map_homOfLE_succ]
    change (F.extension l).inclusion ≫ F.into (l + 1) = F.into l ≫ 𝟙 M
    exact (F.compatible l).trans (Category.comp_id _).symm

/-- Injectivity and exhaustiveness identify the filtered module with the strict
sequential colimit. Two representatives can be compared in their common stage. -/
private def filtrationIsColimit :
    IsColimit (filtrationCocone F) := by
  let X := Functor.ofSequence fun l => (F.extension l).inclusion
  let c := filtrationCocone F
  let b := colimitCocone X
  let m := (colimitCoconeIsColimit X).desc c
  have hm (l : ℕ) : b.ι.app l ≫ m = c.ι.app l :=
    (colimitCoconeIsColimit X).fac c l
  have hmEval (l : ℕ) (a : A.Obj) (n : ℤ) (x : ((F.stage l).complex a).X n) :
      (m.app a).f n (((b.ι.app l).app a).f n x) = ((F.into l).app a).f n x :=
    congrArg (fun f => (f.app a).f n x) (hm l)
  haveI hmIso : IsIso m := by
    apply isIso_of_degreewise_isIso
    intro a n
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro x y hxy
      obtain ⟨l, xl, rfl⟩ := colimitInclusions_exhaustive _ (colimitCoconeIsColimitDegree X a n) x
      obtain ⟨r, yr, rfl⟩ := colimitInclusions_exhaustive _ (colimitCoconeIsColimitDegree X a n) y
      change (m.app a).f n (((b.ι.app l).app a).f n xl) =
        (m.app a).f n (((b.ι.app r).app a).f n yr) at hxy
      let p : l ⟶ max l r := homOfLE (le_max_left _ _)
      let q : r ⟶ max l r := homOfLE (le_max_right _ _)
      have hl :
          ((b.ι.app (max l r)).app a).f n (((X.map p).app a).f n xl) =
            ((b.ι.app l).app a).f n xl :=
        congrArg (fun f => (f.app a).f n xl) (b.w p)
      have hr :
          ((b.ι.app (max l r)).app a).f n (((X.map q).app a).f n yr) =
            ((b.ι.app r).app a).f n yr :=
        congrArg (fun f => (f.app a).f n yr) (b.w q)
      have hx := congrArg ((m.app a).f n) hl
      have hy := congrArg ((m.app a).f n) hr
      have hs := hx.trans (hxy.trans hy.symm)
      have hsame := (hmEval (max l r) a n (((X.map p).app a).f n xl)).symm.trans
        (hs.trans (hmEval (max l r) a n (((X.map q).app a).f n yr)))
      exact hl.symm.trans
        ((congrArg (((b.ι.app (max l r)).app a).f n) (F.injective _ a n hsame)).trans hr)
    · intro x
      obtain ⟨l, y, hy⟩ := F.exhaustive a n x
      exact ⟨((b.ι.app l).app a).f n y, (hmEval l a n y).trans hy⟩
  exact (colimitCoconeIsColimit X).ofIsoColimit
    (Cocone.ext (asIso m) hm)

end Filtration

section Native

variable {k : Type u} [CommRing k] {B : DGCategoryModel.{u,max v w,w} k}
variable (h : Derived.HomotopyCategoryLaws B)

local instance : Category (HomComplex.homotopyCategory B) := instCategoryK B
local instance : Category (Derived.derivedCategory B h) := derivedCategoryInstance B h

local notation "K₀" => HomComplex.homotopyCategory B
local notation "D₀" => Derived.derivedCategory B h
private abbrev localizationFunctor : K₀ ⥤ D₀ := Derived.quotient B h

local notation "Q₀" => localizationFunctor h

private theorem zeroMapLocalization [S : Preadditive D₀] (hadd : LocalizationMapAdditive h S)
    (M N : RightDGModuleModel B) :
    (Q₀).map (HomComplex.homotopyClass (0 : M ⟶ N)) = 0 := by
  let q : Basic.h0Hom (HomComplex.homComplex M N) := 0
  let mapClass := fun (f : Basic.h0Hom (HomComplex.homComplex M N)) => (Q₀).map f
  have hz : mapClass (q + q) = mapClass q + mapClass q := hadd M N q q
  have hsum : mapClass (q + q) = mapClass q := congrArg mapClass (zero_add q)
  have hh : mapClass q = 0 := add_left_cancel (hz.symm.trans (hsum.trans (add_zero _).symm))
  have hclass : HomComplex.homotopyClass (0 : M ⟶ N) = q :=
    (toHomotopyCategory B).map_zero M N
  exact (congrArg mapClass hclass).trans hh

private theorem localizedAcyclicIsZero [S : Preadditive D₀]
    (hadd : LocalizationMapAdditive h S) (M : RightDGModuleModel B)
    (hM : Module.acyclic M) : IsZero ((Q₀).obj M) := by
  let Z : RightDGModuleModel B := zeroModule
  have hZ (a : B.Obj) (n : ℤ) : Subsingleton ((Z.complex a).X n) :=
    inferInstanceAs (Subsingleton PUnit)
  have hId : (𝟙 Z : Z ⟶ Z) = 0 := by
    apply RightDGModuleModel.hom_ext
    intro a
    apply HomologicalComplex.hom_ext
    intro n
    exact ModuleCat.hom_ext (LinearMap.ext fun x => (hZ a n).elim _ _)
  have hz : IsZero ((Q₀).obj Z) := by
    apply (IsZero.iff_id_eq_zero _).2
    rw [← (Q₀).map_id Z]
    change (Q₀).map (HomComplex.homotopyClass (𝟙 Z)) = 0
    rw [hId]
    exact zeroMapLocalization h hadd Z Z
  have hq : Module.quasiIsomorphism (0 : Z ⟶ M) := by
    intro a
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have hZa : (Z.complex a).ExactAt n := by
      apply HomologicalComplex.ExactAt.of_isZero
      exact ModuleCat.isZero_iff_subsingleton.mpr (hZ a n)
    exact hZa.isZero_homology.isIso ((hM a n).isZero_homology) _
  exact hz.of_iso (replacementIso h (0 : Z ⟶ M) hq).symm

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Apply the strict quotient triangle at each stage and the telescope triangle
to the entire presentation. -/
private theorem generationOfStrictTriangles
    [SK : HasShift K₀ ℤ] [HasShift D₀ ℤ] [Preadditive D₀] [HasZeroObject D₀]
    [∀ n : ℤ, (shiftFunctor D₀ n).Additive] [Pretriangulated D₀] [(Q₀).CommShift ℤ]
    (hS : ∀ (M : K₀) (n : ℤ), (shiftFunctor K₀ n).obj M = ShiftCone.shift M n)
    (hcone : ∀ {M N : RightDGModuleModel B} (f : M ⟶ N),
      (Q₀).mapTriangle.obj (DerivedTriangles.coneTriangle h SK (hS M 1) f) ∈ distTriang D₀)
    (hzero : ∀ M : RightDGModuleModel B, Module.acyclic M → IsZero ((Q₀).obj M))
    (P : ObjectProperty D₀) [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (hsum : CoproductClosed.{max v w,_,_} P)
    (hrep : ∀ a : B.Obj, P ((Q₀).obj (Yoneda.representable (A := B) a))) :
    ∀ X, P X := by
  classical
  have hcell (a : B.Obj) (n : ℤ) : P ((Q₀).obj (SemiFree.cell (A := B) a n)) := by
    let H := Yoneda.representable (A := B) a
    let e : (Q₀).obj (SemiFree.cell (A := B) a n) ≅ (shiftFunctor D₀ (-n)).obj ((Q₀).obj H) :=
      (Q₀).mapIso (eqToIso (hS H (-n)).symm) ≪≫ ((Q₀).commShiftIso (-n)).app H
    exact P.prop_of_iso e.symm (P.le_shift (-n) ((Q₀).obj H) (hrep a))
  intro X
  letI : (Q₀).EssSurj := inferInstanceAs ((Derived.quasiIsomorphisms B).Q.EssSurj)
  let M := (Q₀).objPreimage X
  obtain ⟨N, p, ⟨F⟩, _, hp⟩ := unboundedSemiFreeResolutionInUniverse k B M
  have hstage (l : ℕ) : P ((Q₀).obj (F.stage l)) := by
    induction l with
    | zero =>
      apply P.prop_of_isZero
      apply hzero
      intro a n
      apply HomologicalComplex.ExactAt.of_isZero
      exact ModuleCat.isZero_iff_subsingleton.mpr
        ⟨fun x y => (F.bottom a n x).trans (F.bottom a n y).symm⟩
    | succ l ih =>
      obtain ⟨S, b, q, hq, _, ⟨hc⟩, _, hexact⟩ :=
        DG.IndexedCellAttachment.quotient (F.extension l)
      obtain ⟨hd⟩ := nativeExistingDerivedCoproduct h b
      have hS' : P ((Q₀).obj S) :=
        hsum (DerivedCoproducts.derivedCofan h b) hd
          (fun i => hcell ((F.family l).object i) ((F.family l).degree i))
      let f := (F.extension l).inclusion
      have hcmp := (coneToCokernel f (fun a n => (hexact a n).1) q hq hc).2
      let T := (Q₀).mapTriangle.obj (DerivedTriangles.coneTriangle h SK (hS (F.stage l) 1) f)
      have hthird : P T.obj₃ :=
        P.prop_of_iso (replacementIso h (Telescope.coneComparison f q hq) hcmp).symm hS'
      exact P.ext_of_isTriangulatedClosed₂ T (hcone f) ih hthird
  let b := DG.IndexedSums.sumRealization F.stage (fun _ _ => inferInstance)
  let U := Cofan.mk _ b.inclusion
  let hu : IsColimit U := DG.IndexedSums.isColimit b
  let c := DerivedCoproducts.derivedCofan h b
  obtain ⟨hc⟩ := nativeExistingDerivedCoproduct h b
  let e : ULift.{max v w} ℕ ≃ ℕ := Equiv.ulift
  have hU : P ((Q₀).obj U.pt) :=
    hsum (Cofan.mk c.pt fun i : ULift.{max v w} ℕ => c.inj (e i))
      ((Cofan.isColimitEquivOfEquiv e c) hc) (fun i => hstage (e i))
  let step := fun l => (F.extension l).inclusion
  let f := Telescope.oneSubSuccessor step hu
  let T := (Q₀).mapTriangle.obj (DerivedTriangles.coneTriangle h SK (hS U.pt 1) f)
  have hthird : P T.obj₃ :=
    P.ext_of_isTriangulatedClosed₃ T (hcone f) hU hU
  let cmp := Telescope.telescopeComparison step hu (filtrationCocone F)
  have hcmp : Module.quasiIsomorphism cmp := telescope_quasiIso step hu (filtrationIsColimit F)
  exact P.prop_of_iso
    (replacementIso h cmp hcmp ≪≫ replacementIso h p hp ≪≫ (Q₀).objObjPreimageIso X) hthird

end Native

private theorem detectsZero (hHom : ShiftedRepresentableHom.{u,v,w,t}) :
    ShiftedRepresentablesDetectZero.{u,v,w,t} := by
  intro k _ A h
  classical
  let B := AmbientDerived.category.{u,v,w,t} A
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  let Q : HomComplex.homotopyCategory B ⥤ Derived.derivedCategory B h := Derived.quotient B h
  letI : Q.EssSurj := inferInstanceAs ((Derived.quasiIsomorphisms B).Q.EssSurj)
  obtain ⟨S, hadd, he⟩ := hHom A h
  letI := S
  change ∀ X : Derived.derivedCategory B h,
    IsZero X ↔ ∀ (a : A.Obj) (n : ℤ),
      Subsingleton (Q.obj (SemiFree.cell (A := B) a n) ⟶ X)
  intro X
  constructor
  · intro hX a n
    exact ⟨fun f g => hX.eq_of_tgt f g⟩
  · intro hx
    let M := Q.objPreimage X
    let e := Q.objObjPreimageIso X
    have hM : Module.acyclic M := by
      intro a n
      apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      apply ModuleCat.isZero_iff_subsingleton.mpr
      obtain ⟨_, _, cmp, _⟩ := he a n
      have hsub : Subsingleton (Q.obj (SemiFree.cell (A := B) a n) ⟶ Q.obj M) :=
        ⟨fun f g => (cancel_mono e.hom).mp ((hx a n).elim (f ≫ e.hom) (g ≫ e.hom))⟩
      exact (cmp M).toEquiv.subsingleton_congr.mp hsub
    exact (localizedAcyclicIsZero h hadd M hM).of_iso e.symm

set_option maxHeartbeats 500000 in
private theorem generates (hTri : AmbientTriangulation.{u,v,w,t})
    (hHom : ShiftedRepresentableHom.{u,v,w,t}) : RepresentablesGenerate.{u,v,w,t} := by
  intro k R A h
  let B := AmbientDerived.category.{u,v,w,t} A
  obtain ⟨SK, _AK, _ZK, _LK, hS, _TK, _, _, _, _HP, _, SD, AD, ZD, LD, qS, TD,
    trD, _, _, _, iffCone, hcone, _⟩ := hTri A h
  letI := SK
  letI := SD
  letI := AD
  letI := ZD
  letI := qS
  letI := LD
  letI := TD
  refine ⟨SK, SD, AD, ZD, hS, qS, LD, TD, trD, iffCone, hcone, ?_⟩
  obtain ⟨S, hadd, _⟩ := hHom A h
  intro P hIso hP hsum hrep X
  exact @generationOfStrictTriangles.{u,max v t,w} k R B h SK SD AD ZD LD TD qS hS hcone
    (@localizedAcyclicIsZero.{u,max v t,w} k R B h S hadd) P hIso hP hsum hrep X

set_option maxHeartbeats 800000 in
/-- The representables are compact, generate the derived category, and detect zero
through their shifts at every adequate coefficient bound. -/
theorem representableCompactGenerators :
    RepresentableCompactGenerators.{u,v,w,t,j} := by
  exact ⟨shiftedRepresentableHom.{u,v,w,t}, representableCompact.{u,v,w,t,j},
    generates.{u,v,w,t} ambientDerivedTriangulation shiftedRepresentableHom,
    detectsZero.{u,v,w,t} shiftedRepresentableHom⟩

end

end DerivedFormalization.RightDGModule
