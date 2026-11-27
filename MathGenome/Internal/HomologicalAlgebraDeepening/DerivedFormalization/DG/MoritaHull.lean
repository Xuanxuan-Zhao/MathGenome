import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.MoritaHull
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.PretriangulatedHull
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactGenerators
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedBimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.MoritaCriterion
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.BalancedTensor (bimodule CochainMap)
open Specs.DerivedFormalization.DG.BimoduleAdjunction (ordinaryHom)
open Specs.DerivedFormalization.DG.DerivedBimoduleAdjunction
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)
open Specs.DerivedFormalization.DG.FiniteCellConstructions
open Specs.DerivedFormalization.DG.MoritaCriterion
open Specs.DerivedFormalization.DG.MoritaHull (source target)
open Specs.DerivedFormalization.DG.MoritaUnit (MorphismQuasiIsomorphisms toComplexHom)
open Specs.DerivedFormalization.DG.Yoneda (representable)

namespace DerivedFormalization.DGBimodule

noncomputable section

set_option maxHeartbeats 1300000
set_option maxRecDepth 1800
set_option linter.style.haveILetI false
set_option autoImplicit false

universe u v w t p
variable {k : Type u} [CommRing k]

open RightDGModule (toHomotopyCategory yoneda yonedaIso yoneda_map_isIso)
open private writtenYoneda from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.FiniteCellConstructions
open private yonedaIso_laws from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Yoneda

private abbrev C (A : DGCategoryModel.{u,v,w} k) := source.{u,v,w,t} A
private abbrev B (A : DGCategoryModel.{u,v,w} k) := target.{u,v,w,t} A

private def cochainMapOfHom {X Y : ModuleCochain.{u,p} k} (f : X ⟶ Y) :
    CochainMap X Y where
  f n := (f.f n).hom
  comm n x := CategoryTheory.congr_fun (f.comm n (n+1)).symm x

private def writtenYonedaMap (A : DGCategoryModel.{u,v,w} k) (a b : A.Obj) :
    CochainMap (A.hom a b) ((pretr A).hom (pretrRepresentable A a) (pretrRepresentable A b)) where
  f n := (((writtenYoneda A).map a b).f n).hom.comp ULift.moduleEquiv.symm.toLinearMap
  comm n x := (cochainMapOfHom ((writtenYoneda A).map a b)).comm n (ULift.up x)

/-- Transport the written Yoneda functor to the common coefficient bound. -/
private def liftedWrittenYoneda (A : DGCategoryModel.{u,v,w} k) :
    DGFunctorModel (C.{u,v,w,t} A) (B.{u,v,w,t} A) where
  obj := pretrRepresentable A
  map a b := liftCochainMap.{u,v,max v w,max v w t} (writtenYonedaMap A a b)
  map_id a := congrArg ULift.up ((writtenYoneda A).map_id a)
  map_comp i j n h f g := congrArg ULift.up
    ((writtenYoneda A).map_comp i j n h (ULift.up f.down) (ULift.up g.down))

private def upToYoneda (A : DGCategoryModel.{u,v,w} k) (X Y : WrittenObject A) :
    (B.{u,v,w,t} A).hom X Y ⟶ (Yoneda.liftCategory (B.{u,v,w,t} A)).hom X Y :=
  toComplexHom { f := fun _ => ULift.moduleEquiv.symm.toLinearMap, comm := fun _ _ => rfl }

/-- The extension bimodule takes each original object to the representable of its
image, with the left action given by postcomposition. -/
private def hullBimodule (A : DGCategoryModel.{u,v,w} k) : bimodule (C.{u,v,w,t} A) (B.{u,v,w,t} A) :=
  ofDGFunctor {
    obj := fun a => representable (A := B.{u,v,w,t} A) (pretrRepresentable A a)
    map := fun a b => (liftedWrittenYoneda.{u,v,w,t} A).map a b ≫
      upToYoneda.{u,v,w,t} A (pretrRepresentable A a) (pretrRepresentable A b) ≫
      (yoneda (B.{u,v,w,t} A)).map (pretrRepresentable A a) (pretrRepresentable A b)
    map_id := fun a => by
      change ((yoneda (B.{u,v,w,t} A)).map _ _).f 0
        (ULift.up (((liftedWrittenYoneda.{u,v,w,t} A).map a a).f 0 ((C.{u,v,w,t} A).id a))) = _
      rw [(liftedWrittenYoneda.{u,v,w,t} A).map_id a]
      exact (yoneda (B.{u,v,w,t} A)).map_id _
    map_comp := fun {a b c} i j n h f g => by
      change ((yoneda (B.{u,v,w,t} A)).map _ _).f n
        (ULift.up (((liftedWrittenYoneda.{u,v,w,t} A).map a c).f n ((C.{u,v,w,t} A).comp i j n h f g))) = _
      rw [(liftedWrittenYoneda.{u,v,w,t} A).map_comp i j n h f g]
      exact (yoneda (B.{u,v,w,t} A)).map_comp i j n h _ _
  }

private theorem hullBimodule_apply (A : DGCategoryModel.{u,v,w} k)
    (a b : A.Obj) (r : ℤ) (f : (A.hom a b).X r) (X : WrittenObject A) (i j : ℤ)
    (h : i+r=j) (x : (((hullBimodule.{u,v,w,t} A).obj a).complex X).X i) :
    HomComplex.component (((hullBimodule.{u,v,w,t} A).map a b).f r (ULift.up f)) X i j h x =
      (B.{u,v,w,t} A).comp r i j (by omega)
        (ULift.up (((writtenYoneda A).map a b).f r (ULift.up f))) x :=
  (yonedaIso_laws (A := B.{u,v,w,t} A)).inverse _ _ r i j (by omega) _ X x

private theorem hullBimodule_quasiIso (A : DGCategoryModel.{u,v,w} k) :
    MorphismQuasiIsomorphisms.{u,max v w t,w,max v w} (hullBimodule.{u,v,w,t} A) := by
  intro a b
  let f := toComplexHom ((hullBimodule.{u,v,w,t} A).map a b)
  haveI (n : ℤ) : IsIso (f.f n) := by
    let Y := writtenYoneda A
    let YB := yoneda (B.{u,v,w,t} A)
    haveI : IsIso (Y.map a b) := yoneda_map_isIso (A := A) a b
    haveI : IsIso (YB.map (pretrRepresentable A a) (pretrRepresentable A b)) := yoneda_map_isIso (A := B.{u,v,w,t} A) _ _
    have hY := (ConcreteCategory.isIso_iff_bijective ((Y.map a b).f n)).mp inferInstance
    have hYB := (ConcreteCategory.isIso_iff_bijective
      ((YB.map (pretrRepresentable A a) (pretrRepresentable A b)).f n)).mp inferInstance
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      ((hYB.comp ULift.moduleEquiv.symm.bijective).comp
        (ULift.moduleEquiv.symm.bijective.comp
          (hY.comp (ULift.moduleEquiv.symm.bijective.comp ULift.moduleEquiv.bijective))))
  letI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact inferInstanceAs (QuasiIso f)

/-- Evaluate a written object as a right module over the lifted original category. -/
@[reducible] private def hullEvaluation {A : DGCategoryModel.{u,v,w} k}
    (E : LiftedHullComparison.{u,v,w,max v w t} A) : bimodule (B.{u,v,w,t} A) (C.{u,v,w,t} A) where
  obj X := liftedWrittenModule.{u,v,w,max v w t} A X
  map X Y := cochainMapOfHom (E.homIso X Y).hom
  map_id := E.identity
  map_comp := E.composition

open private isIso_of_degreewise_isIso from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Telescope

private def homAtWrittenIso {A : DGCategoryModel.{u,v,w} k}
    (E : LiftedHullComparison.{u,v,w,max v w t} A)
    (G : BimoduleAdjunction.InternalHomModel (hullEvaluation.{u,v,w,t} E)) (X : WrittenObject A) :
    representable (A := B.{u,v,w,t} A) X ≅
      (ordinaryHom.{u,max v w t,max v w,w} G).obj ((hullEvaluation.{u,v,w,t} E).obj X) := by
  let N := (hullEvaluation.{u,v,w,t} E).obj X
  let f : representable (A := B.{u,v,w,t} A) X ⟶ (ordinaryHom.{u,max v w t,max v w,w} G).obj N :=
    { app := fun a => (E.homIso a X).hom ≫ (G.objectwise N a).hom
      comm_act := by
        intro a b i j n h x g
        change (G.objectwise N a).hom.f n ((E.homIso a X).hom.f n ((B.{u,v,w,t} A).comp i j n h x g)) =
          (G.functor.obj N).act i j n h ((G.objectwise N b).hom.f i ((E.homIso b X).hom.f i x)) g
        exact (congrArg ((G.objectwise N a).hom.f n) ((hullEvaluation.{u,v,w,t} E).map_comp i j n h x g)).trans
          (G.action N i j n h ((E.homIso b X).hom.f i x) g).symm }
  letI : IsIso f := isIso_of_degreewise_isIso f (fun a n => by
    change IsIso (((E.homIso a X).hom ≫ (G.objectwise N a).hom).f n)
    change IsIso ((E.homIso a X).hom.f n ≫ (G.objectwise N a).hom.f n)
    let E₁ := (HomologicalComplex.eval (ModuleCat.{max v w t} k) (ComplexShape.up ℤ) n).mapIso
      (E.homIso a X)
    let E₂ := (HomologicalComplex.eval (ModuleCat.{max v w t} k) (ComplexShape.up ℤ) n).mapIso
      (G.objectwise N a)
    exact (E₁ ≪≫ E₂).isIso_hom)
  exact asIso f

open private strictToDerived writtenZero_isZero writtenShift_iso writtenCone_iso writtenSum_isColimit
  writtenKProjective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.PretriangulatedHull
open private representable_kProjective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective

/-- A triangulated subcategory containing the original representables contains
the localized images of all written objects. -/
private theorem writtenObjectsInTriangulatedSubcategory
    {A : DGCategoryModel.{u,v,w} k} {h : HomotopyCategoryLaws (C.{u,v,w,t} A)}
    (c : ConeLocalization (C.{u,v,w,t} A) h) :
    letI := Derived.homotopyCategory (C.{u,v,w,t} A) h
    letI := derivedCategoryInstance (C.{u,v,w,t} A) h
    letI := c.shiftD
    letI := c.addD
    letI := c.zeroD
    letI := c.addShiftD
    letI := c.trianglesD
    ∀ (P : ObjectProperty (Derived.derivedCategory (C.{u,v,w,t} A) h))
      [P.IsClosedUnderIsomorphisms] [P.IsTriangulated],
      (∀ (a : A.Obj), P ((strictToDerived.{u,v,w,max v t} h).obj (representable a))) →
      ∀ X : WrittenObject A, P ((strictToDerived.{u,v,w,max v t} h).obj (writtenModule A X)) := by
  letI := Derived.homotopyCategory (C.{u,v,w,t} A) h
  letI := derivedCategoryInstance (C.{u,v,w,t} A) h
  letI := c.shiftD
  letI := c.addD
  letI := c.zeroD
  letI := c.addShiftD
  letI := c.trianglesD
  intro P _ _ hrep
  letI : HasShift (HomComplex.homotopyCategory (C.{u,v,w,t} A)) ℤ := c.shiftK
  letI : HasShift (RightDGModule.K (C.{u,v,w,t} A)) ℤ := c.shiftK
  letI : HasShift (RightDGModule.D (C.{u,v,w,t} A) h) ℤ := c.shiftD
  letI : (RightDGModule.Q (C.{u,v,w,t} A) h).CommShift ℤ := c.quotientShift
  letI : Preadditive (RightDGModule.D (C.{u,v,w,t} A) h) := c.addD
  letI : HasZeroObject (RightDGModule.D (C.{u,v,w,t} A) h) := c.zeroD
  let QA : HomComplex.homotopyCategory (C.{u,v,w,t} A) ⥤
      Derived.derivedCategory (C.{u,v,w,t} A) h := Derived.quotient (C.{u,v,w,t} A) h
  letI : QA.CommShift ℤ := c.quotientShift
  let Q := strictToDerived.{u,v,w,max v t} h
  have hh (n : ℕ) : ∀ i : (writtenStage A n).1, P (Q.obj ((writtenStage A n).2 i)) := by
    induction n with
    | zero =>
      intro i
      change ULift.{v} A.Obj ⊕ Unit at i
      cases i with
      | inl a => exact hrep a.down
      | inr _ => exact P.prop_of_isZero (writtenZero_isZero.{u,v,w,max v t} h)
    | succ n ih =>
      intro i
      change WrittenStep A (writtenStage A n).2 at i
      cases i with
      | previous i => exact ih i
      | shift i s =>
        let M := (writtenStage A n).2 i
        exact P.prop_of_iso (writtenShift_iso.{u,v,w,max v t} h c.shiftObj M s).symm
          (P.le_shift s _ (ih i))
      | sum m f =>
        let X (i : Fin m) : WrittenObject A := Quotient.mk _ ⟨n, f i⟩
        obtain ⟨col⟩ := writtenSum_isColimit.{u,v,w,max v t} h X
        let lim := biconeIsBilimitOfColimitCoconeOfIsColimit col
        exact P.prop_of_isLimit_fan lim.isLimit (fun i => ih (f i.down))
      | cone i j f =>
        let T := QA.mapTriangle.obj
          (DerivedTriangles.coneTriangle h c.shiftK (c.shiftObj _ 1)
            ((AmbientDerived.strictInput.{u,v,w,max v t} A).map f))
        have hT : T ∈ distTriang _ := c.localizedConeTriangles.1 _
        exact P.prop_of_iso (writtenCone_iso.{u,v,w,max v t} h c.shiftObj f).symm
          (P.ext_of_isTriangulatedClosed₃ T hT (ih i) (ih j))
  intro X
  refine Quotient.inductionOn X ?_
  rintro ⟨n,i⟩
  exact hh n i

private theorem hullDetectsZero
    {A : DGCategoryModel.{u,v,w} k}
    (hA : HomotopyCategoryLaws (C.{u,v,w,t} A))
    (hB : HomotopyCategoryLaws (B.{u,v,w,t} A)) :
    ShiftedImagesDetectZero.{u,max v w t,w,max v w} (hullBimodule.{u,v,w,t} A) hB := by
  classical
  obtain ⟨E⟩ := (RightDGModule.liftedHull.{u,v,w,max v w t} A).comparison
  let J := hullEvaluation.{u,v,w,t} E
  obtain ⟨L,G,U,adj,hlaws⟩ := underivedAdjunction.{u,max v w t,max v w,w}
    (B.{u,v,w,t} A) (C.{u,v,w,t} A) J
  let m : SignedModels.{u,max v w t,max v w,w} J := ⟨L,G,U,adj,hlaws⟩
  have kprojective (X : (B.{u,v,w,t} A).Obj) : KProjective.isKProjective (J.obj X) :=
    writtenKProjective.{u,v,w,max v t} (RightDGModule.liftedHull.{u,v,w,max v w t} A) X
  obtain ⟨d, _, _, hexact⟩ := exactDerivedAdjunctionAt.{u,max v w t,max v w,w} m kprojective hB hA
  obtain ⟨cB, cA, _, _, _, _, _, gshift, _, htri, _, _⟩ := hexact
  letI := Derived.homotopyCategory (C.{u,v,w,t} A) hA
  letI := Derived.homotopyCategory (B.{u,v,w,t} A) hB
  letI := derivedCategoryInstance (C.{u,v,w,t} A) hA
  letI := derivedCategoryInstance (B.{u,v,w,t} A) hB
  letI := cA.shiftD
  letI := cA.addD
  letI := cA.zeroD
  letI := cA.addShiftD
  letI := cA.trianglesD
  letI := cB.shiftD
  letI := cB.addD
  letI := cB.zeroD
  letI := cB.addShiftD
  letI := cB.trianglesD
  letI := gshift
  letI := htri
  let F := d.hom.derived
  let QB : HomComplex.homotopyCategory (B.{u,v,w,t} A) ⥤
      Derived.derivedCategory (B.{u,v,w,t} A) hB := Derived.quotient (B.{u,v,w,t} A) hB
  let QA := strictToDerived.{u,v,w,max v t} hA
  have repIso (X : WrittenObject A) :
      F.obj (QA.obj (writtenModule A X)) ≅ QB.obj (representable X) :=
    d.onInput (J.obj X) ≪≫
      (toHomotopyCategory (B.{u,v,w,t} A) ⋙ QB).mapIso (homAtWrittenIso.{u,v,w,t} E G X).symm
  have allRepresentables (P : ObjectProperty (Derived.derivedCategory (B.{u,v,w,t} A) hB))
      [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
      (hrep : ∀ a : A.Obj, P (QB.obj (representable (pretrRepresentable A a))))
      (X : WrittenObject A) : P (QB.obj (representable X)) := by
    apply P.prop_of_iso (repIso X)
    exact writtenObjectsInTriangulatedSubcategory.{u,v,w,t} cA (P.inverseImage F)
      (fun a => P.prop_of_iso (repIso (pretrRepresentable A a)).symm (hrep a)) X
  intro Y vanishes
  let V := (ObjectProperty.ofObj (fun _ : Unit => Y)).shiftClosure ℤ
  have base (a : A.Obj) : V.leftOrthogonal (QB.obj (representable (pretrRepresentable A a))) := by
    intro Z g hZ
    rcases hZ with ⟨Y', n, e, i⟩
    obtain ⟨_, eq⟩ := (ObjectProperty.ofObj_iff _ _).mp i
    subst Y'
    let R := representable (A := B.{u,v,w,t} A) (pretrRepresentable A a)
    have hv (n : ℤ) : Subsingleton (QB.obj (ShiftCone.shift R n) ⟶ Y) := vanishes a n
    let e' := cB.onShift R (-n)
    have hv' : Subsingleton ((shiftFunctor _ (-n)).obj (QB.obj R) ⟶ Y) :=
      e'.homFromEquiv.subsingleton_congr.mp (hv (-n))
    have hV : Subsingleton (QB.obj R ⟶ (shiftFunctor _ n).obj Y) :=
      ((shiftEquiv _ n).symm.toAdjunction.homEquiv (QB.obj R) Y).subsingleton_congr.mp hv'
    exact (cancel_mono e.hom).mp (hV.elim _ _)
  apply (RightDGModule.representableCompactGenerators.{u,max v w,max v w,t,max v w t}.2.2.2
    (pretr A) hB Y).2
  intro X n
  let R := representable (A := B.{u,v,w,t} A) X
  have horth : V.leftOrthogonal (QB.obj R) :=
    allRepresentables V.leftOrthogonal base X
  have hshift := V.leftOrthogonal.le_shift (-n) (QB.obj R) horth
  let e := cB.onShift R (-n)
  have hy : V Y :=
    (ObjectProperty.ofObj (fun _ : Unit => Y)).le_shiftClosure (A := ℤ) Y (ObjectProperty.ofObj_apply _ ())
  have hs : Subsingleton ((shiftFunctor _ (-n)).obj (QB.obj R) ⟶ Y) :=
    ⟨fun f g => (hshift f hy).trans (hshift g hy).symm⟩
  exact e.homFromEquiv.subsingleton_congr.mpr hs

/-- The derived extension of scalars along the inclusion into the written hull. -/
theorem moritaHull : Specs.DerivedFormalization.DG.MoritaHull.HullDerivedEquivalence.{u,v,w,t} := by
  intro k _ A hA hB
  let T := hullBimodule.{u,v,w,t} A
  obtain ⟨L,G,U,adj,hlaws⟩ := underivedAdjunction.{u,max v w t,w,max v w}
    (C.{u,v,w,t} A) (B.{u,v,w,t} A) T
  let m : SignedModels.{u,max v w t,w,max v w} T := ⟨L,G,U,adj,hlaws⟩
  have hp (a : A.Obj) : KProjective.isKProjective (T.obj a) :=
    representable_kProjective (A := B.{u,v,w,t} A) (pretrRepresentable A a)
  obtain ⟨d, hd, hreps, hexact⟩ := exactDerivedAdjunctionAt.{u,max v w t,w,max v w} m hp hA hB
  refine ⟨writtenYoneda A, T, m, d, ?_, ?_, hd, hreps, hexact, ?_⟩
  · exact ⟨rfl, yonedaIso, yonedaIso_laws, fun a b => ⟨HEq.rfl, yoneda_map_isIso (A := A) a b⟩⟩
  · exact ⟨fun _ => Iso.refl _, hullBimodule_apply.{u,v,w,t} A⟩
  obtain ⟨S, hadd, _⟩ := RightDGModule.shiftedRepresentableHom.{u,max v w,max v w,t} (pretr A) hB
  apply (moritaCriterionAt.{u,max v w t,w,max v w} m hA hB S d hadd hd hreps hexact hp).2
  refine ⟨fun a => ?_, hullBimodule_quasiIso.{u,v,w,t} A, hullDetectsZero.{u,v,w,t} hA hB⟩
  exact RightDGModule.representableCompact.{u,max v w,max v w,t,max v w t} (pretr A) hB S hadd _

end
end DerivedFormalization.DGBimodule
