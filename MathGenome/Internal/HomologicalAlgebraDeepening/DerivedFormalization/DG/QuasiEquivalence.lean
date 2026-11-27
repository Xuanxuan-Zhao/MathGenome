import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.QuasiEquivalence
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactGenerators
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedBimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.MoritaCriterion
open CategoryTheory
open _root_.DerivedFormalization

namespace DerivedFormalization.DGFunctor

open Specs.DerivedFormalization.DG
open QuasiEquivalence
open Basic (cyclesZero classOf)
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open DerivedBimoduleAdjunction (LocalizedFunctor SignedModels)
open private representable_kProjective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective
open private yonedaIso_laws from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Yoneda

noncomputable section

section

universe u v w z

variable {k : Type u} [CommRing k]

private def upCycle {C : ModuleCochain.{u,v} k}
    (f : cyclesZero C) : cyclesZero (Yoneda.liftComplex.{u,v,w} C) :=
  ⟨ULift.up f.val, ULift.ext f.property⟩

private theorem upCycle_class_iff {C : ModuleCochain.{u,v} k} (f g : cyclesZero C) :
    classOf (upCycle.{u,v,w} f) = classOf (upCycle.{u,v,w} g) ↔ classOf f = classOf g := by
  rw [Submodule.Quotient.eq, Submodule.Quotient.eq]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.down, Subtype.ext (congrArg (fun q => q.val.down) hx)⟩
  · rintro ⟨x, hx⟩
    exact ⟨ULift.up x, Subtype.ext (ULift.ext (congrArg Subtype.val hx))⟩

private theorem liftFunctor_quasiEquivalence
    {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,z} k}
    (F : DGFunctorModel A B) (hF : Basic.quasiEquivalence F) :
    Basic.quasiEquivalence (liftFunctor F) := by
  refine ⟨fun a b => ?_, fun b => ?_⟩
  · letI := hF.1 a b
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let U := ModuleCat.uliftFunctor.{max w z,v} k
    have e := (DG.CoefficientLift.homologyComparison.{u,v,max w z} (k := k)).2 (F.map a b) i
    change IsIso (HomologicalComplex.homologyMap
      ((U.mapHomologicalComplex (ComplexShape.up ℤ)).map (F.map a b)) i)
    rw [← isIso_comp_right_iff _ (CoefficientLiftComparison.homologyIso
      (B.hom (F.obj a) (F.obj b)) i).hom, e]
    infer_instance
  · obtain ⟨a, f, g, hfg, hgf⟩ := hF.2 b
    let f₀ := Quotient.out f
    let g₀ := Quotient.out g
    have hf : classOf f₀ = f := Quotient.out_eq _
    have hg : classOf g₀ = g := Quotient.out_eq _
    rw [← hf, ← hg, DGCategory.h0Comp_mk] at hfg hgf
    refine ⟨a, classOf (upCycle.{u,v,max w z} f₀), classOf (upCycle.{u,v,max w z} g₀), ?_, ?_⟩
    · rw [DGCategory.h0Comp_mk]
      exact (upCycle_class_iff.{u,v,max w z} _ _).2 hfg
    · rw [DGCategory.h0Comp_mk]
      exact (upCycle_class_iff.{u,v,max w z} _ _).2 hgf

section Ambient

variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}

/-- Yoneda with its source at the common adequate coefficient bound. -/
private def ambientYoneda (B : DGCategoryModel.{u,max v w z,z} k) :
    DGFunctorModel B (HomComplex.dgModuleCategory B) where
  obj := Yoneda.representable
  map a b := (upIso.{u,max v w,z} (B.hom a b)).hom ≫ (RightDGModule.yoneda B).map a b
  map_id a := (RightDGModule.yoneda B).map_id a
  map_comp i j n h f g := (RightDGModule.yoneda B).map_comp i j n h (ULift.up f) (ULift.up g)

private theorem ambientYoneda_isYoneda (B : DGCategoryModel.{u,max v w z,z} k) :
    IsYoneda.{u,max v w,z} (ambientYoneda.{u,v,w,z} B) :=
  ⟨rfl, RightDGModule.yonedaIso, yonedaIso_laws, fun _ _ => HEq.rfl⟩

private def graphModels (F : DGFunctorModel A B) :
    SignedModels.{u,v,w,z} (graph.{u,v,w,z} F (ambientYoneda.{u,v,w,z} B)) where
  tensor := DGBimodule.tensorModel _
  hom := DGBimodule.internalHomModel _
  curry := DGBimodule.curryIso _
  adjunction := DGBimodule.adjunction _
  laws := DGBimodule.strictAdjunctionLaws _

private theorem graph_morphism_quasiIso (F : DGFunctorModel A B)
    (hF : Basic.quasiEquivalence F) :
    MoritaUnit.MorphismQuasiIsomorphisms.{u,v,w,z} (graph.{u,v,w,z} F (ambientYoneda.{u,v,w,z} B)) := by
  intro a b
  letI := hF.1 a b
  change QuasiIso (F.map a b ≫ ((upIso.{u,max v w,z} (B.hom (F.obj a) (F.obj b))).hom ≫
    (RightDGModule.yoneda B).map (F.obj a) (F.obj b)))
  infer_instance

private def homRestrictionIso (F : DGFunctorModel A B) :
    BimoduleAdjunction.ordinaryHom.{u,v,w,z} (graphModels.{u,v,w,z} F).hom ≅ restriction F := by
  let H := BimoduleAdjunction.ordinaryHom.{u,v,w,z} (graphModels.{u,v,w,z} F).hom
  let eval (N : RightDGModuleModel B) : H.obj N ≅ (restriction F).obj N :=
    DG.CoefficientLift.isoOfComponents
      (fun a i => RightDGModule.yonedaEquiv (F.obj a) N i)
      (fun a i x => RightDGModule.yonedaEquiv_comm_d (F.obj a) N i x)
      (by
        intro a b i j n h x f
        change RightDGModule.yonedaEquiv (F.obj a) N n
          ((HomComplex.dgModuleCategory B).comp i j n h x
            (RightDGModule.yonedaExtend (F.obj a) (Yoneda.representable (F.obj b)) j
              ((F.map a b).f j f))) =
          N.act i j n h (RightDGModule.yonedaEquiv (F.obj b) N i x) ((F.map a b).f j f)
        exact RightDGModule.yoneda_natural_object (F.obj a) N (F.obj b) i j n h x ((F.map a b).f j f))
  refine NatIso.ofComponents eval ?_
  intro N P f
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change RightDGModule.yonedaEquiv (F.obj a) P i
    ((HomComplex.dgModuleCategory B).comp 0 i i (zero_add i) (HomComplex.ofStrict f) g) =
    (f.app (F.obj a)).f i (RightDGModule.yonedaEquiv (F.obj a) N i g)
  exact RightDGModule.yoneda_natural_module (F.obj a) N 0 i i (zero_add i) (HomComplex.ofStrict f) g

/-- Shift and localize the Yoneda image of each isomorphism in the essential image. -/
private theorem graph_detectsZero (F : DGFunctorModel A B)
    (hs : (DGFunctor.H0 F).EssSurj) (hB : HomotopyCategoryLaws B)
    (detect : letI := Derived.homotopyCategory B hB
      letI := derivedCategoryInstance B hB
      ∀ X : Derived.derivedCategory B hB,
        (∀ (b : B.Obj) (n : ℤ),
          Subsingleton ((Derived.quotient B hB).obj (SemiFree.cell b n) ⟶ X)) → Limits.IsZero X) :
    MoritaCriterion.ShiftedImagesDetectZero.{u,v,w,z}
      (graph.{u,v,w,z} F (ambientYoneda.{u,v,w,z} B)) hB := by
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance B hB
  intro X hX
  apply detect X
  intro b n
  obtain ⟨a, ⟨e⟩⟩ := hs.mem_essImage b
  let eY := (DGFunctor.H0 (ambientYoneda.{u,v,w,z} B)).mapIso e
  let eS := (DGFunctor.H0 (ShiftCone.shiftDGFunctor B (-n))).mapIso eY
  let eD := (Derived.quotient B hB).mapIso eS
  refine ⟨fun f g => (cancel_epi eD.hom).1 ?_⟩
  exact @Subsingleton.elim _ (hX a (-n)) _ _

end Ambient

set_option backward.isDefEq.respectTransparency false in
/-- Transfer descent along a strict natural isomorphism, using the same derived functor. -/
private def rebaseDescent
    {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,z} k}
    {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
    {H R : RightDGModuleModel B ⥤ RightDGModuleModel A}
    (L : LocalizedFunctor hB hA H) (e : H ≅ R)
    (hR : ∀ {X Y : RightDGModuleModel B} (f : X ⟶ Y),
      Module.quasiIsomorphism f → Module.quasiIsomorphism (R.map f)) :
    LocalizedFunctor hB hA R := by
  letI := Derived.homotopyCategory A hA
  letI := Derived.homotopyCategory B hB
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  let π : RightDGModuleModel A ⥤ HomComplex.homotopyCategory A :=
    RightDGModule.toHomotopyCategory A
  let c (X : HomComplex.homotopyCategory B) : L.homotopy.obj X ≅ R.obj X :=
    eqToIso (L.obj X) ≪≫ π.mapIso (e.app X)
  refine
    { homotopy := L.homotopy.copyObj (fun X => R.obj X) c
      derived := L.derived
      obj := fun _ => rfl
      map := ?_
      square := L.square ≪≫ Functor.isoWhiskerRight
        (L.homotopy.isoCopyObj _ c) (Derived.quotient A hA)
      preservesQuasiIsomorphisms := hR }
  intro X Y f
  apply heq_of_eq
  have h := (conj_eqToHom_iff_heq _ (π.map (H.map f)) (L.obj X) (L.obj Y)).2 (L.map f)
  have hn : (e.app X).inv ≫ H.map f ≫ (e.app Y).hom = R.map f := by
    rw [show H.map f ≫ (e.app Y).hom = (e.app X).hom ≫ R.map f from e.hom.naturality f]
    simp
  change (c X).inv ≫ L.homotopy.map (HomComplex.homotopyClass f) ≫
    (c Y).hom = π.map (R.map f)
  change ((π.mapIso (e.app X)).inv ≫ eqToHom (L.obj X).symm) ≫
    L.homotopy.map (HomComplex.homotopyClass f) ≫
    (eqToHom (L.obj Y) ≫ (π.mapIso (e.app Y)).hom) = π.map (R.map f)
  rw [h]
  simp only [Category.assoc, Functor.mapIso_hom, Functor.mapIso_inv]
  rw [eqToHom_trans_assoc (L.obj X).symm (L.obj X),
    eqToHom_trans_assoc (L.obj Y).symm (L.obj Y)]
  simp only [eqToHom_refl, Category.id_comp, ← π.map_comp, hn]

/-- Restriction along a dg functor preserves every objectwise quasi-isomorphism. -/
private theorem restriction_quasiIso
    {A : DGCategoryModel.{u,v,w} k} {B : DGCategoryModel.{u,v,z} k}
    (F : DGFunctorModel A B) {X Y : RightDGModuleModel B} (f : X ⟶ Y)
    (hf : Module.quasiIsomorphism f) : Module.quasiIsomorphism ((restriction F).map f) :=
  fun a => hf (F.obj a)

end

set_option maxHeartbeats 1000000 in
/-- Invariance under quasi-equivalence, conditional on the ordered upstream results. -/
theorem derivedQuasiEquivalence_conditional.{u,v,w,z}
    (_adequateNativeProjectivityTransition : DerivedBimoduleAdjunction.AdequateNativeProjectivityTransition.{u,v,w,v,z,v})
    (_ambientDerivedAdjunction : DerivedBimoduleAdjunction.AmbientDerivedAdjunction.{u,v,w,v,z,v})
    (_ambientDerivedAdjunctionComparison : DerivedBimoduleAdjunction.AmbientDerivedAdjunctionComparison.{u,v,w,v,z,v,v})
    (_ambientExactDerivedAdjunction : DerivedBimoduleAdjunction.AmbientExactDerivedAdjunction.{u,v,w,v,z,v})
    (_ambientProjectivityTransition : DerivedBimoduleAdjunction.AmbientProjectivityTransition.{u,v,w,v,z,v,v})
    (_derivedAdjunctionAt : DerivedBimoduleAdjunction.DerivedAdjunctionAt.{u,v,w,z})
    (exactAdjunction : DerivedBimoduleAdjunction.ExactDerivedAdjunctionAt.{u,v,w,z})
    (_homShiftConeComparison : DerivedBimoduleAdjunction.HomShiftConeComparison.{u,v,w,z})
    (_nativeDerivedAdjunctionCompatibility : DerivedBimoduleAdjunction.NativeDerivedAdjunctionCompatibility.{u,v,w,z})
    (_nativeHomDescent : DerivedBimoduleAdjunction.NativeHomDescent.{u,v,w,v,z})
    (_nativeHomPreservesQuasiIsomorphisms : DerivedBimoduleAdjunction.NativeHomPreservesQuasiIsomorphisms.{u,v,w,v,z})
    (_tensorPreservesKProjectives : DerivedBimoduleAdjunction.TensorPreservesKProjectives.{u,v,w,z})
    (_ambientMorphismQuasiIsomorphisms : MoritaCriterion.AmbientMorphismQuasiIsomorphisms.{u,v,w,z,v,v})
    (morita : MoritaCriterion.MoritaCriterionAt.{u,v,w,z})
    : DerivedQuasiEquivalence.{u,v,w,z} := by
  intro k _ A B F hF
  let A' := AmbientDerived.category.{u,v,w,z} A
  let B' := AmbientDerived.category.{u,v,z,w} B
  let F' := liftFunctor F
  have hF' := liftFunctor_quasiEquivalence F hF
  refine ⟨hF', ?_⟩
  intro hA hB
  letI := Derived.homotopyCategory A' hA
  letI := Derived.homotopyCategory B' hB
  letI := derivedCategoryInstance A' hA
  letI := derivedCategoryInstance B' hB
  let Y := ambientYoneda.{u,v,w,z} B'
  let m := graphModels.{u,v,w,z} F'
  have hp : ∀ a, KProjective.isKProjective ((graph.{u,v,w,z} F' Y).obj a) :=
    fun a => representable_kProjective (A := B') (F'.obj a)
  obtain ⟨d, hRealizes, hComputes, hExact⟩ := exactAdjunction m hp hA hB
  obtain ⟨S, hadd, _⟩ := RightDGModule.shiftedRepresentableHom.{u,v,z,w} B hB
  have hc := RightDGModule.representableCompact.{u,v,z,w,max v w z} B hB S hadd
  have hdet :=
    (RightDGModule.representableCompactGenerators.{u,v,z,w,max v w z}).2.2.2 B hB
  have hes := (DGFunctor.isQuasiEquivalence_iff F').1 hF' |>.2
  letI : d.tensor.IsEquivalence :=
    (morita m hA hB S d hadd hRealizes hComputes hExact hp).mpr
      ⟨fun a => hc (F'.obj a), graph_morphism_quasiIso F' hF',
        graph_detectsZero F' hes hB (fun X hX => (hdet X).2 hX)⟩
  let R := rebaseDescent d.hom (homRestrictionIso F') (restriction_quasiIso F')
  have e : d.tensor ⊣ R.derived := d.adjunction
  letI : R.derived.IsEquivalence := e.isEquivalence_right_of_isEquivalence_left
  exact ⟨Y, ambientYoneda_isYoneda.{u,v,w,z} B', m, d, R,
    hRealizes, hComputes, hExact, e, inferInstance, inferInstance⟩

end
end DerivedFormalization.DGFunctor

universe v8_closure_2c0a2209160e2a70_u0 v8_closure_2c0a2209160e2a70_u1 v8_closure_2c0a2209160e2a70_u2 v8_closure_2c0a2209160e2a70_u3
theorem _root_.«DerivedFormalization».«DGFunctor».«derivedQuasiEquivalence» : _root_.«Specs».«DerivedFormalization».«DG».«QuasiEquivalence».«DerivedQuasiEquivalence».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u3} :=
  @_root_.«DerivedFormalization».«DGFunctor».«derivedQuasiEquivalence_conditional».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u3} (@_root_.«DerivedFormalization».«DGBimodule».«adequateNativeProjectivityTransition».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u3, v8_closure_2c0a2209160e2a70_u1}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientDerivedAdjunction».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u3, v8_closure_2c0a2209160e2a70_u1}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientDerivedAdjunctionComparison».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u3, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u1}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientExactDerivedAdjunction».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u3, v8_closure_2c0a2209160e2a70_u1}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientProjectivityTransition».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u3, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u1}) (@_root_.«DerivedFormalization».«DGBimodule».«derivedAdjunctionAt».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«exactDerivedAdjunctionAt».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«homShiftConeComparison».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeDerivedAdjunctionCompatibility».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeHomDescent».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeHomPreservesQuasiIsomorphisms».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«tensorPreservesKProjectives».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientMorphismQuasiIsomorphisms».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u3, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u1}) (@_root_.«DerivedFormalization».«DGBimodule».«moritaCriterionAt».{v8_closure_2c0a2209160e2a70_u0, v8_closure_2c0a2209160e2a70_u1, v8_closure_2c0a2209160e2a70_u2, v8_closure_2c0a2209160e2a70_u3})
