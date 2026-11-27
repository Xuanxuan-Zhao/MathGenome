import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.EndomorphismGenerator
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CoefficientLiftComparison

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.MoritaCriterion
open CategoryTheory

namespace DerivedFormalization.DGBimodule

open Specs.DerivedFormalization.DG
open BalancedTensor (CochainMap)
open EndomorphismGenerator
open HomComplex (component gradedHom homComplex)
open MoritaCriterion (AmbientMorphismQuasiIsomorphisms MoritaCriterionAt ShiftedImagesDetectZero)
open MoritaUnit (MorphismQuasiIsomorphisms toComplexHom)

noncomputable section

private abbrev endomorphismDegreeEquiv.{u,v,w,z}
    {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,z} k}
    (P : RightDGModuleModel B) (r : ℤ) :
    ((ambientEnd.{u,v,w,z} P).hom PUnit.unit PUnit.unit).X r ≃ₗ[k]
      gradedHom (ambientModule.{u,v,w,z} P) (ambientModule.{u,v,w,z} P) r :=
  ULift.moduleEquiv.trans (DG.CoefficientLift.gradedEquiv.{u,v,z,max v w z} P P r)

private def endomorphismComplexMap.{u,v,w,z}
    {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,z} k}
    (P : RightDGModuleModel B) :
    (ambientEnd.{u,v,w,z} P).hom PUnit.unit PUnit.unit ⟶
      homComplex (ambientModule.{u,v,w,z} P) (ambientModule.{u,v,w,z} P) :=
  toComplexHom
    { f := fun r => (endomorphismDegreeEquiv.{u,v,w,z} P r).toLinearMap
      comm := fun r x => DG.CoefficientLift.gradedEquiv_comm_d.{u,v,z,max v w z}
        r (r+1) x.down }

private instance endomorphismComplexMap_isIso.{u,v,w,z}
    {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,z} k} (P : RightDGModuleModel B) :
    IsIso (endomorphismComplexMap.{u,v,w,z} P) := by
  let (r : ℤ) : IsIso ((endomorphismComplexMap.{u,v,w,z} P).f r) :=
    (endomorphismDegreeEquiv.{u,v,w,z} P r).toModuleIso.isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem endomorphismComplexMap_component.{u,v,w,z}
    {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,z} k}
    (P : RightDGModuleModel B) (r : ℤ) (g : gradedHom P P r) (b : B.Obj)
    (i j : ℤ) (h : i+r=j) (x : (P.complex b).X i) :
    component ((endomorphismComplexMap.{u,v,w,z} P).f r (ULift.up g)) b i j h (ULift.up x) =
      ULift.up (component g b i j h x) :=
  ULift.ext (DG.CoefficientLift.gradedEquiv_apply_down.{u,v,z,max v w z}
    r g b i j h (ULift.up x))

private def endomorphismLiftFunctor.{u,v,w,z}
    {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,z} k} (P : RightDGModuleModel B) :
    DGFunctorModel (ambientEnd.{u,v,w,z} P)
      (endomorphismCategory.{u,max v w z,w,z} (ambientModule.{u,v,w,z} P)) where
  obj := id
  map _ _ := endomorphismComplexMap.{u,v,w,z} P
  map_id _ := by
    change DG.CoefficientLift.gradedEquiv.{u,v,z,max v w z} P P 0
        (HomComplex.ofStrict (𝟙 P)) = HomComplex.ofStrict (𝟙 (ambientModule.{u,v,w,z} P))
    rw [DG.CoefficientLift.gradedEquiv_strict]
    rfl
  map_comp i j n h f g :=
    DG.CoefficientLift.gradedEquiv_comp.{u,v,z,max v w z} i j n h f.down g.down

private theorem endomorphismComplexMap_eq_transport.{u,v,w,z}
    {k : Type u} [CommRing k] {B : DGCategoryModel.{u,v,z} k}
    (P : RightDGModuleModel B) {X : RightDGModuleModel (ambientBase.{u,v,w,z} B)}
    (e : X = ambientModule.{u,v,w,z} P)
    (f : CochainMap ((ambientEnd.{u,v,w,z} P).hom PUnit.unit PUnit.unit) (homComplex X X))
    (up : ∀ (b : B.Obj) (i : ℤ), (P.complex b).X i → (X.complex b).X i)
    (hup : ∀ (b : B.Obj) (i : ℤ) (x : (P.complex b).X i),
      HEq (up b i x) (ULift.up.{max v w z} x))
    (hact : ∀ (r : ℤ) (g : gradedHom P P r) (b : B.Obj)
        (i j : ℤ) (h : i+r=j) (x : (P.complex b).X i),
      component (f.f r (ULift.up g)) b i j h (up b i x) = up b j (component g b i j h x)) :
    toComplexHom f ≫ eqToHom (congrArg (fun M => homComplex M M) e) =
      endomorphismComplexMap.{u,v,w,z} P := by
  subst X
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨g⟩
  apply RightDGModule.GradedHom.ext
  intro b i j h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x⟩
  exact (by simpa only [eq_of_heq (hup b i x),
    eq_of_heq (hup b j (component g b i j h x))] using hact r g b i j h x
    : component (f.f r (ULift.up g)) b i j h (ULift.up x) =
        ULift.up (component g b i j h x)).trans
    (endomorphismComplexMap_component.{u,v,w,z} P r g b i j h x).symm

theorem endomorphismLiftComparison_conditional.{u,v,w,z}
    (_ambient : AmbientMorphismQuasiIsomorphisms.{u,v,w,z,v,w})
    (_criterion : MoritaCriterionAt.{u,v,w,z}) :
    EndomorphismLiftComparison.{u,v,w,z} := by
  intro k _ B P
  refine ⟨endomorphismLiftFunctor.{u,v,w,z} P, fun _ _ => endomorphismComplexMap_isIso.{u,v,w,z} P,
    endomorphismComplexMap_component.{u,v,w,z} P, ?_⟩
  intro m
  let e := m.comparisonLaws.obj_eq PUnit.unit
  refine ⟨e, endomorphismComplexMap_eq_transport.{u,v,w,z} P e (m.bimodule.map PUnit.unit PUnit.unit)
    (fun b i x => (m.comparison PUnit.unit).degree b i x)
    (m.comparisonLaws.term_up PUnit.unit) ?_⟩
  intro r g b i j h x
  exact (m.comparisonLaws.left_action b (a := PUnit.unit) (a' := PUnit.unit)
    r i j (by omega) g x).symm

theorem ambientEndomorphismEquivalence_conditional.{u,v,w,z}
    (ambient : AmbientMorphismQuasiIsomorphisms.{u,v,w,z,v,w})
    (criterion : MoritaCriterionAt.{u,v,w,z}) :
    AmbientEndomorphismEquivalence.{u,v,w,z} := by
  intro k _ B P m hA hB S d hAdd hReal hRep hExact hProj hCompact hDetect
  have obj_eq (a : (ambientEnd.{u,v,w,z} P).Obj) :
      m.bimodule.obj a = ambientModule.{u,v,w,z} P :=
    m.comparisonLaws.obj_eq a
  have hAllProj (a : (ambientEnd.{u,v,w,z} P).Obj) :
      KProjective.isKProjective (m.bimodule.obj a) := by
    rw [obj_eq a]
    exact hProj
  -- The two records use the same adequate coefficient universe max v w z.
  let models : DerivedBimoduleAdjunction.SignedModels.{u,v,w,z} m.bimodule :=
    { tensor := m.models.tensor
      hom := m.models.hom
      curry := m.models.curry
      adjunction := m.models.adjunction
      laws := BimoduleAdjunction.StrictLaws.mk.{u,v,w,z}
        m.models.laws.apply_tmul m.models.laws.homEquiv m.models.laws.unit m.models.laws.counit }
  refine (criterion (A := ambientEnd.{u,v,w,z} P) (B := ambientBase.{u,v,w,z} B)
    (T := m.bimodule) models hA hB S d hAdd hReal hRep hExact hAllProj).2
    ⟨?_, ?_, ?_⟩
  · intro a
    rw [obj_eq a]
    exact hCompact
  · rcases endomorphismLiftComparison_conditional.{u,v,w,z} ambient criterion P with ⟨F, hIso, _, hMap⟩
    obtain ⟨e, h⟩ := hMap m
    rintro ⟨⟩ ⟨⟩
    let f := toComplexHom (m.bimodule.map PUnit.unit PUnit.unit)
    let g := eqToHom (congrArg (fun M => homComplex M M) e)
    have hComp : IsIso (f ≫ g) := by
      rw [h]
      exact hIso _ _
    have : IsIso f := (isIso_comp_right_iff f g).mp hComp
    exact quasiIso_of_isIso f
  · intro Y hY
    apply hDetect Y
    intro n
    simpa only [obj_eq PUnit.unit] using hY PUnit.unit n

theorem nativeEndomorphismEquivalence_conditional.{u,v,w,z}
    (_ambient : AmbientMorphismQuasiIsomorphisms.{u,v,w,z,v,w})
    (criterion : MoritaCriterionAt.{u,v,w,z}) :
    NativeEndomorphismEquivalence.{u,v,w,z} := by
  intro k _ B P m hA hB S d hAdd hReal hRep hExact hProj hCompact hDetect
  refine (criterion m hA hB S d hAdd hReal hRep hExact (fun _ => hProj)).2
    ⟨fun _ => hCompact, ?_, fun Y hY => hDetect Y (hY PUnit.unit)⟩
  intro a b
  have h : toComplexHom ((endomorphismAction.{u,max v w z,w,z} P).map a b) =
      𝟙 (homComplex P P) := by
    apply HomologicalComplex.Hom.ext
    rfl
  rw [h]
  have : IsIso (𝟙 (homComplex P P)) := IsIso.id _
  exact quasiIso_of_isIso (𝟙 (homComplex P P))

end

end DerivedFormalization.DGBimodule

universe v8_closure_318085afc7002614_u0 v8_closure_318085afc7002614_u1 v8_closure_318085afc7002614_u2 v8_closure_318085afc7002614_u3
theorem _root_.«DerivedFormalization».«DGBimodule».«ambientEndomorphismEquivalence» : _root_.«Specs».«DerivedFormalization».«DG».«EndomorphismGenerator».«AmbientEndomorphismEquivalence».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3} :=
  @_root_.«DerivedFormalization».«DGBimodule».«ambientEndomorphismEquivalence_conditional».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3} (@_root_.«DerivedFormalization».«DGBimodule».«ambientMorphismQuasiIsomorphisms».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2}) (@_root_.«DerivedFormalization».«DGBimodule».«moritaCriterionAt».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3})
theorem _root_.«DerivedFormalization».«DGBimodule».«endomorphismLiftComparison» : _root_.«Specs».«DerivedFormalization».«DG».«EndomorphismGenerator».«EndomorphismLiftComparison».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3} :=
  @_root_.«DerivedFormalization».«DGBimodule».«endomorphismLiftComparison_conditional».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3} (@_root_.«DerivedFormalization».«DGBimodule».«ambientMorphismQuasiIsomorphisms».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2}) (@_root_.«DerivedFormalization».«DGBimodule».«moritaCriterionAt».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3})
theorem _root_.«DerivedFormalization».«DGBimodule».«nativeEndomorphismEquivalence» : _root_.«Specs».«DerivedFormalization».«DG».«EndomorphismGenerator».«NativeEndomorphismEquivalence».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3} :=
  @_root_.«DerivedFormalization».«DGBimodule».«nativeEndomorphismEquivalence_conditional».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3} (@_root_.«DerivedFormalization».«DGBimodule».«ambientMorphismQuasiIsomorphisms».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2}) (@_root_.«DerivedFormalization».«DGBimodule».«moritaCriterionAt».{v8_closure_318085afc7002614_u0, v8_closure_318085afc7002614_u1, v8_closure_318085afc7002614_u2, v8_closure_318085afc7002614_u3})
