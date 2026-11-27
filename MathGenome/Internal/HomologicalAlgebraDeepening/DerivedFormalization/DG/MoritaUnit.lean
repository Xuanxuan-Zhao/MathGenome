import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.MoritaUnit
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactGenerators
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactFiniteCells
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedBimoduleAdjunction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.MoritaUnit

namespace DerivedFormalization.DGBimodule

open BalancedTensor (bimodule tmul left)
open BimoduleAdjunction (ordinaryHom ordinaryTensor)
open Derived (HomotopyCategoryLaws)
open DerivedBimoduleAdjunction
open DerivedKProjective (derivedCategoryInstance replacementIso)
open HomComplex (homotopyClass component ofStrict dgModuleCategory)
open KProjective (isKProjective)
open Yoneda (representable)
open private representable_kProjective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective
open private hom_eq_of_heq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift

universe u v w vA z t s j v' w'

noncomputable section

set_option allowUnsafeReducibility true in
attribute [local reducible] Derived.derivedCategory
local notation "D" => Derived.derivedCategory
local notation "Q" => Derived.quotient

set_option linter.style.haveILetI false
set_option linter.checkUnivs false

section AtBound

variable {k : Type u} [CommRing k]
variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {T : bimodule A B} (m : SignedModels.{u,v,w,z} T)
variable {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}

set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option hygiene false in
local notation "F₀" => ordinaryTensor.{u,v,w,z} m.tensor
set_option hygiene false in
local notation "G₀" => ordinaryHom.{u,v,w,z} m.hom

set_option maxHeartbeats 500000 in
private theorem strictRepresentableUnit (b : A.Obj)
    (e : (F₀).obj (representable (A := A) b) ≅ T.obj b)
    (he : ∀ (a : A.Obj) (c : B.Obj) (i j n : ℤ) (h : i+j=n)
      (f : (A.hom a b).X i) (x : ((T.obj a).complex c).X j),
      (e.hom.app c).f n (m.tensor.degree (representable b) c n
        (tmul T (representable b) c a i j n h f x)) = left T c i j n h f x)
    (a : A.Obj) :
    (m.adjunction.unit.app (representable b) ≫ (G₀).map e.hom).app a ≫
      (m.hom.objectwise (T.obj b) a).inv = toComplexHom (T.map a b) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  let R := representable (A := A) b
  let g : HomComplex.gradedHom (T.obj a) ((F₀).obj R) i :=
    (m.hom.objectwise ((F₀).obj R) a).inv.f i (((m.adjunction.unit.app R).app a).f i f)
  have hg : (m.hom.objectwise ((F₀).obj R) a).hom.f i g =
      ((m.adjunction.unit.app R).app a).f i f :=
    (HomologicalComplex.congr_hom (m.hom.objectwise ((F₀).obj R) a).inv_hom_id i) |> fun h =>
      CategoryTheory.congr_fun h _
  have hm := m.hom.map e.hom a i g
  change (m.hom.objectwise (T.obj b) a).inv.f i
    ((((G₀).map e.hom).app a).f i (((m.adjunction.unit.app R).app a).f i f)) = (T.map a b).f i f
  rw [← hg]
  change (m.hom.objectwise (T.obj b) a).inv.f i
    (((m.hom.functor.map e.hom).app a).f i ((m.hom.objectwise ((F₀).obj R) a).hom.f i g)) = _
  rw [hm]
  let p := (dgModuleCategory B).comp 0 i i (zero_add i) (ofStrict e.hom) g
  change (m.hom.objectwise (T.obj b) a).inv.f i ((m.hom.objectwise (T.obj b) a).hom.f i p) =
    (T.map a b).f i f
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, HomologicalComplex.id_f, ModuleCat.id_apply]
  apply Subtype.ext
  funext c
  apply CochainComplex.HomComplex.Cochain.ext
  intro j n h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((g.val c).comp (CochainComplex.HomComplex.Cochain.ofHom (e.hom.app c)) (add_zero i)).v j n h) x =
    component ((T.map a b).f i f) c j n h x
  rw [CochainComplex.HomComplex.Cochain.comp_v _ _ _ j n n h (add_zero n),
    ModuleCat.comp_apply, CochainComplex.HomComplex.Cochain.ofHom_v]
  have hji : i + j = n := (add_comm i j).trans h
  change (e.hom.app c).f n (component g c j n h x) = left T c i j n hji f x
  rw [m.laws.unit R a c i j n hji f x]
  exact he a c i j n hji f x

variable (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB)

local instance (C : DGCategoryModel.{u,v',w'} k) :
    Category (HomComplex.homotopyCategory C) := RightDGModule.instCategoryK C
local instance (C : DGCategoryModel.{u,v',w'} k) (h : HomotopyCategoryLaws C) :
    Category (D C h) := derivedCategoryInstance C h

local notation "QA" => Q A hA
local notation "QB" => Q B hB

set_option hygiene false in
local notation "homDescent" => DerivedAdjunctionData.hom.{u,v,w,z} d
set_option hygiene false in
local notation "homotopyTensor" => DerivedAdjunctionData.tensorH.{u,v,w,z} d
set_option hygiene false in
local notation "resolutionFunctor" => DerivedAdjunctionData.resolution.{u,v,w,z} d
set_option hygiene false in
local notation "resolutionAdjunction" => DerivedAdjunctionData.resolutionAdjunction.{u,v,w,z} d
set_option hygiene false in
local notation "homotopyAdjunction" => DerivedAdjunctionData.homotopyAdjunction.{u,v,w,z} d
set_option hygiene false in
local notation "derivedAdjunction" => DerivedAdjunctionData.adjunction.{u,v,w,z} d

set_option maxHeartbeats 500000 in
private theorem onInput_naturality {N N' : RightDGModuleModel B} (f : N ⟶ N') :
    (homDescent).derived.map ((QB).map (homotopyClass f)) ≫
      (DerivedAdjunctionData.onInput.{u,v,w,z} d N').hom =
      (DerivedAdjunctionData.onInput.{u,v,w,z} d N).hom ≫ (QA).map (homotopyClass ((G₀).map f)) := by
  let g : @Quiver.Hom (HomComplex.homotopyCategory B) _ N N' := homotopyClass f
  have h := (homDescent).square.hom.naturality g
  change (homDescent).derived.map ((QB).map g) ≫ (homDescent).square.hom.app N' =
    (homDescent).square.hom.app N ≫ (QA).map ((homDescent).homotopy.map g) at h
  have e := hom_eq_of_heq ((homDescent).obj N) ((homDescent).obj N') ((homDescent).map f)
  change (homDescent).derived.map ((QB).map g) ≫ (homDescent).square.hom.app N' ≫
      eqToHom (congrArg (QA).obj ((homDescent).obj N')) =
    ((homDescent).square.hom.app N ≫ eqToHom (congrArg (QA).obj ((homDescent).obj N))) ≫
      (QA).map (homotopyClass ((G₀).map f))
  erw [← Category.assoc, h]
  simp only [Category.assoc]
  apply congrArg (fun z => (homDescent).square.hom.app N ≫ z)
  erw [← eqToHom_map (QA) ((homDescent).obj N'),
    ← eqToHom_map (QA) ((homDescent).obj N),
    ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (QA).map e

set_option maxHeartbeats 500000 in
private theorem unit_representative (hd : (DerivedAdjunctionData.Realizes.{u,v,w,z} d) m.adjunction)
    (ht : DerivedAdjunctionData.ComputesRepresentatives.{u,v,w,z} d)
    (R : RightDGModuleModel A) (hp : isKProjective R) :
    (derivedAdjunction).unit.app ((QA).obj R) ≫
      (homDescent).derived.map (DerivedAdjunctionData.onProjective.{u,v,w,z} d R hp).hom ≫
      ((DerivedAdjunctionData.onInput.{u,v,w,z} d) ((F₀).obj R)).hom =
    (QA).map (homotopyClass (m.adjunction.unit.app R)) := by
  let c := (resolutionAdjunction).counit.app R
  have hsq := (homDescent).square.inv.naturality ((homotopyTensor).map c)
  change (QA).map ((homDescent).homotopy.map ((homotopyTensor).map c)) ≫ (homDescent).square.inv.app ((homotopyTensor).obj R) =
      (homDescent).square.inv.app ((homotopyTensor).obj ((resolutionFunctor).obj ((QA).obj R))) ≫
        (homDescent).derived.map ((QB).map ((homotopyTensor).map c)) at hsq
  have hη := (homotopyAdjunction).unit.naturality c
  change c ≫ (homotopyAdjunction).unit.app R =
      (homotopyAdjunction).unit.app ((resolutionFunctor).obj ((QA).obj R)) ≫
        (homDescent).homotopy.map ((homotopyTensor).map c) at hη
  have htriangle := (resolutionAdjunction).right_triangle_components R
  have htcomp := ht.1 R hp
  let e : (homotopyTensor).obj R ≅ (F₀).obj R :=
    eqToIso (DerivedAdjunctionData.tensorObj.{u,v,w,z} d R)
  have hunit := hd.2.2.2.2.1 ((QA).obj R)
  change (derivedAdjunction).unit.app ((QA).obj R) ≫
      (homDescent).derived.map
        ((DerivedAdjunctionData.tensorSquare.{u,v,w,z} d).hom.app ⟨R, hp⟩ ≫
          eqToHom (congrArg (QB).obj (DerivedAdjunctionData.tensorObj.{u,v,w,z} d R))) ≫
      ((homDescent).square.hom.app ((F₀).obj R) ≫ eqToHom (congrArg (QA).obj ((homDescent).obj ((F₀).obj R)))) =
    (QA).map (homotopyClass (m.adjunction.unit.app R))
  have hsq' := (homDescent).square.hom.naturality e.hom
  change (homDescent).derived.map ((QB).map e.hom) ≫ (homDescent).square.hom.app ((F₀).obj R) =
      (homDescent).square.hom.app ((homotopyTensor).obj R) ≫ (QA).map ((homDescent).homotopy.map e.hom) at hsq'
  erw [hunit, htcomp, ← eqToHom_map (QB) ((DerivedAdjunctionData.tensorObj.{u,v,w,z} d) R)]
  simp only [Functor.map_comp, Category.assoc]
  simp only [e, eqToIso.hom] at hsq'
  erw [reassoc_of% hsq']
  erw [← (reassoc_of% hsq), Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, ← hη,
    Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% htriangle]
  erw [← eqToHom_map (QA) ((homDescent).obj ((F₀).obj R))]
  simp only [← Functor.map_comp]
  apply congrArg (QA).map
  have hx := hom_eq_of_heq rfl ((congrArg (homDescent).homotopy.obj ((DerivedAdjunctionData.tensorObj.{u,v,w,z} d) R)).trans
    ((homDescent).obj ((F₀).obj R))) (hd.2.2.1 R)
  change (homotopyAdjunction).unit.app R ≫ (homDescent).homotopy.map e.hom ≫
      eqToHom ((homDescent).obj ((F₀).obj R)) = _
  rw [show e.hom = eqToHom ((DerivedAdjunctionData.tensorObj.{u,v,w,z} d) R) from rfl, eqToHom_map, eqToHom_trans]
  simpa using hx

set_option maxHeartbeats 550000 in
private theorem computesRepresentableUnit (hd : (DerivedAdjunctionData.Realizes.{u,v,w,z} d) m.adjunction)
    (ht : (DerivedAdjunctionData.ComputesRepresentatives.{u,v,w,z} d)) : ComputesRepresentableUnit.{u,v,w,z} d := by
  intro b
  let R := representable (A := A) b
  have hp : isKProjective R := representable_kProjective b
  obtain ⟨e, he, _⟩ := ht.2 b
  have he' := fun a c i j n h f x => he c a i j n h f x
  refine ⟨hp, e, he', strictRepresentableUnit m b e he', ?_⟩
  have hc := unit_representative m d hd ht R hp
  have hn := onInput_naturality m d e.hom
  erw [Functor.map_comp, Category.assoc, hn]
  simp only [← Category.assoc] at hc ⊢
  erw [hc]
  exact ((RightDGModule.toHomotopyCategory A ⋙ QA).map_comp
    (m.adjunction.unit.app R) ((G₀).map e.hom)).symm

end AtBound

section Categorical

open scoped DirectSum
open CompactRepresentables (coproductHomMap IsCompact)
open private coproductHomMap_of from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables

variable {C E : Type*} [Category* C] [Category* E]
variable [Preadditive C] [Preadditive E]

/-- Adjunction identifies the comparison for maps from a test object with
the comparison for maps from its image under the left adjoint. -/
private theorem adjoint_coproductHomMap {F : C ⥤ E} {G : E ⥤ C}
    (a : F ⊣ G) [G.Additive] (X : C) {I : Type j} {N : I → E} (c : Cofan N) :
    Function.Bijective (coproductHomMap (F.obj X) c) ↔
      Function.Bijective (coproductHomMap X (mapCofan G c)) := by
  classical
  letI : F.Additive := a.left_adjoint_additive
  let f (i : I) := (a.homAddEquiv X (N i)).toAddMonoidHom
  let e := (a.homAddEquiv X c.pt).toAddMonoidHom
  have hsum : Function.Bijective (DirectSum.map f) :=
    ⟨(DirectSum.map_injective f).mpr (fun i => (a.homAddEquiv X (N i)).injective),
      (DirectSum.map_surjective f).mpr (fun i => (a.homAddEquiv X (N i)).surjective)⟩
  have h : e.comp (coproductHomMap (F.obj X) c) =
      (coproductHomMap X (mapCofan G c)).comp (DirectSum.map f) := by
    apply DirectSum.addHom_ext
    intro i x
    change e (coproductHomMap (F.obj X) c (DirectSum.of _ i x)) =
      coproductHomMap X (mapCofan G c) (DirectSum.map f (DirectSum.of _ i x))
    rw [DirectSum.map_of, coproductHomMap_of, coproductHomMap_of]
    change a.homEquiv X c.pt (x ≫ c.inj i) =
      a.homEquiv X (N i) x ≫ G.map (c.inj i)
    exact a.homEquiv_naturality_right x (c.inj i)
  have he : Function.Bijective e := (a.homAddEquiv X c.pt).bijective
  constructor
  · intro hc
    apply (Function.Bijective.of_comp_iff _ hsum).mp
    change Function.Bijective ((coproductHomMap X (mapCofan G c)).comp (DirectSum.map f))
    rw [← h]
    exact he.comp hc
  · intro hc
    apply (he.of_comp_iff' _).mp
    change Function.Bijective (e.comp (coproductHomMap (F.obj X) c))
    rw [h]
    exact hc.comp hsum

omit [Preadditive C] [Preadditive E] in
private theorem mapCofan_preserves (G : E ⥤ C) (hG : PreservesColimitsOfSize.{j, j} G)
    {I : Type j} {N : I → E} (c : Cofan N) (hc : IsColimit c) :
    Nonempty (IsColimit (mapCofan G c)) := by
  letI := hG
  let c' : Cofan N := Cofan.mk c.pt c.inj
  let hc' : IsColimit c' := hc.ofIsoColimit (Cofan.ext (Iso.refl _) (by simp [c']))
  exact ⟨isColimitCofanMkObjOfIsColimit G N c.inj hc'⟩

private theorem compact_shift [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    {X : C} (hX : IsCompact.{j} X) (n : ℤ) :
    IsCompact.{j} ((shiftFunctor C n).obj X) := by
  let e := shiftEquiv C n
  letI : e.inverse.Additive := inferInstanceAs ((shiftFunctor C (-n)).Additive)
  intro I N c hc
  obtain ⟨hm⟩ := mapCofan_preserves e.inverse (by infer_instance) c hc
  exact (adjoint_coproductHomMap e.toAdjunction X c).mpr (hX _ hm)

private theorem compact_iso {X Y : C} (e : X ≅ Y) (hX : IsCompact.{j} X) :
    IsCompact.{j} Y := by
  classical
  intro I N c hc
  let E (Z : C) : (X ⟶ Z) ≃+ (Y ⟶ Z) :=
    { toEquiv := e.homCongr (Iso.refl Z)
      map_add' := fun a b => by simp [Iso.homCongr, Preadditive.comp_add] }
  let f (i : I) := (E (N i)).toAddMonoidHom
  let g := (E c.pt).toAddMonoidHom
  have hsum : Function.Bijective (DirectSum.map f) :=
    ⟨(DirectSum.map_injective f).mpr (fun i => (E (N i)).injective),
      (DirectSum.map_surjective f).mpr (fun i => (E (N i)).surjective)⟩
  have h : g.comp (coproductHomMap X c) = (coproductHomMap Y c).comp (DirectSum.map f) := by
    apply DirectSum.addHom_ext
    intro i x
    simp [coproductHomMap_of, g, f, E, Iso.homCongr, Category.assoc]
  apply (Function.Bijective.of_comp_iff _ hsum).mp
  change Function.Bijective ((coproductHomMap Y c).comp (DirectSum.map f))
  rw [← h]
  exact (E c.pt).bijective.comp (hX c hc)

private theorem isIso_of_compact_tests
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {ι : Type*} (P : ι → C)
    (detect : ∀ Z, (∀ i, Subsingleton (P i ⟶ Z)) → IsZero Z)
    (shiftTest : ∀ i, ∃ i', Nonempty (P i ≅ (shiftFunctor C (1 : ℤ)).obj (P i')))
    {X Y : C} (f : X ⟶ Y) (test : ∀ i, Function.Bijective (fun g : P i ⟶ X => g ≫ f)) :
    IsIso f := by
  obtain ⟨Z, g, h, ht⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  have hz : IsZero Z := by
    apply detect
    intro i
    obtain ⟨i', ⟨e⟩⟩ := shiftTest i
    let S := shiftFunctor C (1 : ℤ)
    have hshift (v : P i ⟶ S.obj X) (hv : v ≫ S.map f = 0) : v = 0 := by
      obtain ⟨q, hq⟩ := S.map_surjective (e.inv ≫ v)
      have hqf : q ≫ f = 0 := S.map_injective (by
        rw [Functor.map_comp, hq, Category.assoc, hv, comp_zero, Functor.map_zero])
      have hq0 : q = 0 := (test i').injective (by
        rw [hqf, zero_comp])
      apply (cancel_epi e.inv).mp
      rw [← hq, hq0, Functor.map_zero, comp_zero]
    have hv0 (v : P i ⟶ Z) : v = 0 := by
      have hvg : v ≫ h = 0 := hshift (v ≫ h) (by
        change (v ≫ T.mor₃) ≫ (shiftFunctor C (1 : ℤ)).map T.mor₁ = 0
        rw [Category.assoc, comp_distTriang_mor_zero₃₁ T ht, comp_zero])
      obtain ⟨r, hr⟩ := T.coyoneda_exact₃ ht v hvg
      obtain ⟨q, hq⟩ := (test i).surjective r
      change v = r ≫ g at hr
      change q ≫ f = r at hq
      rw [hr, ← hq, Category.assoc]
      change q ≫ T.mor₁ ≫ T.mor₂ = 0
      rw [comp_distTriang_mor_zero₁₂ T ht, comp_zero]
    exact ⟨fun v v' => (hv0 v).trans (hv0 v').symm⟩
  exact (T.isZero₃_iff_isIso₁ ht).mp hz

private theorem colimit_of_tests {ι : Type*} (P : ι → C)
    (detect : ∀ {X Y : C} (f : X ⟶ Y),
      (∀ i, Function.Bijective (fun g : P i ⟶ X => g ≫ f)) → IsIso f)
    {I : Type j} {N : I → C} (c c' : Cofan N) (hc' : IsColimit c')
    (compact : ∀ i, IsCompact.{j} (P i))
    (test : ∀ i, Function.Bijective (coproductHomMap (P i) c)) :
    Nonempty (IsColimit c) := by
  classical
  let f := Cofan.IsColimit.desc hc' c.inj
  have hf (i : I) : c'.inj i ≫ f = c.inj i := Cofan.IsColimit.fac hc' c.inj i
  have hiso : IsIso f := detect f (fun i => by
    have h : (Preadditive.rightComp (P i) f).comp (coproductHomMap (P i) c') =
        coproductHomMap (P i) c := by
      apply DirectSum.addHom_ext
      intro j x
      change coproductHomMap (P i) c' (DirectSum.of _ j x) ≫ f =
        coproductHomMap (P i) c (DirectSum.of _ j x)
      rw [coproductHomMap_of, coproductHomMap_of, Category.assoc, hf j]
    apply (Function.Bijective.of_comp_iff _ (compact i c' hc')).mp
    change Function.Bijective ((Preadditive.rightComp (P i) f).comp (coproductHomMap (P i) c'))
    exact h.symm ▸ test i)
  exact ⟨hc'.ofIsoColimit (Cofan.ext (asIso f) hf)⟩

/-- A coproduct over the nonzero summands is a coproduct over the
whole family, with zero inclusions on the omitted objects. -/
private theorem exists_cofan_of_small_nonzero_summands
    {I : Type j} (N : I → C) [Small.{v} {i : I // ¬ IsZero (N i)}]
    (existsSum : ∀ {J : Type v} (M : J → C), ∃ c : Cofan M, Nonempty (IsColimit c)) :
    ∃ c : Cofan N, Nonempty (IsColimit c) := by
  classical
  let J := {i : I // ¬ IsZero (N i)}
  let e := equivShrink J
  obtain ⟨c, ⟨hc⟩⟩ := existsSum (fun x => N (e.symm x).val)
  let r : Cofan (fun i : J => N (e.symm (e i)).val) := Cofan.mk c.pt (fun i => c.inj (e i))
  let hr : IsColimit r := (Cofan.isColimitEquivOfEquiv e c) hc
  let α : Discrete.functor (fun i : J => N i.val) ≅
      Discrete.functor (fun i : J => N (e.symm (e i)).val) :=
    Discrete.natIso fun i => eqToIso (congrArg (fun i : J => N i.val) (e.symm_apply_apply i.as).symm)
  let b : Cofan (fun i : J => N i.val) := (Cocone.precompose α.hom).obj r
  let hb : IsColimit b := (IsColimit.precomposeHomEquiv α r).symm hr
  let inj (i : I) : N i ⟶ b.pt := if h : ¬IsZero (N i) then Cofan.inj b ⟨i, h⟩ else 0
  refine ⟨Cofan.mk b.pt inj, ⟨Cofan.IsColimit.mk _ (fun c' =>
    Cofan.IsColimit.desc hb (fun i => c'.inj i.val)) ?_ ?_⟩⟩
  · intro c' i
    change inj i ≫ _ = _
    by_cases h : IsZero (N i)
    · exact h.eq_of_src _ _
    · rw [show inj i = Cofan.inj b ⟨i, h⟩ from dite_eq_left h]
      exact Cofan.IsColimit.fac hb _ _
  · intro c' g hg
    apply hb.hom_ext
    rintro ⟨i⟩
    change Cofan.inj b i ≫ g = Cofan.inj b i ≫ Cofan.IsColimit.desc hb (fun i => c'.inj i.val)
    rw [Cofan.IsColimit.fac]
    have hi := hg i.val
    change inj i.val ≫ g = c'.inj i.val at hi
    rwa [show inj i.val = Cofan.inj b i from dite_eq_left i.property] at hi

end Categorical

section UnitClosure

open CompactGenerators (CoproductClosed)
open ZeroObject

variable {C E : Type*} [Category* C] [Category* E]
variable {F : C ⥤ E} {G : E ⥤ C} (a : F ⊣ G)

private def unitIsomorphism : ObjectProperty C := fun X => IsIso (a.unit.app X)

private theorem unitIsomorphism_closed : (unitIsomorphism a).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    haveI : IsIso (a.unit.app X) := hX
    change IsIso (a.unit.app Y)
    rw [show a.unit.app Y = e.inv ≫ a.unit.app X ≫ (F ⋙ G).map e.hom by
      simp]
    infer_instance

variable [Preadditive C] [Preadditive E] [HasZeroObject C] [HasZeroObject E]
  [HasShift C ℤ] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated C] [Pretriangulated E]
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated] [a.CommShift ℤ]

private theorem unitIsomorphism_triangulated : (unitIsomorphism a).IsTriangulated := by
  letI := unitIsomorphism_closed a
  refine
    { exists_zero := ⟨0, isZero_zero C, (isZero_zero C).isIso
        ((F ⋙ G).map_isZero (isZero_zero C)) _⟩
      isStableUnderShiftBy := fun n => ⟨?_⟩
      toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' ?_ }
  · intro X hX
    haveI : IsIso (a.unit.app X) := hX
    change IsIso (a.unit.app ((shiftFunctor C n).obj X))
    rw [← a.unit_app_shift_commShiftIso_inv_app ℤ n X]
    infer_instance
  · intro T hT h₁ h₃
    let H := F ⋙ G
    let f : T ⟶ H.mapTriangle.obj T :=
      { hom₁ := a.unit.app T.obj₁
        hom₂ := a.unit.app T.obj₂
        hom₃ := a.unit.app T.obj₃
        comm₁ := a.unit.naturality T.mor₁
        comm₂ := a.unit.naturality T.mor₂
        comm₃ := by
          change T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map (a.unit.app T.obj₁) =
            a.unit.app T.obj₃ ≫ H.map T.mor₃ ≫ (H.commShiftIso (1 : ℤ)).hom.app T.obj₁
          have hn := a.unit.naturality T.mor₃
          change T.mor₃ ≫ a.unit.app ((shiftFunctor C (1 : ℤ)).obj T.obj₁) =
            a.unit.app T.obj₃ ≫ H.map T.mor₃ at hn
          rw [← a.unit_app_commShiftIso_hom_app ℤ, reassoc_of% hn] }
    haveI : IsIso f.hom₁ := h₁
    haveI : IsIso f.hom₃ := h₃
    exact isIso₂_of_isIso₁₃ f hT (H.map_distinguished T hT) h₁ h₃

omit [a.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [F.CommShift ℤ] [G.CommShift ℤ] [Pretriangulated C] [Pretriangulated E]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
  [HasShift C ℤ] [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E]
  [Preadditive C] [Preadditive E] in
private theorem unitIsomorphism_coproducts (hG : PreservesCoproducts.{j} G) :
    CoproductClosed.{j} (unitIsomorphism a) := by
  intro I N c hc hi
  obtain ⟨hF⟩ := mapCofan_preserves F a.leftAdjoint_preservesColimits c hc
  obtain ⟨hH⟩ := hG (mapCofan F c) hF
  let H := F ⋙ G
  letI instUnit (i : I) : IsIso (a.unit.app (N i)) := hi i
  let p : H.obj c.pt ⟶ c.pt :=
    Cofan.IsColimit.desc hH (fun i => (asIso (a.unit.app (N i))).inv ≫ c.inj i)
  have hp (i : I) : H.map (c.inj i) ≫ p = (asIso (a.unit.app (N i))).inv ≫ c.inj i :=
    Cofan.IsColimit.fac hH _ i
  change IsIso (a.unit.app c.pt)
  refine ⟨⟨p, ?_, ?_⟩⟩
  · apply hc.hom_ext
    rintro ⟨i⟩
    change c.inj i ≫ a.unit.app c.pt ≫ p = c.inj i ≫ 𝟙 _
    have hn := a.unit.naturality (c.inj i)
    change c.inj i ≫ a.unit.app c.pt = a.unit.app (N i) ≫ H.map (c.inj i) at hn
    rw [reassoc_of% hn, hp]
    simp
  · apply hH.hom_ext
    rintro ⟨i⟩
    change H.map (c.inj i) ≫ p ≫ a.unit.app c.pt = H.map (c.inj i) ≫ 𝟙 _
    have hn := a.unit.naturality (c.inj i)
    change c.inj i ≫ a.unit.app c.pt = a.unit.app (N i) ≫ H.map (c.inj i) at hn
    rw [← Category.assoc, hp, Category.assoc, hn]
    simp [← Category.assoc]

end UnitClosure

section NativeLocalization

open DerivedCoproducts (derivedCofan)
open CompactRepresentables (IsCompact LocalizationMapAdditive coproductHomMap)
open RightDGModule (nativeExistingDerivedCoproduct kProjectiveLocalizationEquivalence
  derivedPreadditive derivedLocalization_additive)
open private nonzeroSummandsSmall coproductHomMap_surjective_of_cover
  realizedSum_surjective coproductHomMap_injective coproductHomMap_surjective_of_iso shiftZeroIso
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,max v w,w} k}
variable (h : HomotopyCategoryLaws A)

local instance (C : DGCategoryModel.{u,v',w'} k) :
    Category (HomComplex.homotopyCategory C) := RightDGModule.instCategoryK C
local instance (C : DGCategoryModel.{u,v',w'} k) (h : HomotopyCategoryLaws C) :
    Category (D C h) := derivedCategoryInstance C h

private theorem native_hasCoproducts : HasCoproducts.{max v w} (D A h) := by
  classical
  intro I
  constructor
  intro F
  let N : I → D A h := fun i => F.obj ⟨i⟩
  have hNColim : HasColimit (Discrete.functor N) := by
    let q := Q A h
    have hq := (Localization.Construction.objEquiv (RightDGModule.quasiIsomorphisms A)).surjective
    choose M hM using fun i => hq (N i)
    have hN : (fun i => q.obj (M i)) = N := funext hM
    let b := DG.IndexedSums.nativeSum M
    obtain ⟨hc⟩ := nativeExistingDerivedCoproduct.{u,v,w,max v w} h b
    rw [← hN]
    exact ⟨⟨derivedCofan h b, hc⟩⟩
  exact @hasColimit_of_iso _ _ _ _ _ _ hNColim Discrete.natIsoFunctor

private theorem native_preadditive_unique (S S' : Preadditive (D A h)) : S = S' := by
  letI := S
  letI := native_hasCoproducts.{u,v,w} h
  letI := hasFiniteCoproducts_of_hasCoproducts (C := D A h)
  letI : HasBinaryBiproducts (D A h) := HasBinaryBiproducts.of_hasBinaryCoproducts
  exact Subsingleton.elim _ _

private theorem native_localization_additive (S : Preadditive (D A h)) :
    LocalizationMapAdditive h S := by
  rw [native_preadditive_unique.{u,v,w} h S (derivedPreadditive.{u,v,w} A h)]
  letI := derivedPreadditive.{u,v,w} A h
  intro M N f g
  exact (derivedLocalization_additive.{u,v,w} A h).map_add (f := f) (g := g)

private theorem native_representable_compact (S : Preadditive (D A h)) (a : A.Obj) :
    letI := S
    IsCompact.{j} ((Q A h).obj (representable a)) := by
  classical
  letI : Preadditive (RightDGModule.D A h) := S
  have hadd := native_localization_additive.{u,v,w} h S
  let q := RightDGModule.Q A h
  intro I N c hc
  let Jq := RightDGModule.toHomotopyCategory A ⋙ q
  let e₀ : Jq.obj (SemiFree.cell a 0) ≅ Jq.obj (representable a) :=
    Jq.mapIso (shiftZeroIso (representable a))
  refine ⟨coproductHomMap_injective _ hc, coproductHomMap_surjective_of_iso c e₀ ?_⟩
  let E := kProjectiveLocalizationEquivalence.{u,v,w} A h
  letI : E.inverse.Faithful := E.fullyFaithfulInverse.faithful
  letI : LocallySmall.{max v w} (D A h) :=
    ⟨fun X Y => small_of_injective (f := fun g : X ⟶ Y => E.inverse.map g)
      (fun _ _ h => E.fullyFaithfulInverse.map_injective h)⟩
  let J := {i : I // ¬ IsZero (N i)}
  letI : Small.{max v w} J := nonzeroSummandsSmall hc
  let e := equivShrink J
  let i (x : Shrink J) := (e.symm x).val
  have hi (x : I) (hx : ¬ IsZero (N x)) : ∃ y, i y = x :=
    ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
  letI : q.IsLocalization (RightDGModule.quasiIsomorphisms A) := RightDGModule.Q_isLocalization A h
  letI : q.EssSurj := Localization.essSurj q (RightDGModule.quasiIsomorphisms A)
  let M (x : Shrink J) := q.objPreimage (N (i x))
  let b := DG.IndexedSums.nativeSum M
  obtain ⟨hb⟩ := nativeExistingDerivedCoproduct.{u,v,w,max v w} h b
  exact coproductHomMap_surjective_of_cover _ hc hb i (fun x => q.objObjPreimageIso _) hi
    (realizedSum_surjective.{u,v,w,max v w} h hadd a b)

private theorem native_compact_for_existing_coproducts (S : Preadditive (D A h)) {X : D A h}
    (hx : letI := S; IsCompact.{max v w} X) :
    letI := S
    IsCompact.{j} X := by
  classical
  letI := S
  intro I N c hc
  refine ⟨coproductHomMap_injective _ hc, ?_⟩
  let E := kProjectiveLocalizationEquivalence.{u,v,w} A h
  letI : E.inverse.Faithful := E.fullyFaithfulInverse.faithful
  letI : LocallySmall.{max v w} (D A h) :=
    ⟨fun X Y => small_of_injective (f := fun g : X ⟶ Y => E.inverse.map g)
      (fun _ _ h => E.fullyFaithfulInverse.map_injective h)⟩
  let J := {i : I // ¬ IsZero (N i)}
  letI : Small.{max v w} J := nonzeroSummandsSmall hc
  let e := equivShrink J
  let i (x : Shrink J) := (e.symm x).val
  have hi (x : I) (hx : ¬ IsZero (N x)) : ∃ y, i y = x :=
    ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
  letI := native_hasCoproducts.{u,v,w} h
  let b := colimit.cocone (Discrete.functor (N ∘ i))
  let hb := colimit.isColimit (Discrete.functor (N ∘ i))
  exact coproductHomMap_surjective_of_cover _ hc hb i (fun _ => Iso.refl _) hi (hx b hb).surjective

open private cellDerivedEquiv cellDerivedEquiv_natural
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables

private theorem strict_quasiIso_of_localizedIso {M N : RightDGModuleModel A} (f : M ⟶ N)
    (hf : IsIso ((Q A h).map (homotopyClass f))) :
    Module.quasiIsomorphism f := by
  let S := derivedPreadditive.{u,v,w} A h
  letI : Preadditive (RightDGModule.D A h) := S
  have hadd := native_localization_additive.{u,v,w} h S
  intro a
  apply (quasiIso_iff _).mpr
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let eM := @cellDerivedEquiv.{u,v,w} k _ A a n M h S hadd
  let eN := @cellDerivedEquiv.{u,v,w} k _ A a n N h S hadd
  let qf := asIso ((Q A h).map (homotopyClass f))
  let E := eM.toEquiv.symm.trans ((Iso.refl _).homCongr qf) |>.trans eN.toEquiv
  have he (x : (M.complex a).homology n) : E x = HomologicalComplex.homologyMap (f.app a) n x := by
    have hn := @cellDerivedEquiv_natural.{u,v,w} k _ A a n M h S hadd N f (eM.symm x)
    change eN (eM.symm x ≫ qf.hom) = _
    change eN (eM.symm x ≫ qf.hom) =
      HomologicalComplex.homologyMap (f.app a) n (eM (eM.symm x)) at hn
    rwa [eM.apply_symm_apply] at hn
  exact (funext he) ▸ E.bijective

end NativeLocalization

section Preservation

open CompactRepresentables (IsCompact)
open private nonzeroSummandsSmall from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables

variable {C E : Type*} [Category* C] [Category* E] [Preadditive C] [Preadditive E]

private theorem preservesCoproducts_of_compact_tests {F : C ⥤ E} {G : E ⥤ C}
    (a : F ⊣ G) [G.Additive] (hE : LocallySmall.{v} E) (hC : HasCoproducts.{v} C)
    {ι : Type*} (P : ι → C)
    (detect : ∀ {X Y : C} (f : X ⟶ Y),
      (∀ i, Function.Bijective (fun g : P i ⟶ X => g ≫ f)) → IsIso f)
    (h₁ : ∀ i, IsCompact.{j} (P i)) (h₂ : ∀ i, IsCompact.{j} (F.obj (P i))) :
    PreservesCoproducts.{j} G := by
  letI := hE
  letI := hC
  intro I N c hc
  let J := {i : I // ¬ IsZero (N i)}
  let J' := {i : I // ¬ IsZero (G.obj (N i))}
  letI : Small.{v} J := nonzeroSummandsSmall hc
  let e (i : J') : J := ⟨i.val, fun hz => i.property (G.map_isZero hz)⟩
  letI : Small.{v} J' := small_of_injective (f := e) (fun _ _ h => Subtype.ext (congrArg (fun (i : J) => i.val) h))
  obtain ⟨b, ⟨hb⟩⟩ := exists_cofan_of_small_nonzero_summands (fun i => G.obj (N i))
    (fun {K} Y => ⟨colimit.cocone (Discrete.functor Y), ⟨colimit.isColimit (Discrete.functor Y)⟩⟩)
  exact colimit_of_tests P detect (mapCofan G c) b hb h₁
    (fun i => (adjoint_coproductHomMap a (P i) c).mp (h₂ i c hc))

end Preservation

section MoritaArgument

open CompactGenerators (ShiftedRepresentablesDetectZero)
open CompactRepresentables (IsCompact)
open RightDGModule (kProjectiveLocalizationEquivalence)
open private detectsZero localizedAcyclicIsZero generationOfStrictTriangles
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactGenerators
open private cellDerivedEquiv from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables

variable {k : Type u} [CommRing k]
variable {A : DGCategoryModel.{u,max v w z,w} k} {B : DGCategoryModel.{u,max v w z,z} k}
variable {T : bimodule A B} (m : SignedModels.{u,v,w,z} T)
variable {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
variable (d : DerivedAdjunctionData.{u,v,w,z} m.tensor m.hom hA hB)

local instance (C : DGCategoryModel.{u,v',w'} k) :
    Category (HomComplex.homotopyCategory C) := RightDGModule.instCategoryK C
local instance (C : DGCategoryModel.{u,v',w'} k) (h : HomotopyCategoryLaws C) :
    Category (D C h) := derivedCategoryInstance C h

local notation "QA" => Q A hA
local notation "QB" => Q B hB

set_option hygiene false in
local notation "F" => DerivedAdjunctionData.tensor.{u,v,w,z} d
set_option hygiene false in
local notation "G" => (DerivedAdjunctionData.hom.{u,v,w,z} d).derived

set_option maxHeartbeats 750000 in
private theorem morita_hom_preserves
    (ht : DerivedAdjunctionData.ComputesRepresentatives.{u,v,w,z} d)
    (hex : DerivedAdjunctionData.IsExact.{u,v,w,z} d)
    (SB : Preadditive (D B hB))
    (hcomp : letI := SB; ∀ a, IsCompact.{max v w z} ((QB).obj (T.obj a))) :
    PreservesCoproducts.{j} G := by
  obtain ⟨cA, cB, _, _, _, _, fS, gS, hf, hg, _, _, _⟩ := hex
  letI := cA.addD
  letI := cB.addD
  letI := cA.shiftD
  letI := cB.shiftD
  letI := cA.zeroD
  letI := cB.zeroD
  letI := cA.addShiftD
  letI := cB.addShiftD
  letI := cA.trianglesD
  letI := cB.trianglesD
  letI := fS
  letI := gS
  letI := hf
  letI := hg
  have hCA := native_hasCoproducts.{u,max v z,w} hA
  let EB := kProjectiveLocalizationEquivalence.{u,max v w,z} B hB
  letI : EB.inverse.Faithful := EB.fullyFaithfulInverse.faithful
  have hEB : LocallySmall.{max v w z} (D B hB) :=
    ⟨fun X Y => small_of_injective (f := fun g : X ⟶ Y => EB.inverse.map g)
      (fun _ _ h => EB.fullyFaithfulInverse.map_injective h)⟩
  let H (a : A.Obj) := (QA).obj (representable (A := A) a)
  let P (i : A.Obj × ℤ) := (shiftFunctor (D A hA) i.2).obj (H i.1)
  have hadd := native_localization_additive.{u,max v z,w} hA cA.addD
  have hdetect (X : D A hA) (hs : ∀ i, Subsingleton (P i ⟶ X)) : IsZero X := by
    obtain ⟨M, rfl⟩ := (Localization.Construction.objEquiv
      (RightDGModule.quasiIsomorphisms A)).surjective X
    have hM : Module.acyclic M := by
      intro a n
      have e := cA.onShift (representable (A := A) a) (-n)
      have hsub : Subsingleton ((QA).obj (SemiFree.cell a n) ⟶ (QA).obj M) :=
        (e.homCongr (Iso.refl _)).subsingleton_congr.mpr (hs (a, -n))
      letI : Preadditive (RightDGModule.D A hA) := cA.addD
      have e' := @cellDerivedEquiv.{u,max v z,w} k _ A a n M hA cA.addD hadd
      exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
        (ModuleCat.isZero_iff_subsingleton.mpr (e'.toEquiv.subsingleton_congr.mp hsub))
    exact localizedAcyclicIsZero.{u,max v z,w} hA hadd _ hM
  have hshift (i : A.Obj × ℤ) :
      ∃ i', Nonempty (P i ≅ (shiftFunctor (D A hA) (1 : ℤ)).obj (P i')) :=
    ⟨(i.1, i.2 - 1), ⟨(shiftFunctorAdd' (D A hA) (i.2 - 1) 1 i.2 (by omega)).app (H i.1)⟩⟩
  have h₁ (i : A.Obj × ℤ) : IsCompact.{j} (P i) :=
    compact_shift (native_representable_compact.{u,max v z,w,j} hA cA.addD i.1) i.2
  have h₂ (i : A.Obj × ℤ) : IsCompact.{j} ((F).obj (P i)) := by
    have eS : SB = cB.addD := native_preadditive_unique.{u,max v w,z} hB _ _
    have hcomp' : letI := cB.addD; ∀ a, IsCompact.{max v w z} ((QB).obj (T.obj a)) := by
      rw [← eS]
      exact hcomp
    have hc : IsCompact.{max v w z} ((QB).obj (T.obj i.1)) := hcomp' i.1
    have hc' : IsCompact.{j} ((QB).obj (T.obj i.1)) :=
      native_compact_for_existing_coproducts.{u,max v w,z,j} hB cB.addD hc
    have hR : isKProjective (representable (A := A) i.1) := representable_kProjective i.1
    obtain ⟨e, _, _⟩ := ht.2 i.1
    let eR := DerivedAdjunctionData.onProjective.{u,v,w,z} d _ hR ≪≫
      (RightDGModule.toHomotopyCategory B ⋙ QB).mapIso e
    let eF : (F).obj (P i) ≅ (shiftFunctor (D B hB) i.2).obj ((QB).obj (T.obj i.1)) :=
      ((F).commShiftIso i.2).app (H i.1) ≪≫ (shiftFunctor (D B hB) i.2).mapIso eR
    have hshifted : IsCompact.{j} ((shiftFunctor (D B hB) i.2).obj ((QB).obj (T.obj i.1))) :=
      compact_shift (C := D B hB) hc' i.2
    intro I N c hc
    exact compact_iso (C := D B hB) eF.symm hshifted c hc
  exact @preservesCoproducts_of_compact_tests (D A hA) (D B hB) _ _ cA.addD cB.addD
    (F) (G) (DerivedAdjunctionData.adjunction.{u,v,w,z} d) (by infer_instance) hEB hCA _ P
    (fun f ht => isIso_of_compact_tests P hdetect hshift f ht) h₁ h₂

set_option maxHeartbeats 750000 in
private theorem units_on_all_objects
    (hunit : ComputesRepresentableUnit.{u,v,w,z} d)
    (hex : DerivedAdjunctionData.IsExact.{u,v,w,z} d)
    (hcoprod : PreservesCoproducts.{max v w z} G)
    (hqi : MorphismQuasiIsomorphisms.{u,v,w,z} T) :
    ∀ X : D A hA, IsIso ((DerivedAdjunctionData.adjunction.{u,v,w,z} d).unit.app X) := by
  let a : (F) ⊣ (G) := DerivedAdjunctionData.adjunction.{u,v,w,z} d
  let P := unitIsomorphism a
  obtain ⟨cA, cB, _, _, _, _, fS, gS, hf, hg, ha, _, _⟩ := hex
  letI := cA.addD
  letI := cB.addD
  letI := cA.shiftD
  letI := cB.shiftD
  letI := cA.zeroD
  letI := cB.zeroD
  letI := cA.addShiftD
  letI := cB.addShiftD
  letI := cA.trianglesD
  letI := cB.trianglesD
  letI := fS
  letI := gS
  letI := hf
  letI := hg
  let hClosed : P.IsClosedUnderIsomorphisms := unitIsomorphism_closed a
  let hTri : P.IsTriangulated :=
    @unitIsomorphism_triangulated (D A hA) (D B hB) _ _ (F) (G) a
      cA.addD cB.addD cA.zeroD cB.zeroD cA.shiftD cB.shiftD cA.addShiftD cB.addShiftD
      cA.trianglesD cB.trianglesD fS gS hf hg ha
  letI := cA.shiftK
  letI := cA.quotientShift
  have hrep (b : A.Obj) : P ((QA).obj (representable (A := A) b)) := by
    let R := representable (A := A) b
    obtain ⟨hp, e, _, he, hη⟩ := hunit b
    let G₀ := ordinaryHom.{u,v,w,z} m.hom
    let η := m.adjunction.unit.app R ≫ G₀.map e.hom
    have hηq : Module.quasiIsomorphism η := by
      intro x
      let φ := (m.hom.objectwise (T.obj b) x).inv
      have hi : QuasiIso (η.app x ≫ φ) := by
        rw [show η.app x ≫ φ = toComplexHom (T.map x b) from he x]
        exact hqi x b
      exact (quasiIso_iff_comp_right _ φ).mp hi
    let f := DerivedAdjunctionData.onProjective.{u,v,w,z} d R hp
    let g := (RightDGModule.toHomotopyCategory B ⋙ QB).mapIso e
    let r := DerivedAdjunctionData.onInput.{u,v,w,z} d (T.obj b)
    let p := ((G).mapIso (f ≪≫ g) ≪≫ r).hom
    have hp' : IsIso p := inferInstance
    let qη := replacementIso hA η hηq
    have hEq : a.unit.app ((QA).obj R) ≫ p = qη.hom := by
      change _ = (QA).map (homotopyClass η)
      exact hη
    have hIso : IsIso (a.unit.app ((QA).obj R) ≫ p) := by
      rw [hEq]
      exact qη.isIso_hom
    exact IsIso.of_isIso_comp_right _ p
  exact @generationOfStrictTriangles.{u,max v z,w} k _ A hA
    cA.shiftK cA.shiftD cA.addD cA.zeroD cA.addShiftD cA.trianglesD cA.quotientShift
    cA.shiftObj cA.localizedConeTriangles.1
    (@localizedAcyclicIsZero.{u,max v z,w} k _ A hA cA.addD
      (native_localization_additive.{u,max v z,w} hA cA.addD))
    P hClosed hTri
    (unitIsomorphism_coproducts a hcoprod) hrep

end MoritaArgument

/-- Conditional form of the Morita unit argument at one common bound. -/
theorem moritaUnitAt_conditional
    (_premise1 : CompactFiniteCells.AmbientCompactnessComparison.{u,v,w,v,j})
    (_premise2 : CompactFiniteCells.NativeCompactFiniteCells.{u,v,w,j})
    (_premise3 : CompactFiniteCells.NativeCompactnessComparison.{u,v,w,j})
    (_premise4 : CompactFiniteCells.OriginalCompactFiniteCells.{u,v,w,j,v})
    (_premise5 : DerivedBimoduleAdjunction.AdequateNativeProjectivityTransition.{u,v,w,v,z,v})
    (_premise6 : DerivedBimoduleAdjunction.AmbientDerivedAdjunction.{u,v,w,v,z,v})
    (_premise7 : DerivedBimoduleAdjunction.AmbientDerivedAdjunctionComparison.{u,v,w,v,z,v,j})
    (_premise8 : DerivedBimoduleAdjunction.AmbientExactDerivedAdjunction.{u,v,w,v,z,v})
    (_premise9 : DerivedBimoduleAdjunction.AmbientProjectivityTransition.{u,v,w,v,z,v,j})
    (_premise10 : DerivedBimoduleAdjunction.DerivedAdjunctionAt.{u,v,w,z})
    (_premise11 : DerivedBimoduleAdjunction.ExactDerivedAdjunctionAt.{u,v,w,z})
    (_premise12 : DerivedBimoduleAdjunction.HomShiftConeComparison.{u,v,w,z})
    (_premise13 : DerivedBimoduleAdjunction.NativeDerivedAdjunctionCompatibility.{u,v,w,z})
    (_premise14 : DerivedBimoduleAdjunction.NativeHomDescent.{u,v,w,v,z})
    (_premise15 : DerivedBimoduleAdjunction.NativeHomPreservesQuasiIsomorphisms.{u,v,w,v,z})
    (_premise16 : DerivedBimoduleAdjunction.TensorPreservesKProjectives.{u,v,w,z}) :
    MoritaUnitAt.{u,v,w,z,j} := by
  intro k _ A B T m hA hB S d _ hd ht hex _ hc hqi
  have hu := computesRepresentableUnit.{u,v,w,z} m d hd ht
  let G := (DerivedAdjunctionData.hom.{u,v,w,z} d).derived
  have hp : PreservesCoproducts.{j} G := morita_hom_preserves.{u,v,w,z,j} m d ht hex S hc
  have hp' : PreservesCoproducts.{max v w z} G :=
    morita_hom_preserves.{u,v,w,z,max v w z} m d ht hex S hc
  exact ⟨hp, hu, units_on_all_objects.{u,v,w,z} m d hu hex hp' hqi⟩

section FiniteCells

open scoped DirectSum
open IndexedSemiFree (Presentation StrictSum summand)
open CellReindex (allCells cellToModule cellToSuccessor GradedDecomposition)
open DerivedCoproducts (derivedCofan)
open CompactRepresentables (IsCompact coproductHomMap)
open RightDGModule (nativeExistingDerivedCoproduct)
open private coproductHomMap_injective coproductHomMap_surjective_of_cover coproductHomMap_of
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {P : RightDGModuleModel A} {I : Type j}
variable {N : I → RightDGModuleModel A} {U : RightDGModuleModel A}

/-- Coordinate projection of a realized strict sum. -/
private def sumProjection (b : StrictSum N U) (i : I) : U ⟶ N i where
  app a :=
    { f := fun n => ModuleCat.ofHom
        ((DFinsupp.lapply i).comp (b.coordinates a n).toLinearMap)
      comm' := by
        intro n m h
        obtain rfl : n + 1 = m := h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        exact fun x => (b.coordinate_d a n x i).symm }
  comm_act := fun m n q h x r => b.coordinate_act m n q h x r i

/-- The underlying graded module is generated by the named cells. -/
private theorem strictMap_eq_zero_on_generators
    {M L : RightDGModuleModel A} (F : Presentation.{u,v,w,v'} M)
    (V : GradedDecomposition F) (f : M ⟶ L)
    (h : ∀ (l : ℕ) (s : F.index l),
      (f.app ((F.family l).object s)).f ((F.family l).degree s)
        (((F.into (l+1)).app ((F.family l).object s)).f ((F.family l).degree s)
          ((F.extension l).generator s)) = 0) :
    f = 0 := by
  letI : DecidableEq (Σ l, F.index l) := Classical.decEq _
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  have hh : ((f.app a).f n).hom.comp (V.coordinates a n).symm.toLinearMap = 0 := by
    apply DirectSum.linearMap_ext
    intro c
    apply LinearMap.ext
    intro x
    obtain ⟨l, s⟩ := c
    let C := F.family l
    let m := n + -C.degree s
    have hm : C.degree s + m = n := by dsimp [m]; omega
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    change (f.app a).f n ((V.coordinates a n).symm (summand (allCells F) a n ⟨l,s⟩ x)) = 0
    rw [← V.cell ⟨l,s⟩ a n x, LinearEquiv.symm_apply_apply]
    have hx := DG.CellReindex.cellMapFormula.{u,v,w,v'} F l s a m n hm x
    change cellToSuccessor F l s a n x =
      (F.stage (l+1)).act (C.degree s) m n hm ((F.extension l).generator s) x at hx
    change (f.app a).f n (((F.into (l+1)).app a).f n (cellToSuccessor F l s a n x)) = 0
    rw [hx, (F.into (l+1)).comm_act, f.comm_act, h l s, map_zero, LinearMap.zero_apply]
  apply LinearMap.ext
  intro x
  have h' := LinearMap.congr_fun hh (V.coordinates a n x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.zero_apply] at h'
  exact h'

private def cycleValue (a : A.Obj) (n : ℤ) (x : (P.complex a).X n) :
    Basic.cyclesZero (HomComplex.homComplex P U) →ₗ[k] (U.complex a).X n where
  toFun q := component q.val a n n (add_zero n) x
  map_add' q q' := by
    change ((q.val.val a + q'.val.val a).v n n (add_zero n)) x = _
    rw [CochainComplex.HomComplex.Cochain.add_v]
    rfl
  map_smul' c q := by
    change ((c • q.val.val a).v n n (add_zero n)) x = _
    rw [CochainComplex.HomComplex.Cochain.smul_v]
    rfl

private theorem finiteCell_factorization
    (F : Presentation.{u,v,w,v'} P) [Finite (Σ l, F.index l)]
    (b : StrictSum N U) (f : P ⟶ U) :
    ∃ E : Finset I, RightDGModule.strictCycle f =
      ∑ i ∈ E, RightDGModule.strictCycle ((f ≫ sumProjection b i) ≫ b.inclusion i) := by
  classical
  obtain ⟨V, _⟩ := DG.CellReindex.directSumDecomposition.{u,v,w,v'} F
  letI : Fintype (Σ l, F.index l) := Fintype.ofFinite _
  let E : Finset I := Finset.univ.biUnion fun (s : Σ l, F.index l) =>
    let C := F.family s.1
    let a := C.object s.2
    let n := C.degree s.2
    (b.coordinates a n ((f.app a).f n (((F.into (s.1+1)).app a).f n
      ((F.extension s.1).generator s.2)))).support
  have hzero (i : I) (hi : i ∉ E) : f ≫ sumProjection b i = 0 := by
    apply strictMap_eq_zero_on_generators F V
    intro l s
    apply DFinsupp.notMem_support_iff.mp
    exact fun hs => hi (Finset.mem_biUnion.mpr ⟨⟨l, s⟩, Finset.mem_univ _, hs⟩)
  refine ⟨E, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext a
  apply CochainComplex.HomComplex.Cochain.ext₀
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (b.coordinates a n).injective
  let ψ := (b.coordinates a n).toLinearMap.comp (cycleValue (U := U) a n x)
  change ψ (RightDGModule.strictCycle f) =
    ψ (∑ i ∈ E, RightDGModule.strictCycle ((f ≫ sumProjection b i) ≫ b.inclusion i))
  rw [map_sum]
  have hval (g : P ⟶ U) : ψ (RightDGModule.strictCycle g) =
      b.coordinates a n ((g.app a).f n x) := by
    change b.coordinates a n (((RightDGModule.strictCycle g).val.val a).v n n (add_zero n) x) = _
    rw [show (RightDGModule.strictCycle g).val.val a =
      CochainComplex.HomComplex.Cochain.ofHom (g.app a) from rfl,
      CochainComplex.HomComplex.Cochain.ofHom_v]
  simp only [hval]
  apply DFinsupp.ext
  intro i
  rw [DFinsupp.finsetSum_apply]
  have hterm (l : I) : (b.coordinates a n ((((f ≫ sumProjection b l) ≫ b.inclusion l).app a).f n x)) i =
      (summand N a n l (b.coordinates a n ((f.app a).f n x) l)) i :=
    congrArg (fun y => y i) (b.coordinate_inclusion l a n (b.coordinates a n ((f.app a).f n x) l))
  simp only [hterm]
  rw [Finset.sum_eq_single i]
  · simp only [summand, DirectSum.lof_apply]
  · intro l _ hli
    rw [summand, DirectSum.lof_eq_of]
    exact DirectSum.of_eq_of_ne l i _ (Ne.symm hli)
  · intro hi
    have he := congrArg (fun g : P ⟶ N i => (g.app a).f n x) (hzero i hi)
    change b.coordinates a n ((f.app a).f n x) i = 0 at he
    simp only [he, map_zero, DFinsupp.zero_apply]

section Adequate

variable {B : DGCategoryModel.{u,max v w,w} k} (h : HomotopyCategoryLaws B)
variable {M : RightDGModuleModel B}

local instance (C : DGCategoryModel.{u,v',w'} k) :
    Category (HomComplex.homotopyCategory C) := RightDGModule.instCategoryK C
local instance (C : DGCategoryModel.{u,v',w'} k) (h : HomotopyCategoryLaws C) :
    Category (D C h) := derivedCategoryInstance C h

private theorem native_finiteCell_compact (S : Preadditive (D B h))
    (hm : IndexedSemiFree.finiteCell M) :
    letI := S
    IsCompact.{max v w} ((Q B h).obj M) := by
  classical
  letI : Preadditive (D B h) := S
  letI : Preadditive ((Derived.quasiIsomorphisms B).Localization) := S
  obtain ⟨F, hF⟩ := hm
  letI := hF
  have hp : isKProjective M := RightDGModule.IsSemiFree.isKProjective ⟨F⟩
  let q : RightDGModule.K B ⥤ D B h := Q B h
  intro J Y c hc
  have hq := (Localization.Construction.objEquiv (RightDGModule.quasiIsomorphisms B)).surjective
  choose N hN using fun i => hq (Y i)
  let U := RightDGModule.directSum N
  let b : StrictSum N U := DG.IndexedSums.nativeSum N
  obtain ⟨hb⟩ := nativeExistingDerivedCoproduct.{u,v,w,max v w} h b
  let d : Cofan (fun i => q.obj (N i)) := derivedCofan h b
  have hd : IsColimit d := hb
  refine ⟨coproductHomMap_injective _ hc,
    coproductHomMap_surjective_of_cover _ hc hd id (fun i => eqToIso (hN i))
      (fun i _ => ⟨i, rfl⟩) ?_⟩
  intro g
  obtain ⟨x, hx⟩ := (RightDGModule.IsKProjective.Q_map_bijective h hp).surjective g
  obtain ⟨f, rfl⟩ := RightDGModule.homotopyClass_surjective x
  obtain ⟨E, hE⟩ := finiteCell_factorization F b f
  let fᵢ (i : J) := f ≫ sumProjection b i
  refine ⟨∑ i ∈ E, DirectSum.of (fun i => q.obj M ⟶ q.obj (N i)) i
    (q.map (homotopyClass (fᵢ i))), ?_⟩
  change coproductHomMap (q.obj M) d
    (∑ i ∈ E, DirectSum.of _ i (q.map (homotopyClass (fᵢ i)))) = g
  rw [map_sum]
  have hclass (i : J) : coproductHomMap (q.obj M) d
      (DirectSum.of (fun i => q.obj M ⟶ q.obj (N i)) i (q.map (homotopyClass (fᵢ i)))) =
      q.map (homotopyClass (fᵢ i ≫ b.inclusion i)) := by
    rw [coproductHomMap_of]
    exact ((RightDGModule.toHomotopyCategory B ⋙ q).map_comp (fᵢ i) (b.inclusion i)).symm
  simp only [hclass]
  rw [← hx]
  letI : Preadditive (RightDGModule.K B) := RightDGModule.homotopyPreadditive
  have hadd := native_localization_additive.{u,v,w} h S
  letI : q.Additive := ⟨fun {X Y} {f₁ f₂} => hadd X Y f₁ f₂⟩
  let L := (q.mapAddHom (X := M) (Y := U)).comp
    (Submodule.mkQ (Basic.boundariesZero (HomComplex.homComplex M U))).toAddMonoidHom
  have hsum := congrArg L hE
  rw [map_sum] at hsum
  exact hsum.symm

set_option maxHeartbeats 500000 in
private theorem native_compact_shift (S : Preadditive (D B h))
    (c : ConeLocalization B h) {P : RightDGModuleModel B}
    (hP : CompactFiniteCells.CompactAt.{u,w,j,max v w} h S ((Q B h).obj P)) (n : ℤ) :
    CompactFiniteCells.CompactAt.{u,w,j,max v w} h S ((Q B h).obj (ShiftCone.shift P n)) := by
  have eS := native_preadditive_unique.{u,v,w} h S c.addD
  rw [eS] at hP ⊢
  letI := c.addD
  letI := c.shiftD
  letI := c.addShiftD
  have hs : IsCompact.{j} ((shiftFunctor (D B h) n).obj ((Q B h).obj P)) :=
    compact_shift (C := D B h) hP n
  intro I F b hb
  exact @compact_iso (D B h) _ c.addD _ _ (c.onShift P n).symm hs I F b hb

end Adequate

end FiniteCells

section CompactnessComparison

open scoped DirectSum
open CompactFiniteCells (CompactAt)
open CompactRepresentables (coproductHomMap IsCompact)
open private coproductHomMap_of coproductHomMap_injective coproductHomMap_surjective_of_cover
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables

section Cofan

variable {C E : Type*} [Category* C] [Category* E]
variable {I : Type j} {X : I → C} {Y : I → E}

private theorem colimit_map_of_represented_cofan (F : C ⥤ E)
    (c : Cofan X) (d : Cofan Y) (hd : IsColimit d)
    (e : F.obj c.pt ≅ d.pt) (es : ∀ i, F.obj (X i) ≅ Y i)
    (he : ∀ i, F.map (c.inj i) ≫ e.hom = (es i).hom ≫ d.inj i) :
    Nonempty (IsColimit (mapCofan F c)) := by
  let α : Discrete.functor (fun i => F.obj (X i)) ≅ Discrete.functor Y :=
    Discrete.natIso fun i => es i.as
  let d' : Cofan (fun i => F.obj (X i)) := (Cocone.precompose α.hom).obj d
  let hd' : IsColimit d' := (IsColimit.precomposeHomEquiv α d).symm hd
  exact ⟨hd'.ofIsoColimit (Cofan.ext (c₁ := mapCofan F c) (c₂ := d') e he).symm⟩

variable [Preadditive C] [Preadditive E]

private theorem coproductHomMap_surjective_of_fullyFaithful (F : C ⥤ E)
    (ff : F.FullyFaithful) [F.Additive] (P : C) (c : Cofan X)
    (h : Function.Surjective (coproductHomMap (F.obj P) (mapCofan F c))) :
    Function.Surjective (coproductHomMap P c) := by
  classical
  let f (i : I) : (P ⟶ X i) →+ (F.obj P ⟶ F.obj (X i)) := F.mapAddHom
  let e : (P ⟶ c.pt) →+ (F.obj P ⟶ F.obj c.pt) := F.mapAddHom
  have hs : Function.Surjective (DirectSum.map f) :=
    (DirectSum.map_surjective _).mpr fun i => (ff.homEquiv (X := P) (Y := X i)).surjective
  have he : e.comp (coproductHomMap P c) =
      (coproductHomMap (F.obj P) (mapCofan F c)).comp (DirectSum.map f) := by
    apply DirectSum.addHom_ext
    intro i x
    change e (coproductHomMap P c (DirectSum.of _ i x)) =
      coproductHomMap (F.obj P) (mapCofan F c) (DirectSum.map f (DirectSum.of _ i x))
    rw [DirectSum.map_of, coproductHomMap_of, coproductHomMap_of]
    exact F.map_comp x (c.inj i)
  intro g
  obtain ⟨u, hu⟩ := (h.comp hs) (e g)
  refine ⟨u, ff.map_injective ?_⟩
  change (e.comp (coproductHomMap P c)) u = e g
  rw [he]
  exact hu

private theorem compact_retract {X Y : C} (r : Retract X Y) (hy : IsCompact.{j} Y) :
    IsCompact.{j} X := by
  classical
  intro I N c hc
  refine ⟨coproductHomMap_injective _ hc, ?_⟩
  let f (i : I) := Preadditive.leftComp (N i) r.i
  let g := Preadditive.leftComp c.pt r.i
  have h : g.comp (coproductHomMap Y c) = (coproductHomMap X c).comp (DirectSum.map f) := by
    apply DirectSum.addHom_ext
    intro i x
    change r.i ≫ coproductHomMap Y c (DirectSum.of _ i x) =
      coproductHomMap X c (DirectSum.map f (DirectSum.of _ i x))
    rw [DirectSum.map_of, coproductHomMap_of, coproductHomMap_of]
    exact (Category.assoc _ _ _).symm
  intro b
  obtain ⟨x, hx⟩ := (hy c hc).surjective (r.r ≫ b)
  refine ⟨DirectSum.map f x, ?_⟩
  change ((coproductHomMap X c).comp (DirectSum.map f)) x = b
  rw [← h]
  change r.i ≫ coproductHomMap Y c x = b
  rw [hx, r.retract_assoc]

end Cofan

section Lift

open AmbientDerived (category)
open DerivedCoefficientLift (Descent strictTransition)
open DerivedCoproducts (derivedCofan)
open IndexedSemiFree (StrictSum)
open RightDGModule (nativeExistingDerivedCoproduct)
open private transitionSum from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift
open private transition_inclusion from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoproducts

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

set_option quotPrecheck false
set_option hygiene false in
local notation "A₀" => category.{u,v,w,t} A
set_option hygiene false in
local notation "A₁" => category.{u,v,w,max t s} A
set_option hygiene false in
local notation "L" => strictTransition.{u,v,w,t,s} A

variable {h : HomotopyCategoryLaws A₀} {h' : HomotopyCategoryLaws A₁}

local instance (C : DGCategoryModel.{u,v',w'} k) :
    Category (HomComplex.homotopyCategory C) := RightDGModule.instCategoryK C
local instance (C : DGCategoryModel.{u,v',w'} k) (h : HomotopyCategoryLaws C) :
    Category (D C h) := derivedCategoryInstance C h

set_option maxHeartbeats 650000 in
/-- The coefficient transition reflects compactness at the lower bound.
The proof uses fully faithful maps and coproducts of represented modules. -/
private theorem compactness_reflects
    (d : Descent h h' L) (ff : d.D.FullyFaithful)
    (S : Preadditive (D A₀ h)) (S' : Preadditive (D A₁ h'))
    {P : D A₀ h}
    (hc : CompactAt.{u,w,max v w t s,max v w t s} h' S' (d.D.obj P)) :
    CompactAt.{u,w,max v w t,max v w t} h S P := by
  classical
  letI : Preadditive (D A₁ h') := S'
  letI : Preadditive (D A₀ h) := S
  have hd : d.D.Additive := by
    have e := native_preadditive_unique.{u,max v t,w} h S (Preadditive.ofFullyFaithful ff)
    change @Functor.Additive _ _ _ _ S S' d.D
    rw [e]
    exact ff.additive_ofFullyFaithful
  intro I N c hc'
  have hq := (Localization.Construction.objEquiv (RightDGModule.quasiIsomorphisms A₀)).surjective
  choose M hM using fun i => hq (N i)
  let b := DG.IndexedSums.nativeSum M
  let b' := transitionSum.{u,v,w,t,s,max v w t} b
  obtain ⟨hb⟩ := nativeExistingDerivedCoproduct.{u,max v t,w,max v w t} h b
  obtain ⟨hb'⟩ := nativeExistingDerivedCoproduct.{u,max v t s,w,max v w t} h' b'
  obtain ⟨hmap⟩ := colimit_map_of_represented_cofan d.D (derivedCofan h b) (derivedCofan h' b') hb'
    (d.representedIso _) (fun i => d.representedIso (M i))
    (fun i => transition_inclusion d b b' (fun _ => rfl) i)
  have hcompact : IsCompact.{max v w t} (d.D.obj P) :=
    native_compact_for_existing_coproducts.{u,max v t s,w,max v w t} h' S' hc
  refine ⟨coproductHomMap_injective _ hc', coproductHomMap_surjective_of_cover _
    hc' hb id (fun i => eqToIso (hM i)) (fun i _ => ⟨i, rfl⟩) ?_⟩
  exact coproductHomMap_surjective_of_fullyFaithful d.D ff P (derivedCofan h b)
    (hcompact _ hmap).surjective

end Lift

end CompactnessComparison

section LargerCoproduct

open AmbientDerived (category)
open DerivedCoefficientLift (Descent strictTransition)
open DerivedCoproducts (derivedCofan)
open RightDGModule (nativeExistingDerivedCoproduct)

variable {k : Type u} [CommRing k]
variable {A : DGCategoryModel.{u,vA,w} k} {B : DGCategoryModel.{u,v,z} k}
variable {T : bimodule A B}

set_option quotPrecheck false
set_option hygiene false in
local notation "A₀" => category.{u,vA,w,max v z t} A
set_option hygiene false in
local notation "B₀" => category.{u,v,z,max vA w t} B
set_option hygiene false in
local notation "A₁" => category.{u,vA,w,max v z t s} A
set_option hygiene false in
local notation "B₁" => category.{u,v,z,max vA w t s} B
set_option hygiene false in
local notation "U" => strictTransition.{u,vA,w,max v z t,s} A
set_option hygiene false in
local notation "V" => strictTransition.{u,v,z,max vA w t,s} B

variable {m : AmbientSignedModels.{u,v,w,vA,z,t} T}
variable {m' : AmbientSignedModels.{u,v,w,vA,z,max t s} T}
variable {hA : HomotopyCategoryLaws A₀} {hB : HomotopyCategoryLaws B₀}
variable {hA' : HomotopyCategoryLaws A₁} {hB' : HomotopyCategoryLaws B₁}
variable {d : DerivedAdjunctionData.{u,max vA v t,w,z} m.models.tensor m.models.hom hA hB}
variable {d' : DerivedAdjunctionData.{u,max vA v t s,w,z} m'.models.tensor m'.models.hom hA' hB'}

local instance (C : DGCategoryModel.{u,v',w'} k) :
    Category (HomComplex.homotopyCategory C) := RightDGModule.instCategoryK C
local instance (C : DGCategoryModel.{u,v',w'} k) (h : HomotopyCategoryLaws C) :
    Category (D C h) := derivedCategoryInstance C h

set_option hygiene false in
local notation "G₀" => (DerivedAdjunctionData.hom.{u,max vA v t,w,z} d).derived
set_option hygiene false in
local notation "G₁" => (DerivedAdjunctionData.hom.{u,max vA v t s,w,z} d').derived

set_option maxHeartbeats 650000 in
private theorem largerCoproducts_on_represented_inputs
    (dI : Descent hA hA' U) (dJ : Descent hB hB' V)
    (ed : AdjunctionComparison
      (DerivedAdjunctionData.adjunction.{u,max vA v t,w,z} d)
      (DerivedAdjunctionData.adjunction.{u,max vA v t s,w,z} d') dI.D dJ.D)
    (preserves : PreservesCoproducts.{s} G₁) :
    TransitionCoproducts.{u,v,w,vA,z,t,s} dI dJ ed := by
  intro I N
  let F (i : I) := (V).obj (N i)
  let b := DG.IndexedSums.sumRealization F (fun _ _ => small_self _)
  obtain ⟨hc⟩ := nativeExistingDerivedCoproduct.{u,max vA v w t s,z,s} hB' b
  obtain ⟨hb⟩ := preserves (derivedCofan hB' b) hc
  refine ⟨_, b, ⟨hc⟩, hb, ?_⟩
  intro M f
  let q := Q B₀ hB
  let α (i : I) := (dJ.representedIso (N i)).inv
  let r₁ (i : I) := (G₁).map (α i ≫ dJ.D.map (f i))
  let r₂ (i : I) := (G₁).map (α i) ≫ ed.hom.inv.app (q.obj (N i)) ≫ dI.D.map ((G₀).map (f i))
  change Cofan.IsColimit.desc hb r₁ ≫ ed.hom.inv.app (q.obj M) = Cofan.IsColimit.desc hb r₂
  apply hb.hom_ext
  rintro ⟨i⟩
  change (mapCofan (G₁) (derivedCofan hB' b)).inj i ≫
      Cofan.IsColimit.desc hb r₁ ≫ ed.hom.inv.app (q.obj M) =
    (mapCofan (G₁) (derivedCofan hB' b)).inj i ≫ Cofan.IsColimit.desc hb r₂
  rw [← Category.assoc, Cofan.IsColimit.fac, Cofan.IsColimit.fac]
  have hn := ed.hom.inv.naturality (f i)
  change (G₁).map (dJ.D.map (f i)) ≫ ed.hom.inv.app (q.obj M) =
    ed.hom.inv.app (q.obj (N i)) ≫ dI.D.map ((G₀).map (f i)) at hn
  dsimp [r₁, r₂]
  rw [Functor.map_comp, Category.assoc, hn]

open CompactFiniteCells (CompactAt AmbientCompactnessComparison)
open CompactRepresentables (IsCompact LocalizationMapAdditive)
open private inputIso from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift

set_option hygiene false in
local notation "QA₀" => Q A₀ hA
set_option hygiene false in
local notation "QA₁" => Q A₁ hA'
set_option hygiene false in
local notation "QB₀" => Q B₀ hB
set_option hygiene false in
local notation "QB₁" => Q B₁ hB'
set_option hygiene false in
local notation "adj₀" => DerivedAdjunctionData.adjunction.{u,max vA v t,w,z} d
set_option hygiene false in
local notation "adj₁" => DerivedAdjunctionData.adjunction.{u,max vA v t s,w,z} d'

set_option maxHeartbeats 550000 in
private theorem units_on_upper_representables
    (dI : Descent hA hA' U) (dJ : Descent hB hB' V)
    (ed : AdjunctionComparison (adj₀) (adj₁) dI.D dJ.D)
    (units : ∀ X, IsIso ((adj₀).unit.app X)) :
    ∀ a : A.Obj, IsIso ((adj₁).unit.app ((QA₁).obj (representable (A := A₁) a))) := by
  intro a
  let X := (QA₀).obj (representable (A := A₀) a)
  have hX : IsIso ((adj₁).unit.app (dI.D.obj X)) := by
    rw [← ed.unit X]
    letI : IsIso ((adj₀).unit.app X) := units X
    exact (dI.D.mapIso (asIso ((adj₀).unit.app X)) ≪≫ ed.hom.app _ ≪≫
      (G₁).mapIso (ed.tensor.app X)).isIso_hom
  let e := (inputIso.{u,vA,w,max v z t,s} A).app (representable (A := A) a)
  let i : dI.D.obj X ≅ (QA₁).obj (representable (A := A₁) a) :=
    dI.representedIso (representable (A := A₀) a) ≪≫
      (RightDGModule.toHomotopyCategory A₁ ⋙ QA₁).mapIso e
  exact (unitIsomorphism_closed (adj₁)).of_iso i hX

set_option maxHeartbeats 550000 in
private theorem morphismQuasiIsomorphisms_of_upper_units
    (hrep : ComputesRepresentableUnit.{u,max vA v t s,w,z} d')
    (units : ∀ a : A.Obj, IsIso ((adj₁).unit.app ((QA₁).obj (representable (A := A₁) a)))) :
    MorphismQuasiIsomorphisms.{u,max vA v t s,w,z} m'.bimodule := by
  intro a b
  let R := representable (A := A₁) b
  obtain ⟨hp, e, _, he, hη⟩ := hrep b
  let G := ordinaryHom.{u,max vA v t s,w,z} m'.models.hom
  let η := m'.models.adjunction.unit.app R ≫ G.map e.hom
  let f := DerivedAdjunctionData.onProjective.{u,max vA v t s,w,z} d' R hp
  let g := (RightDGModule.toHomotopyCategory B₁ ⋙ QB₁).mapIso e
  let r := DerivedAdjunctionData.onInput.{u,max vA v t s,w,z} d' (m'.bimodule.obj b)
  let p := ((G₁).mapIso (f ≪≫ g) ≪≫ r).hom
  have hp' : IsIso p := inferInstance
  letI : IsIso ((adj₁).unit.app ((QA₁).obj R)) := units b
  have hi : IsIso ((QA₁).map (homotopyClass η)) := by
    rw [← (show (adj₁).unit.app ((QA₁).obj R) ≫ p = (QA₁).map (homotopyClass η) from hη)]
    infer_instance
  have hηq := strict_quasiIso_of_localizedIso.{u,max vA v t z s,w} hA' η hi
  rw [← he a]
  letI : QuasiIso (η.app a) := hηq a
  exact inferInstance

set_option maxHeartbeats 850000 in
private theorem upper_compactness
    (classify : CompactFiniteCells.OriginalCompactFiniteCells.{u,v,z,s,t})
    (S : Preadditive (D B₀ hB)) (S' : Preadditive (D B₁ hB'))
    (h : ∀ a, CompactAt.{u,z,max vA v w z t,max vA v w z t} hB S
      ((QB₀).obj (m.bimodule.obj a))) :
    ∀ a, CompactAt.{u,z,max vA v w z t s,max vA v w z t s} hB' S'
      ((QB₁).obj (m'.bimodule.obj a)) := by
  let Bsmall := category.{u,v,z,t} B
  have hsmall : HomotopyCategoryLaws Bsmall := ⟨RightDGModule.instCategoryK _, rfl⟩
  let Ssmall := RightDGModule.derivedPreadditive.{u,max v t,z} Bsmall hsmall
  have hadd := native_localization_additive.{u,max v t,z} hsmall Ssmall
  obtain ⟨d₀, ⟨_, ⟨ff⟩⟩, _, _⟩ :=
    DG.DerivedCoefficientLift.derivedCoefficientTransition.{u,v,z,t,max vA w} B hsmall hB
  obtain ⟨d₁, _, _, _⟩ :=
    DG.DerivedCoefficientLift.derivedCoefficientTransition.{u,v,z,t,max vA w s} B hsmall hB'
  let qsmall := Q Bsmall hsmall
  let Jsmall := AmbientDerived.strictInput.{u,v,z,t} B
  let q₀ := RightDGModule.toHomotopyCategory B₀ ⋙ QB₀
  let q₁ := RightDGModule.toHomotopyCategory B₁ ⋙ QB₁
  let up₀ := inputIso.{u,v,z,t,max vA w} B
  let up₁ := inputIso.{u,v,z,t,max vA w s} B
  intro a
  let X := qsmall.obj (Jsmall.obj (T.obj a))
  let e₀ : d₀.D.obj X ≅ (QB₀).obj (m.bimodule.obj a) :=
    d₀.representedIso (Jsmall.obj (T.obj a)) ≪≫ q₀.mapIso
      ((up₀.app (T.obj a)) ≪≫ eqToIso (m.comparisonLaws.obj_eq a).symm)
  have h₀ : CompactAt.{u,z,max vA v w z t,max vA v w z t} hB S (d₀.D.obj X) := by
    letI := S
    intro I N c hc
    exact compact_iso e₀.symm (h a) c hc
  have hs : CompactAt.{u,z,max v z t,max v z t} hsmall Ssmall X :=
    compactness_reflects.{u,v,z,t,max vA w} d₀ ff Ssmall S h₀
  obtain ⟨P, hP, ⟨r⟩⟩ := ((classify B hsmall Ssmall hadd X).1).mp hs
  let P₁ := (AmbientDerived.strictInput.{u,v,z,max vA w t s} B).obj P
  have hP₁ : IndexedSemiFree.finiteCell P₁ :=
    (DG.CellLift.finiteCellTransport.{u,v,z,max vA w z t s} P₁).mpr
      ⟨P, hP, ⟨Iso.refl _⟩⟩
  let e₁ : d₁.D.obj X ≅ (QB₁).obj (m'.bimodule.obj a) :=
    d₁.representedIso (Jsmall.obj (T.obj a)) ≪≫ q₁.mapIso
      ((up₁.app (T.obj a)) ≪≫ eqToIso (m'.comparisonLaws.obj_eq a).symm)
  let eP : d₁.D.obj (qsmall.obj (Jsmall.obj P)) ≅ (QB₁).obj P₁ :=
    d₁.representedIso (Jsmall.obj P) ≪≫ q₁.mapIso (up₁.app P)
  let r₁ : Retract ((QB₁).obj (m'.bimodule.obj a)) ((QB₁).obj P₁) :=
    (Retract.ofIso e₁.symm).trans ((r.map d₁.D).trans (Retract.ofIso eP))
  letI := S'
  intro I N c hc
  exact compact_retract r₁ (native_finiteCell_compact.{u,max vA v w t s,z} hB' S' hP₁) c hc

end LargerCoproduct

set_option maxHeartbeats 1400000 in
/-- Conditional form of the Morita unit comparison under coefficient enlargement. -/
theorem moritaUnitTransition_conditional
    (_premise1 : CompactFiniteCells.AmbientCompactnessComparison.{u,v,w,t,s})
    (_premise2 : CompactFiniteCells.NativeCompactFiniteCells.{u,v,w,s})
    (_premise3 : CompactFiniteCells.NativeCompactnessComparison.{u,v,w,s})
    (classify : CompactFiniteCells.OriginalCompactFiniteCells.{u,v,z,s,t})
    (_premise5 : DerivedBimoduleAdjunction.AdequateNativeProjectivityTransition.{u,v,w,vA,z,t})
    (_premise6 : DerivedBimoduleAdjunction.AmbientDerivedAdjunction.{u,v,w,vA,z,t})
    (compare : DerivedBimoduleAdjunction.AmbientDerivedAdjunctionComparison.{u,v,w,vA,z,t,s})
    (_premise8 : DerivedBimoduleAdjunction.AmbientExactDerivedAdjunction.{u,v,w,vA,z,t})
    (_premise9 : DerivedBimoduleAdjunction.AmbientProjectivityTransition.{u,v,w,vA,z,t,s})
    (_premise10 : DerivedBimoduleAdjunction.DerivedAdjunctionAt.{u,v,w,z})
    (_premise11 : DerivedBimoduleAdjunction.ExactDerivedAdjunctionAt.{u,v,w,z})
    (_premise12 : DerivedBimoduleAdjunction.HomShiftConeComparison.{u,v,w,z})
    (_premise13 : DerivedBimoduleAdjunction.NativeDerivedAdjunctionCompatibility.{u,v,w,z})
    (_premise14 : DerivedBimoduleAdjunction.NativeHomDescent.{u,v,w,vA,z})
    (_premise15 : DerivedBimoduleAdjunction.NativeHomPreservesQuasiIsomorphisms.{u,v,w,vA,z})
    (_premise16 : DerivedBimoduleAdjunction.TensorPreservesKProjectives.{u,v,w,z}) :
    MoritaUnitTransition.{u,v,w,vA,z,t,s} := by
  intro k _ A B T m m' hA hB hA' hB' S S' _ _ hP hc hqi
  let B' := AmbientDerived.category.{u,v,z,max vA w t s} B
  letI := Derived.homotopyCategory B' hB'
  letI := derivedCategoryInstance B' hB'
  let qB' : HomComplex.homotopyCategory B' ⥤ D B' hB' := Q B' hB'
  obtain ⟨hP', step⟩ := compare T m m' hP
  obtain ⟨dI, dJ, e, eT, hI, hJ, _, hStrict, d, d', hd, ht, hex, hd', ht', hex', ⟨ed, hEd⟩⟩ :=
    step hA hB hA' hB'
  have hcompact := upper_compactness.{u,v,w,vA,z,t,s} (m := m) (m' := m') (hB := hB) (hB' := hB')
    classify S S' hc
  have hshifted : ∀ a n, CompactFiniteCells.CompactAt.{u,z,max vA v w z t s,max vA v w z t s} hB' S'
      (qB'.obj (ShiftCone.shift (m'.bimodule.obj a) n)) := by
    obtain ⟨_, cB, _, _, _⟩ := hex'
    intro a n
    exact native_compact_shift.{u,max vA v w t s,z,max vA v w z t s} hB' S' cB (hcompact a) n
  have hU := computesRepresentableUnit.{u,max vA v t,w,z} m.models d hd ht
  have hU' := computesRepresentableUnit.{u,max vA v t s,w,z} m'.models d' hd' ht'
  have hcoprod : PreservesCoproducts.{max vA v w z t}
      (DerivedAdjunctionData.hom.{u,max vA v t,w,z} d).derived :=
    morita_hom_preserves.{u,max vA v t,w,z,max vA v w z t} m.models d ht hex S hc
  have units := units_on_all_objects.{u,max vA v t,w,z} m.models d hU hex hcoprod hqi
  have hq' : MorphismQuasiIsomorphisms.{u,max vA v t s,w,z} m'.bimodule :=
    morphismQuasiIsomorphisms_of_upper_units.{u,v,w,vA,z,t,s} (d' := d') hU'
      (units_on_upper_representables.{u,v,w,vA,z,t,s} (d := d) (d' := d') dI dJ ed units)
  have hG' : PreservesCoproducts.{s} (DerivedAdjunctionData.hom.{u,max vA v t s,w,z} d').derived :=
    morita_hom_preserves.{u,max vA v t s,w,z,s} m'.models d' ht' hex' S' hcompact
  exact ⟨hP', hshifted, hq', dI, dJ, e, eT, hI, hJ, hStrict, d, d', hd, ht, hex, hd', ht', hex',
    ed, hEd, hG', largerCoproducts_on_represented_inputs.{u,v,w,vA,z,t,s} dI dJ ed hG'⟩

end

end DerivedFormalization.DGBimodule

universe v8_closure_8fd8830b2bd90968_u0 v8_closure_8fd8830b2bd90968_u1 v8_closure_8fd8830b2bd90968_u2 v8_closure_8fd8830b2bd90968_u3 v8_closure_8fd8830b2bd90968_u4 v8_closure_8fd8830b2bd90968_u5 v8_closure_8fd8830b2bd90968_u6
theorem _root_.«DerivedFormalization».«DGBimodule».«moritaUnitAt» : _root_.«Specs».«DerivedFormalization».«DG».«MoritaUnit».«MoritaUnitAt».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4} :=
  @_root_.«DerivedFormalization».«DGBimodule».«moritaUnitAt_conditional».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4} (@_root_.«DerivedFormalization».«RightDGModule».«ambientCompactnessComparison».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«RightDGModule».«nativeCompactFiniteCells».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«RightDGModule».«nativeCompactnessComparison».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«RightDGModule».«originalCompactFiniteCells».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u4, v8_closure_8fd8830b2bd90968_u1}) (@_root_.«DerivedFormalization».«DGBimodule».«adequateNativeProjectivityTransition».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u1}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientDerivedAdjunction».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u1}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientDerivedAdjunctionComparison».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientExactDerivedAdjunction».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u1}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientProjectivityTransition».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«DGBimodule».«derivedAdjunctionAt».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«exactDerivedAdjunctionAt».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«homShiftConeComparison».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeDerivedAdjunctionCompatibility».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeHomDescent».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeHomPreservesQuasiIsomorphisms».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u3}) (@_root_.«DerivedFormalization».«DGBimodule».«tensorPreservesKProjectives».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3})
theorem _root_.«DerivedFormalization».«DGBimodule».«moritaUnitTransition» : _root_.«Specs».«DerivedFormalization».«DG».«MoritaUnit».«MoritaUnitTransition».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4, v8_closure_8fd8830b2bd90968_u5, v8_closure_8fd8830b2bd90968_u6} :=
  @_root_.«DerivedFormalization».«DGBimodule».«moritaUnitTransition_conditional».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4, v8_closure_8fd8830b2bd90968_u5, v8_closure_8fd8830b2bd90968_u6} (@_root_.«DerivedFormalization».«RightDGModule».«ambientCompactnessComparison».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u5, v8_closure_8fd8830b2bd90968_u6}) (@_root_.«DerivedFormalization».«RightDGModule».«nativeCompactFiniteCells».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u6}) (@_root_.«DerivedFormalization».«RightDGModule».«nativeCompactnessComparison».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u6}) (@_root_.«DerivedFormalization».«RightDGModule».«originalCompactFiniteCells».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u4, v8_closure_8fd8830b2bd90968_u6, v8_closure_8fd8830b2bd90968_u5}) (@_root_.«DerivedFormalization».«DGBimodule».«adequateNativeProjectivityTransition».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4, v8_closure_8fd8830b2bd90968_u5}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientDerivedAdjunction».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4, v8_closure_8fd8830b2bd90968_u5}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientDerivedAdjunctionComparison».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4, v8_closure_8fd8830b2bd90968_u5, v8_closure_8fd8830b2bd90968_u6}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientExactDerivedAdjunction».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4, v8_closure_8fd8830b2bd90968_u5}) (@_root_.«DerivedFormalization».«DGBimodule».«ambientProjectivityTransition».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4, v8_closure_8fd8830b2bd90968_u5, v8_closure_8fd8830b2bd90968_u6}) (@_root_.«DerivedFormalization».«DGBimodule».«derivedAdjunctionAt».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«DGBimodule».«exactDerivedAdjunctionAt».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«DGBimodule».«homShiftConeComparison».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeDerivedAdjunctionCompatibility».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeHomDescent».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeHomPreservesQuasiIsomorphisms».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u3, v8_closure_8fd8830b2bd90968_u4}) (@_root_.«DerivedFormalization».«DGBimodule».«tensorPreservesKProjectives».{v8_closure_8fd8830b2bd90968_u0, v8_closure_8fd8830b2bd90968_u1, v8_closure_8fd8830b2bd90968_u2, v8_closure_8fd8830b2bd90968_u4})
