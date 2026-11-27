import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.FlatFiltration
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedBimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeResolution
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Products.Basic

open CategoryTheory
open CategoryTheory.Prod
open scoped Classical DirectSum

universe u v t

namespace DerivedFormalization.Affine.DerivedTensor

open Tensor
open RightDGModule (IsKProjective)
open Specs.DerivedFormalization.Affine.Tensor (dgCat regular term act pure signedBimodule restrict)
open Specs.DerivedFormalization.Affine.FlatFiltration (GradedSplit GradedDirectSum)
open _root_.Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.HomComplex (component)

open private cycles_are_boundaries chain_comm chain_comm_at from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.FlatFiltration
open private representable_kProjective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B C : CommDGAlgebra.{u,v} k}

local notation "φ[" f "," n "]" => HomologicalComplex.Hom.f (RightDGModuleHomModel.app f ()) n

private theorem flat_of_zero_terms {M : A.Module} (h : ∀ n (x : term M n), x = 0) :
    KFlat M := by
  intro E _
  apply (cycles_are_boundaries _).2
  intro n x _
  refine ⟨0, ?_⟩
  rw [map_zero]
  have e : LinearMap.id (R := k) (M := term (over E M) n) = 0 := by
    apply pure_ext (f := 𝟙 A) (M := E) (N := M)
    intro i j hij y z
    change pure (𝟙 A) i j n hij y z = 0
    rw [h j z, ← pair_apply, map_zero]
  exact (LinearMap.congr_fun e x).symm

set_option maxHeartbeats 800000 in
private def cellProjection {P Q : A.Module} {I : Type v} {c : IndexedSemiFree.CellFamily P I}
    (E : IndexedSemiFree.Attachment c Q) : Q ⟶ SemiFree.directSum (IndexedSemiFree.cells c) :=
  homOfDegrees
    (fun n => (LinearMap.snd k _ _).comp (E.coordinates () n).toLinearMap)
    (by
      intro n x
      change differential (SemiFree.directSum (IndexedSemiFree.cells c)) n
        (E.coordinates () n x).2 = (E.coordinates () (n+1) (differential Q n x)).2
      apply DFinsupp.ext
      intro s
      rw [show differential (SemiFree.directSum (IndexedSemiFree.cells c)) n
          (E.coordinates () n x).2 s = _ from
        SemiFree.directSum_d (IndexedSemiFree.cells c) () n (E.coordinates () n x).2 s]
      exact ((E.coordinate_d () n x).2 s).symm)
    (by
      intro i j n h x a
      apply DFinsupp.ext
      intro s
      exact (E.coordinate_act (a := ()) (b := ()) i j n h x a).2 s)

private def cellSplitting {P Q : A.Module} {I : Type v} {c : IndexedSemiFree.CellFamily P I}
    (E : IndexedSemiFree.Attachment c Q) : GradedSplit E.inclusion (cellProjection E) := by
  let S := SemiFree.directSum (IndexedSemiFree.cells c)
  let L (n : ℤ) := E.coordinates () n
  let p := cellProjection E
  change GradedSplit E.inclusion p
  have hp (n : ℤ) (x : term Q n) : φ[p,n] x = (L n x).2 := rfl
  refine
    { zero := ?_
      retraction := ⟨fun a => by
        cases a
        exact CochainComplex.HomComplex.Cochain.ofHoms fun i =>
          ModuleCat.ofHom ((LinearMap.fst k _ _).comp (L i).toLinearMap),
        ?_⟩
      sectionMap := ⟨fun a => by
        cases a
        exact CochainComplex.HomComplex.Cochain.ofHoms fun i =>
          ModuleCat.ofHom ((L i).symm.toLinearMap.comp (LinearMap.inr k _ _)),
        ?_⟩
      retract := ?_
      section_id := ?_
      decompose := ?_ }
  · apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg Prod.snd (E.coordinate_inclusion () n x)
  · rintro ⟨⟩ ⟨⟩ i j n i' n' h hi hn x a
    have hi' : i = i' := by omega
    have hn' : n = n' := by omega
    cases hi'
    cases hn' 
    simpa [CochainComplex.HomComplex.Cochain.ofHoms_v] using
      (E.coordinate_act (a := ()) (b := ()) i j n h x a).1
  · rintro ⟨⟩ ⟨⟩ i j n i' n' h hi hn x a
    have hi' : i = i' := by omega
    have hn' : n = n' := by omega
    cases hi'
    cases hn' 
    simp only [CochainComplex.HomComplex.Cochain.ofHoms_v]
    change (L n).symm (0, act S i j n h x a) =
      act Q i j n h ((L i).symm (0, x)) a
    apply (L n).injective
    rw [LinearEquiv.apply_symm_apply]
    have e := E.coordinate_act (a := ()) (b := ()) i j n h ((L i).symm (0, x)) a
    change (L n (act Q i j n h ((L i).symm (0, x)) a)).1 =
      act P i j n h (L i ((L i).symm (0, x))).1 a ∧ _ at e
    rw [LinearEquiv.apply_symm_apply] at e
    exact (Prod.ext (by simpa using e.1) (DFinsupp.ext e.2)).symm
  · intro n x
    exact congrArg Prod.fst (E.coordinate_inclusion () n x)
  · intro n x
    change φ[p,n] ((L n).symm (0, x)) = x
    rw [hp, LinearEquiv.apply_symm_apply]
  · intro n x
    change φ[E.inclusion,n] (L n x).1 + (L n).symm (0, (φ[p,n] x)) = x
    apply (L n).injective
    rw [map_add, hp, LinearEquiv.apply_symm_apply]
    change E.coordinates () n (φ[E.inclusion,n] (L n x).1) + _ = _
    rw [E.coordinate_inclusion]
    exact Prod.ext (add_zero _) (zero_add _)

theorem semiFree_kFlat {M : A.Module} (h : IndexedSemiFree.semiFree M) : KFlat M := by
  obtain ⟨F⟩ := h
  let D : ℕ ⥤ A.Module := Functor.ofSequence (fun n => (F.extension n).inclusion)
  let α : D ⟶ (Functor.const ℕ).obj M := NatTrans.ofSequence F.into (by
    intro n
    dsimp only [D]
    rw [Functor.ofSequence_map_homOfLE_succ]
    change (F.extension n).inclusion ≫ F.into (n + 1) = F.into n ≫ 𝟙 M
    rw [Category.comp_id]
    exact F.compatible n)
  refine FlatFiltration.kFlat_of_union (F := D)
    ⟨F.into, fun {i j} e => by
      have he := α.naturality (homOfLE e)
      change D.map (homOfLE e) ≫ F.into j = F.into i ≫ 𝟙 M at he
      exact he.trans (Category.comp_id _),
      fun n i => F.injective n () i, F.exhaustive ()⟩ ?_
  intro n
  induction n with
  | zero => exact flat_of_zero_terms (F.bottom ())
  | succ n ih =>
    let c := F.family n
    have hS : KFlat (SemiFree.directSum (IndexedSemiFree.cells c)) := by
      apply FlatFiltration.kFlat_of_directSum
        (S := ⟨SemiFree.sumInclusion _, fun i => by
          have e : DirectSum.toModule k _ _
              (fun s => φ[SemiFree.sumInclusion (IndexedSemiFree.cells c) s,i].hom) =
              LinearMap.id := by
            apply DirectSum.linearMap_ext
            intro s
            apply LinearMap.ext
            intro x
            change DirectSum.toModule k _ _ (fun s => (SemiFree.summand
              (IndexedSemiFree.cells c) () i s)) (DirectSum.lof k _ _ s x) = _
            rw [DirectSum.toModule_lof]
            rfl
          rw [e]
          exact Function.bijective_id⟩)
      intro s
      have hs : c.object s = () := Subsingleton.elim _ _
      change KFlat (SemiFree.cell (c.object s) (c.degree s))
      rw [hs]
      exact FlatFiltration.kFlat_shift (regular A) _ (regular_kFlat (A := A))
    exact FlatFiltration.kFlat_of_gradedSplit (cellSplitting (F.extension n)) ih hS

theorem kProjective_kFlat {P : A.Module} (hP : IsKProjective P) : KFlat P := by
  obtain ⟨S, p, hS, _, hp⟩ :=
    RightDGModule.unboundedSemiFreeResolutionInUniverse.{u,v,0} k (dgCat A) P
  obtain ⟨q, _, j, _, hj⟩ :=
    RightDGModule.IsKProjective.homotopyEquivalence_of_quasiIso p
      (RightDGModule.IsSemiFree.isKProjective hS) hP hp
  intro E hE
  apply (cycles_are_boundaries _).2
  intro n x hx
  have hy : differential (over E S) n (φ[mapSecond (𝟙 A) E q,n] x) = 0 := by
    rw [← chain_comm (mapSecond (𝟙 A) E q), hx, map_zero]
  obtain ⟨y, hy⟩ := (cycles_are_boundaries _).1 (semiFree_kFlat hS E hE) n _ hy
  let w := mapSecondGraded (𝟙 A) E j
  have hw := map_second_homotopy (𝟙 A) E _ _ j hj () n x
  change φ[mapSecond (𝟙 A) E (q ≫ p),n] x - φ[mapSecond (𝟙 A) E (𝟙 P),n] x =
    ((over E P).complex ()).d (n-1) n (component w () n (n-1) (by omega) x) +
      component w () (n+1) n (by omega) (differential (over E P) n x) at hw
  have hcomp : mapSecond (𝟙 A) E (q ≫ p) =
      mapSecond (𝟙 A) E q ≫ mapSecond (𝟙 A) E p :=
    (secondFunctor (𝟙 A) E).map_comp q p
  have hid : mapSecond (𝟙 A) E (𝟙 P) = 𝟙 (over E P) :=
    (secondFunctor (𝟙 A) E).map_id P
  rw [hcomp, hid, hx, map_zero, add_zero] at hw
  change φ[mapSecond (𝟙 A) E p,n] (φ[mapSecond (𝟙 A) E q,n] x) - x = _ at hw
  refine ⟨φ[mapSecond (𝟙 A) E p,n-1] y - component w () n (n-1) (by omega) x, ?_⟩
  rw [map_sub, ← chain_comm_at (mapSecond (𝟙 A) E p), hy, ← hw]
  abel

open RightDGModule

private def strictTensor (f : A ⟶ B) : A.Module × B.Module ⥤ B.Module where
  obj X := tensor f X.1 X.2
  map {X Y} g := (extension f X.2).map g.1 ≫ mapSecond f Y.1 g.2
  map_id X := by
    change (extension f X.2).map (𝟙 X.1) ≫ (secondFunctor f X.1).map (𝟙 X.2) = _
    rw [(extension f X.2).map_id X.1, (secondFunctor f X.1).map_id X.2]
    exact Category.id_comp _
  map_comp {X Y Z} g h := by
    change (extension f X.2).map (g.1 ≫ h.1) ≫
        (secondFunctor f Z.1).map (g.2 ≫ h.2) =
      ((extension f X.2).map g.1 ≫ mapSecond f Y.1 g.2) ≫
        ((extension f Y.2).map h.1 ≫ mapSecond f Z.1 h.2)
    rw [Functor.map_comp, Functor.map_comp]
    change ((extension f X.2).map g.1 ≫ (extension f X.2).map h.1) ≫
        (mapSecond f Z.1 g.2 ≫ mapSecond f Z.1 h.2) = _
    let a := (extension f X.2).map g.1
    let b := (extension f X.2).map h.1
    let c := mapSecond f Z.1 g.2
    let d := mapSecond f Z.1 h.2
    let e := mapSecond f Y.1 g.2
    let j := (extension f Y.2).map h.1
    change (a ≫ b) ≫ (c ≫ d) = (a ≫ e) ≫ (j ≫ d)
    calc
      _ = a ≫ (b ≫ c) ≫ d :=
        (Category.assoc a b (c ≫ d)).trans (congrArg (a ≫ ·) (Category.assoc b c d).symm)
      _ = a ≫ (e ≫ j) ≫ d := congrArg (fun m => a ≫ m ≫ d) (map_tensor_comm f h.1 g.2)
      _ = _ := (congrArg (a ≫ ·) (Category.assoc e j d)).trans
        (Category.assoc a e (j ≫ d)).symm

open private representative representative_class from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedBimoduleAdjunction

private theorem tensorHomotopyCongr (f : A ⟶ B) {X Y : A.Module × B.Module}
    (g h : X ⟶ Y) (e₁ : homotopyClass g.1 = homotopyClass h.1)
    (e₂ : homotopyClass g.2 = homotopyClass h.2) :
    homotopyClass ((strictTensor f).map g) = homotopyClass ((strictTensor f).map h) := by
  obtain ⟨w₁, hw₁⟩ := (homotopyCriterion _ _).1 e₁
  obtain ⟨w₂, hw₂⟩ := (homotopyCriterion _ _).1 e₂
  have c₁ := (homotopyCriterion _ _).2
    ⟨_, map_first_homotopy f X.2 g.1 h.1 w₁ hw₁⟩
  have c₂ := (homotopyCriterion _ _).2
    ⟨_, map_second_homotopy f Y.1 g.2 h.2 w₂ hw₂⟩
  let H := toHomotopyCategory (dgCat B)
  change H.map ((extension f X.2).map g.1 ≫ mapSecond f Y.1 g.2) =
    H.map ((extension f X.2).map h.1 ≫ mapSecond f Y.1 h.2)
  rw [H.map_comp, H.map_comp]
  exact congrArg₂ (fun a b => a ≫ b) c₁ c₂

private abbrev strictPair {X Y : A.Module × B.Module} (g : X.1 ⟶ Y.1) (h : X.2 ⟶ Y.2) :
    X ⟶ Y := ⟨g, h⟩

private abbrev prodQuotient (A B : CommDGAlgebra.{u,v} k) :=
  (toHomotopyCategory (dgCat A)).prod (toHomotopyCategory (dgCat B))

private def tensorRepresentative {X Y : A.Module × B.Module}
    (g : (prodQuotient A B).obj X ⟶ (prodQuotient A B).obj Y) : X ⟶ Y :=
  strictPair (representative (C := dgCat A) g.1) (representative (C := dgCat B) g.2)

private theorem tensorRepresentative_class {X Y : A.Module × B.Module}
    (g : (prodQuotient A B).obj X ⟶ (prodQuotient A B).obj Y) :
    (prodQuotient A B).map (tensorRepresentative g) = g :=
  CategoryTheory.Prod.hom_ext (representative_class g.1) (representative_class g.2)

private abbrev tensorClass (f : A ⟶ B) := strictTensor f ⋙ toHomotopyCategory (dgCat B)

private def tensorClassMap (f : A ⟶ B) {X Y : A.Module × B.Module}
    (g : (prodQuotient A B).obj X ⟶ (prodQuotient A B).obj Y) :
    (tensorClass f).obj X ⟶ (tensorClass f).obj Y :=
  (tensorClass f).map (tensorRepresentative g)

private theorem tensorClassMap_on_strict (f : A ⟶ B) {X Y : A.Module × B.Module}
    (g : X ⟶ Y) :
    tensorClassMap f ((prodQuotient A B).map g) = (tensorClass f).map g :=
  tensorHomotopyCongr f _ _ (representative_class _) (representative_class _)

set_option maxHeartbeats 900000 in
/-- The signed tensor on the full module homotopy categories. -/
def homotopyTensor (f : A ⟶ B) : K (dgCat A) × K (dgCat B) ⥤ K (dgCat B) where
  obj X := (tensorClass f).obj X
  map g := tensorClassMap f g
  map_id X := by
    let X₀ : A.Module × B.Module := X
    have e := tensorClassMap_on_strict f (𝟙 X₀)
    rw [(prodQuotient A B).map_id, (tensorClass f).map_id] at e
    exact e
  map_comp {X Y Z} g h := by
    let g₀ := tensorRepresentative (X := X) (Y := Y) g
    let h₀ := tensorRepresentative (X := Y) (Y := Z) h
    have e := tensorClassMap_on_strict f (g₀ ≫ h₀)
    have eg : (prodQuotient A B).map g₀ = g := tensorRepresentative_class g
    have eh : (prodQuotient A B).map h₀ = h := tensorRepresentative_class h
    rw [(prodQuotient A B).map_comp, eg, eh, (tensorClass f).map_comp] at e
    exact e

theorem homotopyTensor_map (f : A ⟶ B) {M M' : A.Module} {N N' : B.Module}
    (g : M ⟶ M') (h : N ⟶ N') :
    (homotopyTensor f).map ((prodQuotient A B).map (strictPair (X := (M, N)) (Y := (M', N')) g h)) =
      homotopyClass ((extension f N).map g ≫ mapSecond f M' h) :=
  tensorClassMap_on_strict f (strictPair (X := (M, N)) (Y := (M', N')) g h)

open private resolutionFunctor from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedBimoduleAdjunction

private theorem laws (A : CommDGAlgebra.{u,v} k) :
    Derived.HomotopyCategoryLaws (dgCat A) := ⟨instCategoryK _, rfl⟩

local instance (A : DGCategory.{u,v,0} k) : Category (HomComplex.homotopyCategory A) :=
  inferInstanceAs (Category (K A))

private abbrev resolve (A : CommDGAlgebra.{u,v} k) : D (dgCat A) (laws A) ⥤ K (dgCat A) :=
  resolutionFunctor.{u,v,0,0} (A := dgCat A) (laws A)

/-- Derive the signed tensor by resolving both arguments in the native category. -/
def derivedTensor (A : CommDGAlgebra.{u,v} k) :
    D (dgCat A) (laws A) × D (dgCat A) (laws A) ⥤ D (dgCat A) (laws A) :=
  (resolve A).prod (resolve A) ⋙ homotopyTensor (𝟙 A) ⋙ Q (dgCat A) (laws A)

private abbrev represented (M : A.Module) : D (dgCat A) (laws A) := (Q (dgCat A) (laws A)).obj M

private abbrev localizeMap {M N : A.Module} (g : M ⟶ N) :
    represented M ⟶ represented N := (Q (dgCat A) (laws A)).map (homotopyClass g)

private abbrev localizeTensor (X : A.Module × A.Module) : D (dgCat A) (laws A) :=
  represented (over X.1 X.2)

private def quasiIsoIso {M N : A.Module} (f : M ⟶ N) (hf : IsQuasiIso f) :
    represented M ≅ represented N := by
  have : IsIso (localizeMap f) :=
    Localization.inverts (Q (dgCat A) (laws A)) (RightDGModule.quasiIsomorphisms (dgCat A)) _
      ⟨f, rfl, hf⟩
  exact asIso (localizeMap f)

private def resolutionAtProjective (P : A.Module) (hP : IsKProjective P) :
    (resolve A).obj (represented P) ≅ (P : K (dgCat A)) :=
  (Specs.DerivedFormalization.DG.DerivedKProjective.kProjectiveObjects (dgCat A)).ι.mapIso
    ((RightDGModule.kProjectiveLocalizationEquivalence.{u,v,0} (dgCat A) (laws A)).unitIso.app
      ⟨P, hP⟩).symm

private def onProjectives (P R : A.Module) (hP : IsKProjective P) (hR : IsKProjective R) :
    (derivedTensor A).obj (represented P, represented R) ≅ localizeTensor (P, R) :=
  (homotopyTensor (𝟙 A) ⋙ Q (dgCat A) (laws A)).mapIso
    ((resolutionAtProjective P hP).prod (resolutionAtProjective R hR))

private def onReplacements {P R M N : A.Module}
    (p : P ⟶ M) (r : R ⟶ N) (hP : IsKProjective P) (hR : IsKProjective R)
    (hp : IsQuasiIso p) (hr : IsQuasiIso r) :
    (derivedTensor A).obj (represented M, represented N) ≅ localizeTensor (P, R) :=
  (derivedTensor A).mapIso (((quasiIsoIso p hp).prod (quasiIsoIso r hr)).symm) ≪≫
    onProjectives P R hP hR

/-- Two K-flat models can be used without resolving either factor again. -/
def onFlatPair {M N : A.Module} (_hM : KFlat M) (hN : KFlat N) :
    (derivedTensor A).obj (represented M, represented N) ≅ localizeTensor (M, N) := Classical.choice (by
  obtain ⟨P, p, hP, _, hp⟩ := RightDGModule.unboundedSemiFreeResolutionInUniverse.{u,v,0}
    k (dgCat A) M
  obtain ⟨R, r, hR, _, hr⟩ := RightDGModule.unboundedSemiFreeResolutionInUniverse.{u,v,0}
    k (dgCat A) N
  exact ⟨onReplacements p r (RightDGModule.IsSemiFree.isKProjective hP)
    (RightDGModule.IsSemiFree.isKProjective hR) hp hr ≪≫
    quasiIsoIso (mapSecond (𝟙 A) P r) (KFlat.map_quasiIso_second P (semiFree_kFlat hP) r hr) ≪≫
    quasiIsoIso ((extension (𝟙 A) N).map p) (hN.map_quasiIso p hp)⟩)

/-- A K-flat first factor computes the derived tensor against any unchanged second factor. -/
def onFlatLeft {M : A.Module} (hM : KFlat M) (N : A.Module) :
    (derivedTensor A).obj (represented M, represented N) ≅ localizeTensor (M, N) := Classical.choice (by
  obtain ⟨R, r, hR, _, hr⟩ := RightDGModule.unboundedSemiFreeResolutionInUniverse.{u,v,0}
    k (dgCat A) N
  exact ⟨(derivedTensor A).mapIso ((Iso.refl (represented M)).prod (quasiIsoIso r hr).symm) ≪≫
    onFlatPair hM (semiFree_kFlat hR) ≪≫
    quasiIsoIso (mapSecond (𝟙 A) M r) (KFlat.map_quasiIso_second M hM r hr)⟩)

/-- A K-flat second factor computes the derived tensor against any unchanged first factor. -/
def onFlatRight (M : A.Module) {N : A.Module} (hN : KFlat N) :
    (derivedTensor A).obj (represented M, represented N) ≅ localizeTensor (M, N) := Classical.choice (by
  obtain ⟨P, p, hP, _, hp⟩ := RightDGModule.unboundedSemiFreeResolutionInUniverse.{u,v,0}
    k (dgCat A) M
  exact ⟨(derivedTensor A).mapIso ((quasiIsoIso p hp).symm.prod (Iso.refl (represented N))) ≪≫
    onFlatPair (semiFree_kFlat hP) hN ≪≫
    quasiIsoIso ((extension (𝟙 A) N).map p) (hN.map_quasiIso p hp)⟩)

local instance specDerivedCategory (A : DGCategory.{u,v,0} k)
    (h : Derived.HomotopyCategoryLaws A) : Category (Derived.derivedCategory A h) :=
  DerivedKProjective.derivedCategoryInstance A h

section ScalarExtension

open _root_.Specs.DerivedFormalization.DG.DerivedBimoduleAdjunction
  (SignedModels DerivedAdjunctionData)
open _root_.Specs.DerivedFormalization.DG.BimoduleAdjunction (ordinaryTensor)

private abbrev scalarBimodule (f : A ⟶ B) := signedBimodule f (regular B)

private def scalarModels (f : A ⟶ B) : SignedModels.{u,v,0,0} (scalarBimodule f) where
  tensor := DGBimodule.tensorModel (scalarBimodule f)
  hom := DGBimodule.internalHomModel (scalarBimodule f)
  curry := DGBimodule.curryIso.{u,v,0,0} (scalarBimodule f)
  adjunction := DGBimodule.adjunction.{u,v,0,0} (scalarBimodule f)
  laws := DGBimodule.strictAdjunctionLaws.{u,v,0,0} (scalarBimodule f)

private theorem scalarBimodule_projective (f : A ⟶ B) (a : (dgCat A).Obj) :
    IsKProjective ((scalarBimodule f).obj a) :=
  representable_kProjective (A := dgCat B) ()

theorem scalarExtension_exact (f : A ⟶ B) :
    ∃ d : DerivedAdjunctionData.{u,v,0,0} (scalarModels f).tensor (scalarModels f).hom
        (laws A) (laws B),
      d.Realizes (scalarModels f).adjunction ∧ d.ComputesRepresentatives ∧ d.IsExact :=
  DGBimodule.exactDerivedAdjunctionAt.{u,v,0,0} (scalarModels f)
    (scalarBimodule_projective f) (laws A) (laws B)

private def scalarAdjunction (f : A ⟶ B) :=
  Classical.choose (scalarExtension_exact f)

/-- Exact derived scalar extension by the signed regular bimodule. -/
def derivedExtension (f : A ⟶ B) : D (dgCat A) (laws A) ⥤ D (dgCat B) (laws B) :=
  (scalarAdjunction f).tensor

private theorem baseChange_eq (f : A ⟶ B) :
    ordinaryTensor.{u,v,0,0} (scalarModels f).tensor = baseChange f := rfl

private theorem baseChange_preserves_for_flat {P M : A.Module}
    (f : A ⟶ B) (p : P ⟶ M) (hp : IsQuasiIso p) (hP : KFlat P) (hM : KFlat M) :
    IsQuasiIso ((baseChange f).map p) := by
  let U := restrict f (regular B)
  obtain ⟨S, s, hS, _, hs⟩ := unboundedSemiFreeResolutionInUniverse.{u,v,0} k (dgCat A) U
  let eP := restrictTensorIso (𝟙 A) f P (regular B)
  let eM := restrictTensorIso (𝟙 A) f M (regular B)
  have h₁ := KFlat.map_quasiIso_second P hP s hs
  have h₂ := KFlat.map_quasiIso_second M hM s hs
  have h₃ := (semiFree_kFlat hS).map_quasiIso p hp
  have e := map_tensor_comm (𝟙 A) p s
  have hQ : IsQuasiIso ((extension (𝟙 A) U).map p) := by
    rintro ⟨⟩
    let a := ((extension (𝟙 A) S).map p).app ()
    let b := (mapSecond (𝟙 A) M s).app ()
    let c := (mapSecond (𝟙 A) P s).app ()
    let d := ((extension (𝟙 A) U).map p).app ()
    have eq : a ≫ b = c ≫ d := congrArg (fun g => g.app ()) e
    have h : QuasiIso (a ≫ b) := quasiIso_comp _ _ (hφ := h₃ ()) (hφ' := h₂ ())
    exact (quasiIso_iff_comp_left c d (hφ := h₁ ())).1 (eq ▸ h)
  have hnat :
      (restrictFunctor f).map ((baseChange (𝟙 A ≫ f)).map p) ≫ eM.hom =
        eP.hom ≫ (extension (𝟙 A) U).map p := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply pure_ext (f := 𝟙 A ≫ f) (M := P) (N := regular B)
    intro i j h x y
    change ((eM.hom.app ()).f n)
        ((((baseChange (𝟙 A ≫ f)).map p).app ()).f n (pure (𝟙 A ≫ f) i j n h x y)) =
      (((extension (𝟙 A) U).map p).app ()).f n
        ((eP.hom.app ()).f n (pure (𝟙 A ≫ f) i j n h x y))
    rw [map_first_pure, restrictTensorIso_pure, restrictTensorIso_pure, map_first_pure]
  have hres : IsQuasiIso ((restrictFunctor f).map ((baseChange (𝟙 A ≫ f)).map p)) := by
    rintro ⟨⟩
    let F := RightDGModuleModel.eval (A := dgCat A) ()
    have hP' := quasiIso_of_isIso (F.mapIso eP).hom
    have hM' := quasiIso_of_isIso (F.mapIso eM).hom
    have h := quasiIso_comp (F.mapIso eP).hom (((extension (𝟙 A) U).map p).app ())
      (hφ := hP') (hφ' := hQ ())
    have eq := congrArg (fun g => g.app ()) hnat
    exact (quasiIso_iff_comp_right _ (F.mapIso eM).hom (hφ' := hM')).1 (eq.symm ▸ h)
  have hf : IsQuasiIso ((baseChange (𝟙 A ≫ f)).map p) := by
    rintro ⟨⟩
    exact hres ()
  rwa [Category.id_comp] at hf

/-- Scalar extension is computed by the unchanged K-flat first factor. -/
def extensionOnFlat {M : A.Module} (f : A ⟶ B) (hM : KFlat M) :
    (derivedExtension f).obj (represented M) ≅ represented ((baseChange f).obj M) :=
  Classical.choice (by
    obtain ⟨P, p, hP, _, hp⟩ := unboundedSemiFreeResolutionInUniverse.{u,v,0} k (dgCat A) M
    have e := (scalarAdjunction f).onReplacement p (IsSemiFree.isKProjective hP) hp
    refine ⟨?_⟩
    change (derivedExtension f).obj (represented M) ≅ represented ((baseChange f).obj P) at e
    exact e ≪≫ quasiIsoIso ((baseChange f).map p)
      (baseChange_preserves_for_flat f p hp (semiFree_kFlat hP) hM))

private def extensionOnFlatReplacement (f : A ⟶ B) {P M : A.Module}
    (p : P ⟶ M) (hP : KFlat P) (hp : IsQuasiIso p) :
    (derivedExtension f).obj (represented M) ≅ represented ((baseChange f).obj P) :=
  ((derivedExtension f).mapIso (quasiIsoIso p hp)).symm ≪≫ extensionOnFlat f hP

set_option maxHeartbeats 600000 in
private theorem baseChangeComp_natural (f : A ⟶ B) (g : B ⟶ C) {M N : A.Module} (p : M ⟶ N) :
    (baseChange g).map ((baseChange f).map p) ≫ (baseChangeComp f g N).hom =
      (baseChangeComp f g M).hom ≫ (baseChange (f ≫ g)).map p := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply pure_ext (f := g) (M := (baseChange f).obj M) (N := regular C)
  intro m l h z c
  let L := ((baseChange g).map ((baseChange f).map p) ≫ (baseChangeComp f g N).hom)
  let R := ((baseChangeComp f g M).hom ≫ (baseChange (f ≫ g)).map p)
  have eq : (φ[L,n].hom).comp ((pair g m l n h).flip c) =
      (φ[R,n].hom).comp ((pair g m l n h).flip c) := by
    apply pure_ext (f := f) (M := M) (N := regular B)
    intro i j e x b
    change φ[(baseChangeComp f g N).hom,n]
        (φ[(baseChange g).map ((baseChange f).map p),n]
          (pure g m l n h (pure f i j m e x b) c)) =
      φ[(baseChange (f ≫ g)).map p,n]
        (φ[(baseChangeComp f g M).hom,n] (pure g m l n h (pure f i j m e x b) c))
    rw [map_first_pure, map_first_pure, baseChangeComp_pure, baseChangeComp_pure, map_first_pure]
  exact LinearMap.congr_fun eq z

open private onHomotopy onHomotopy_map from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedBimoduleAdjunction
open private commute_heq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleCoefficientCompatibility

private theorem scalarRespectsHomotopy (f : A ⟶ B) {M N : A.Module} (p q : M ⟶ N)
    (e : homotopyClass p = homotopyClass q) :
    homotopyClass ((baseChange f).map p) = homotopyClass ((baseChange f).map q) := by
  obtain ⟨w, hw⟩ := (homotopyCriterion _ _).1 e
  exact (homotopyCriterion _ _).2 ⟨_, map_first_homotopy f (regular B) p q w hw⟩

private abbrev scalarHomotopy (f : A ⟶ B) :=
  onHomotopy (baseChange f) (scalarRespectsHomotopy f)

private theorem scalarHomotopy_map (f : A ⟶ B) {M N : A.Module} (p : M ⟶ N) :
    (scalarHomotopy f).map (homotopyClass p) = homotopyClass ((baseChange f).map p) :=
  onHomotopy_map (baseChange f) (scalarRespectsHomotopy f) p

private def scalarHomotopyComp (f : A ⟶ B) (g : B ⟶ C) :
    scalarHomotopy f ⋙ scalarHomotopy g ≅ scalarHomotopy (f ≫ g) :=
  NatIso.ofComponents
    (fun M => (toHomotopyCategory (dgCat C)).mapIso (baseChangeComp f g M))
    (by
      intro M N p
      obtain ⟨a, rfl⟩ := homotopyClass_surjective p
      change (scalarHomotopy g).map ((scalarHomotopy f).map (homotopyClass a)) ≫
        homotopyClass (baseChangeComp f g N).hom = homotopyClass (baseChangeComp f g M).hom ≫
          (scalarHomotopy (f ≫ g)).map (homotopyClass a)
      rw [scalarHomotopy_map f a, scalarHomotopy_map g ((baseChange f).map a),
        scalarHomotopy_map (f ≫ g) a]
      let F := toHomotopyCategory (dgCat C)
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← F.map_comp, ← F.map_comp, baseChangeComp_natural])

private def scalarHomotopyComparison (f : A ⟶ B) :
    (scalarAdjunction f).tensorH ≅ scalarHomotopy f :=
  NatIso.ofComponents (fun M => eqToIso ((scalarAdjunction f).tensorObj M)) (by
    intro M N p
    obtain ⟨a, rfl⟩ := homotopyClass_surjective p
    have hd := (Classical.choose_spec (scalarExtension_exact f)).1
    have e := commute_heq (C := K (dgCat B)) ((scalarAdjunction f).tensorObj M)
      ((scalarAdjunction f).tensorObj N) (hd.2.1 a)
    change (scalarAdjunction f).tensorH.map (homotopyClass a) ≫
        eqToHom ((scalarAdjunction f).tensorObj N) =
      eqToHom ((scalarAdjunction f).tensorObj M) ≫ (scalarHomotopy f).map (homotopyClass a)
    rw [scalarHomotopy_map]
    exact e)

private theorem baseChange_projective (f : A ⟶ B) (P : A.Module) (hP : IsKProjective P) :
    IsKProjective ((baseChange f).obj P) :=
  DGBimodule.tensorPreservesKProjectives.{u,v,0,0} (scalarModels f).tensor (scalarModels f).hom
    (scalarModels f).curry
    (scalarBimodule_projective f) P hP

private abbrev proj (A : CommDGAlgebra.{u,v} k) :=
  Specs.DerivedFormalization.DG.DerivedKProjective.kProjectiveObjects (dgCat A)

private abbrev localizedProjectives (A : CommDGAlgebra.{u,v} k) :=
  kProjectiveLocalizationEquivalence.{u,v,0} (dgCat A) (laws A)

private def scalarProjectives (f : A ⟶ B) : (proj A).FullSubcategory ⥤ (proj B).FullSubcategory :=
  (proj B).lift ((proj A).ι ⋙ scalarHomotopy f)
    (fun P => baseChange_projective f P.obj P.property)

private def scalarProjectiveComparison (f : A ⟶ B) :
    (localizedProjectives A).functor ⋙ derivedExtension f ≅
      scalarProjectives f ⋙ (localizedProjectives B).functor :=
  (scalarAdjunction f).tensorSquare ≪≫
    Functor.isoWhiskerLeft (proj A).ι
      (Functor.isoWhiskerRight (scalarHomotopyComparison f) (Q (dgCat B) (laws B)))

private def cancelEquivalence {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z]
    (E : X ≌ Y) {F G : Y ⥤ Z} (e : E.functor ⋙ F ≅ E.functor ⋙ G) : F ≅ G :=
  (Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight E.counitIso.symm F ≪≫
    Functor.isoWhiskerLeft E.inverse e ≪≫ Functor.isoWhiskerRight E.counitIso G ≪≫
    Functor.leftUnitor G

private theorem cancelEquivalence_on_image {X Y Z : Type*} [Category* X] [Category* Y]
    [Category* Z] (E : X ≌ Y) {F G : Y ⥤ Z} (e : E.functor ⋙ F ≅ E.functor ⋙ G) (x : X) :
    (cancelEquivalence E e).hom.app (E.functor.obj x) = e.hom.app x := by
  change 𝟙 _ ≫ F.map (E.counitInv.app (E.functor.obj x)) ≫
    e.hom.app (E.inverse.obj (E.functor.obj x)) ≫ G.map (E.counit.app (E.functor.obj x)) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id, E.counitInv_app_functor, E.counit_app_functor]
  have hn := e.hom.naturality (E.unitInv.app x)
  change F.map (E.functor.map (E.unitInv.app x)) ≫ e.hom.app x =
      e.hom.app (E.inverse.obj (E.functor.obj x)) ≫ G.map (E.functor.map (E.unitInv.app x)) at hn
  rw [← hn, ← Category.assoc, ← F.map_comp, ← E.functor.map_comp, E.unitIso.hom_inv_id_app]
  change F.map (E.functor.map (𝟙 x)) ≫ e.hom.app x = e.hom.app x
  rw [E.functor.map_id x, F.map_id (E.functor.obj x), Category.id_comp]

private theorem scalarProjectiveComparison_app (f : A ⟶ B) (P : (proj A).FullSubcategory) :
    (scalarProjectiveComparison f).hom.app P =
      ((scalarAdjunction f).onProjective P.obj P.property).hom := by
  change (scalarAdjunction f).tensorSquare.hom.app P ≫
      (Q (dgCat B) (laws B)).map (eqToHom ((scalarAdjunction f).tensorObj P.obj)) =
    (scalarAdjunction f).tensorSquare.hom.app P ≫
      eqToHom (congrArg (Q (dgCat B) (laws B)).obj ((scalarAdjunction f).tensorObj P.obj))
  rw [eqToHom_map]
  rfl

private def extensionCompAtProjectives (f : A ⟶ B) (g : B ⟶ C) :
    (localizedProjectives A).functor ⋙ (derivedExtension f ⋙ derivedExtension g) ≅
      (localizedProjectives A).functor ⋙ derivedExtension (f ≫ g) :=
  Functor.isoWhiskerRight (scalarProjectiveComparison f) (derivedExtension g) ≪≫
    Functor.isoWhiskerLeft (scalarProjectives f) (scalarProjectiveComparison g) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (proj A).ι (scalarHomotopyComp f g)) (Q (dgCat C) (laws C)) ≪≫
    (scalarProjectiveComparison (f ≫ g)).symm

/-- Successive extensions compare with extension along the composite, by the
strict multiplication comparison on K-projectives. -/
def extensionComp (f : A ⟶ B) (g : B ⟶ C) :
    derivedExtension f ⋙ derivedExtension g ≅ derivedExtension (f ≫ g) :=
  cancelEquivalence (localizedProjectives A) (extensionCompAtProjectives f g)

set_option maxHeartbeats 800000 in
private theorem extensionCompAtProjectives_app (f : A ⟶ B) (g : B ⟶ C)
    (P : (proj A).FullSubcategory) :
    (extensionComp f g).hom.app ((localizedProjectives A).functor.obj P) ≫
        (scalarProjectiveComparison (f ≫ g)).hom.app P =
      (derivedExtension g).map ((scalarProjectiveComparison f).hom.app P) ≫
        (scalarProjectiveComparison g).hom.app ((scalarProjectives f).obj P) ≫
        localizeMap (baseChangeComp f g P.obj).hom := by
  unfold extensionComp
  rw [cancelEquivalence_on_image]
  let a := (derivedExtension g).map ((scalarProjectiveComparison f).hom.app P)
  let b := (scalarProjectiveComparison g).hom.app ((scalarProjectives f).obj P)
  let c := localizeMap (baseChangeComp f g P.obj).hom
  let δ := scalarProjectiveComparison (f ≫ g)
  change (a ≫ b ≫ c ≫ δ.inv.app P) ≫ δ.hom.app P = a ≫ b ≫ c
  rw [Category.assoc, Category.assoc]
  have hc : (c ≫ δ.inv.app P) ≫ δ.hom.app P = c :=
    (Category.assoc c _ _).trans
      ((congrArg (fun z => c ≫ z) (δ.inv_hom_id_app P)).trans (Category.comp_id c))
  exact congrArg (fun z => a ≫ b ≫ z) hc

set_option maxHeartbeats 800000 in
theorem extensionComp_onProjective (f : A ⟶ B) (g : B ⟶ C) (P : A.Module) (hP : IsKProjective P) :
    (extensionComp f g).hom.app (represented P) ≫
        ((scalarAdjunction (f ≫ g)).onProjective P hP).hom =
      (derivedExtension g).map ((scalarAdjunction f).onProjective P hP).hom ≫
        ((scalarAdjunction g).onProjective ((baseChange f).obj P) (baseChange_projective f P hP)).hom ≫
        localizeMap (baseChangeComp f g P).hom := by
  let PP : (proj A).FullSubcategory := ⟨P, hP⟩
  have e := extensionCompAtProjectives_app f g PP
  rw [scalarProjectiveComparison_app (f ≫ g) PP, scalarProjectiveComparison_app f PP,
    scalarProjectiveComparison_app g ((scalarProjectives f).obj PP)] at e
  exact e

end ScalarExtension

private def onFlatReplacements {P R M N : A.Module} (p : P ⟶ M) (r : R ⟶ N)
    (hP : KFlat P) (hR : KFlat R) (hp : IsQuasiIso p) (hr : IsQuasiIso r) :
    (derivedTensor A).obj (represented M, represented N) ≅ localizeTensor (P, R) :=
  (derivedTensor A).mapIso ((quasiIsoIso p hp).prod (quasiIsoIso r hr)).symm ≪≫ onFlatPair hP hR

section Specification

open _root_.Specs.DerivedFormalization.Affine.DerivedTensor
  (SemifreeIsFlat ProjectiveIsFlat HomotopyTensor NativeTensor NativeExtension
    DerivedTensorType derivedTensorValue)

/-- The tensor on the common localization, computed through its full
homotopy subcategory of K-projective modules. -/
def derivedTensorFromProjectives : DerivedTensorType.{u,v} := derivedTensorValue

theorem semifreeIsFlat : SemifreeIsFlat.{u,v} := by
  intro k _ _ T A h M hM
  exact (FlatFiltration.model_kFlat_iff T (h M)).2 (semiFree_kFlat hM)

theorem projectiveIsFlat : ProjectiveIsFlat.{u,v} := by
  intro k _ _ T A h M hM
  exact (FlatFiltration.model_kFlat_iff T (h M)).2 (kProjective_kFlat hM)

private def homotopyModel (f : A ⟶ B) :
    HomotopyTensor (moduleTensorModel.{u,v} k) f (laws A) (laws B) where
  functor := homotopyTensor f
  obj _ _ := rfl
  map_tmul {M M' N N'} g h := by
    refine ⟨(extension f N).map g ≫ mapSecond f M' h, ?_, ?_⟩
    · exact heq_of_eq (homotopyTensor_map f g h)
    · intro i j n e x y
      change ((mapSecond f M' h).app ()).f n
          ((((extension f N).map g).app ()).f n (pure f i j n e x y)) =
        pure f i j n e ((g.app ()).f i x) ((h.app ()).f j y)
      rw [map_first_pure, map_second_pure]

theorem nativeTensor : NativeTensor.{u,v} := by
  intro k _ _
  refine ⟨moduleTensorModel k, moduleTensor_formulas, ?_⟩
  intro A h
  refine ⟨homotopyModel (𝟙 A), kProjectiveLocalization_isEquivalence.{u,v,0} _ _, ?_⟩
  constructor
  · intro P R M N p r hP hR hp hr
    exact ⟨onReplacements p r hP hR hp hr⟩
  constructor
  · intro P R M N p r hP hR hp hr
    exact ⟨onFlatReplacements p r hP hR hp hr⟩
  · intro M N h
    rcases h with h | h
    · exact ⟨onFlatLeft h N⟩
    · exact ⟨onFlatRight M h⟩

theorem nativeExtension : NativeExtension.{u,v} := by
  intro k _ _
  refine ⟨moduleTensorModel k, moduleTensor_formulas, ?_⟩
  intro A B f hA hB
  have hd := Classical.choose_spec (scalarExtension_exact f)
  refine ⟨scalarModels f, scalarAdjunction f, baseChange_eq f, hd.1, hd.2.1, hd.2.2, ?_⟩
  intro P M p hP hp
  exact ⟨extensionOnFlatReplacement f p hP hp⟩

open _root_.Specs.DerivedFormalization.Affine.DerivedTensor
  (ScalarExtension NativeExtensionComposition)

private def scalarExtensionModel (f : A ⟶ B) :
    ScalarExtension (moduleTensorModel.{u,v} k) f (laws A) (laws B) :=
  let hd := Classical.choose_spec (scalarExtension_exact f)
  ⟨scalarModels f, scalarAdjunction f, baseChange_eq f, hd.1, hd.2.2⟩

private theorem scalarExtensionModel_onProjective_hom (f : A ⟶ B) (P : A.Module)
    (hP : IsKProjective P) :
    ((scalarExtensionModel f).onProjective P hP).hom =
      ((scalarAdjunction f).onProjective P hP).hom := by
  change ((scalarAdjunction f).onProjective P hP).hom ≫ 𝟙 _ = _
  exact Category.comp_id _

set_option maxHeartbeats 800000 in
theorem nativeExtensionComposition : NativeExtensionComposition.{u,v} := by
  intro k _ _
  refine ⟨moduleTensorModel k, moduleTensor_formulas, ?_⟩
  intro h
  refine ⟨fun f => scalarExtensionModel f, ?_⟩
  intro A B C f g
  refine ⟨NatIso.ofComponents (baseChangeComp f g) (fun p => baseChangeComp_natural f g p),
    extensionComp f g, ?_, ?_⟩
  · exact baseChangeComp_pure f g
  · intro P hP
    refine ⟨baseChange_projective f P hP, ?_⟩
    change (extensionComp f g).hom.app (represented P) ≫
        ((scalarExtensionModel (f ≫ g)).onProjective P hP).hom =
      (derivedExtension g).map ((scalarExtensionModel f).onProjective P hP).hom ≫
        ((scalarExtensionModel g).onProjective ((baseChange f).obj P)
          (baseChange_projective f P hP)).hom ≫ localizeMap (baseChangeComp f g P).hom
    rw [scalarExtensionModel_onProjective_hom (f ≫ g) P hP,
      scalarExtensionModel_onProjective_hom f P hP,
      scalarExtensionModel_onProjective_hom g ((baseChange f).obj P) (baseChange_projective f P hP)]
    exact extensionComp_onProjective f g P hP

end Specification

section Coefficients

open _root_.Specs.DerivedFormalization.Affine.DerivedTensor

/-- The transported cdga over the original field. -/
abbrev liftAlgebra : LiftAlgebraType.{u,v,t} :=
  _root_.Specs.DerivedFormalization.Affine.DerivedTensor.liftAlgebra

/-- The transported algebra map on the lifted homogeneous elements. -/
abbrev liftAlgebraMap : LiftAlgebraMapType.{u,v,t} :=
  _root_.Specs.DerivedFormalization.Affine.DerivedTensor.liftAlgebraMap

private def liftTensorDegree (f : A ⟶ B) (M : A.Module) (N : B.Module) (n : ℤ) :
    term (tensor f M N) n ≃ₗ[k]
      term (tensor (liftAlgebraMap.{u,v,t} f)
        ((liftInput.{u,v,t} A).obj M) ((liftInput.{u,v,t} B).obj N)) n :=
  DGBimodule.tensorLiftEquiv.{u,v,0,0,v,t} (signedBimodule f N) M () n

private theorem liftTensorDegree_pure (f : A ⟶ B) (M : A.Module) (N : B.Module)
    (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    liftTensorDegree.{u,v,t} f M N n (pure f i j n h x y) =
      pure (liftAlgebraMap.{u,v,t} f)
        (M := (liftInput.{u,v,t} A).obj M) (N := (liftInput.{u,v,t} B).obj N)
        i j n h (ULift.up x) (ULift.up y) :=
  DGBimodule.tensorLiftEquiv_tmul.{u,v,0,0,v,t} (signedBimodule f N) M () () i j n h x y

private def isoOfDegreeEquivs {M N : A.Module} (E : ∀ n, term M n ≃ₗ[k] term N n)
    (hd : ∀ n (x : term M n), differential N n (E n x) = E (n+1) (differential M n x))
    (ha : ∀ i j n (h : i+j=n) (x : term M i) (a : A.complex.X j),
      E n (act M i j n h x a) = act N i j n h (E i x) a) : M ≅ N where
  hom := homOfDegrees (fun n => (E n).toLinearMap) hd ha
  inv := homOfDegrees (fun n => (E n).symm.toLinearMap)
    (by
      intro n x
      apply (E (n+1)).injective
      change E (n+1) (differential M n ((E n).symm x)) =
        E (n+1) ((E (n+1)).symm (differential N n x))
      rw [← hd, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
    (by
      intro i j n h x a
      apply (E n).injective
      change E n ((E n).symm (act N i j n h x a)) =
        E n (act M i j n h ((E i).symm x) a)
      rw [LinearEquiv.apply_symm_apply, ha, LinearEquiv.apply_symm_apply])
  hom_inv_id := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    exact LinearMap.ext (E n).symm_apply_apply
  inv_hom_id := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    exact LinearMap.ext (E n).apply_symm_apply

set_option maxHeartbeats 800000 in
private def liftTensorIso (f : A ⟶ B) (M : A.Module) (N : B.Module) :
    (liftInput.{u,v,t} B).obj (tensor f M N) ≅
      tensor (liftAlgebraMap.{u,v,t} f) ((liftInput.{u,v,t} A).obj M) ((liftInput.{u,v,t} B).obj N) := by
  let S := signedBimodule f N
  refine isoOfDegreeEquivs (A := liftAlgebra.{u,v,t} B)
    (fun n => ULift.moduleEquiv ≪≫ₗ liftTensorDegree.{u,v,t} f M N n) ?_ ?_
  · intro n z
    exact (DGBimodule.tensorLiftEquiv_d.{u,v,0,0,v,t} S M () n z.down).symm
  · intro i j n h z a
    exact DGBimodule.tensorLiftEquiv_act.{u,v,0,0,v,t} S M
      (b := ()) (c := ()) i j n h z.down a.down

private theorem liftTensorIso_pure (f : A ⟶ B) (M : A.Module) (N : B.Module)
    (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    φ[(liftTensorIso.{u,v,t} f M N).hom,n] (ULift.up (pure f i j n h x y)) =
      pure (liftAlgebraMap.{u,v,t} f)
        (M := (liftInput.{u,v,t} A).obj M) (N := (liftInput.{u,v,t} B).obj N)
        i j n h (ULift.up x) (ULift.up y) :=
  liftTensorDegree_pure.{u,v,t} f M N i j n h x y

set_option maxHeartbeats 850000 in
private theorem liftTensor_natural (f : A ⟶ B) (N : B.Module) {L M : A.Module} (p : L ⟶ M) :
    (liftInput.{u,v,t} B).map ((extension f N).map p) ≫ (liftTensorIso.{u,v,t} f M N).hom =
      (liftTensorIso.{u,v,t} f L N).hom ≫
        (extension (liftAlgebraMap.{u,v,t} f) ((liftInput.{u,v,t} B).obj N)).map
          ((liftInput.{u,v,t} A).map p) := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact DGBimodule.tensorLiftEquiv_map.{u,v,0,0,v,t} (signedBimodule f N) p () n z.down

/-- Comparing the actual homogeneous tensors under coefficient enlargement
gives a natural strict isomorphism. -/
def liftTensorComparison (f : A ⟶ B) (N : B.Module) :
    extension f N ⋙ liftInput.{u,v,t} B ≅
      liftInput.{u,v,t} A ⋙
        extension (liftAlgebraMap.{u,v,t} f) ((liftInput.{u,v,t} B).obj N) :=
  NatIso.ofComponents (fun M => liftTensorIso.{u,v,t} f M N)
    (fun p => liftTensor_natural.{u,v,t} f N p)

theorem coefficientTensor : CoefficientTensor.{u,v,t} := by
  intro k _ _
  refine ⟨moduleTensorModel k, moduleTensorModel k, moduleTensor_formulas, moduleTensor_formulas, ?_⟩
  intro A B f N
  exact ⟨liftTensorComparison.{u,v,t} f N, fun M => liftTensorIso_pure.{u,v,t} f M N⟩

theorem liftNonpositive : LiftNonpositive.{u,v,t} := by
  intro k _ _ A h n hn
  have := h n hn
  exact ⟨fun x y => ULift.ext (Subsingleton.elim x.down y.down)⟩

theorem adequateNativeLocalization : AdequateNativeLocalization.{u,v} := by
  intro k _ _ A h h'
  obtain ⟨H, _, _, _, E, e⟩ :=
    _root_.DerivedFormalization.DG.AmbientDerived.nativeLocalizationComparison.{u,v,0,v}
      (dgCat A) h h'
  exact ⟨H, E, e⟩

private abbrev ambientHomotopyInput (A : CommDGAlgebra.{u,v} k) :=
  _root_.DerivedFormalization.DG.AmbientDerived.homotopyInput.{u,v,0,max v t} (dgCat A)

/-- The canonical input functor from the native localization to the common bound. -/
abbrev ambientInput (A : CommDGAlgebra.{u,v} k) :=
  _root_.DerivedFormalization.DG.AmbientDerived.derivedInput.{u,v,0,max v t} (dgCat A)

private abbrev ambientInputSquare (A : CommDGAlgebra.{u,v} k) :=
  _root_.DerivedFormalization.DG.AmbientDerived.inputSquare.{u,v,0,max v t} (dgCat A)

private theorem projective_lift (P : A.Module) (hP : IsKProjective P) :
    IsKProjective ((liftInput.{u,v,t} A).obj P) :=
  (_root_.DerivedFormalization.DG.DerivedCoefficientLift.nativeDerivedCoefficientTransition.{u,v,0,max v t}
    (dgCat A) (laws A) (laws (liftAlgebra.{u,v,t} A))).2 P hP

private def liftProjectives (A : CommDGAlgebra.{u,v} k) :
    (proj A).FullSubcategory ⥤ (proj (liftAlgebra.{u,v,t} A)).FullSubcategory :=
  (proj (liftAlgebra.{u,v,t} A)).lift ((proj A).ι ⋙ ambientHomotopyInput.{u,v,t} A)
    (fun P => projective_lift P.obj P.property)

private def liftProjectivesComparison (A : CommDGAlgebra.{u,v} k) :
    (localizedProjectives A).functor ⋙ ambientInput.{u,v,t} A ≅
      liftProjectives.{u,v,t} A ⋙ (localizedProjectives (liftAlgebra.{u,v,t} A)).functor :=
  Functor.isoWhiskerLeft (proj A).ι (ambientInputSquare.{u,v,t} A)

open _root_.DerivedFormalization.DG.CoefficientLift (homotopyLift_map_class)

set_option maxHeartbeats 1000000 in
private def scalarHomotopyLiftComp (f : A ⟶ B) :
    scalarHomotopy f ⋙ ambientHomotopyInput.{u,v,t} B ≅
      ambientHomotopyInput.{u,v,t} A ⋙ scalarHomotopy (liftAlgebraMap.{u,v,t} f) :=
  NatIso.ofComponents
    (fun M => (toHomotopyCategory (dgCat (liftAlgebra.{u,v,t} B))).mapIso
      (liftTensorIso.{u,v,t} f M (regular B)))
    (by
      intro M N g
      obtain ⟨p, rfl⟩ := homotopyClass_surjective g
      let f' := liftAlgebraMap.{u,v,t} f
      let I := liftInput.{u,v,t} A
      let J := liftInput.{u,v,t} B
      let F := toHomotopyCategory (dgCat (liftAlgebra.{u,v,t} B))
      change (ambientHomotopyInput.{u,v,t} B).map ((scalarHomotopy f).map (homotopyClass p)) ≫
        F.map (liftTensorIso.{u,v,t} f N (regular B)).hom =
        F.map (liftTensorIso.{u,v,t} f M (regular B)).hom ≫
          (scalarHomotopy f').map ((ambientHomotopyInput.{u,v,t} A).map (homotopyClass p))
      rw [scalarHomotopy_map f p]
      have hb : (ambientHomotopyInput.{u,v,t} B).map
          (homotopyClass ((baseChange f).map p)) = homotopyClass (J.map ((baseChange f).map p)) :=
        homotopyLift_map_class ((baseChange f).map p)
      have ha : (ambientHomotopyInput.{u,v,t} A).map (homotopyClass p) =
          homotopyClass (I.map p) := homotopyLift_map_class p
      rw [hb, ha, scalarHomotopy_map f' (I.map p)]
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← F.map_comp, ← F.map_comp]
      exact congrArg F.map (liftTensor_natural.{u,v,t} f (regular B) p))

/-- Paste the two ways around the square on projective representatives and
transfer the comparison along localization. -/
private def compareLocalizedComposites
    {P Q Q' R X Y Y' Z : Type*} [Category* P] [Category* Q] [Category* Q']
    [Category* R] [Category* X] [Category* Y] [Category* Y'] [Category* Z]
    (E : P ≌ X) {L : Q ⥤ Y} {L' : Q' ⥤ Y'} {V : R ⥤ Z}
    {F : X ⥤ Y} {G : Y ⥤ Z} {F' : X ⥤ Y'} {G' : Y' ⥤ Z}
    {H : P ⥤ Q} {J : Q ⥤ R} {H' : P ⥤ Q'} {J' : Q' ⥤ R}
    (a : E.functor ⋙ F ≅ H ⋙ L) (b : L ⋙ G ≅ J ⋙ V)
    (c : E.functor ⋙ F' ≅ H' ⋙ L') (d : L' ⋙ G' ≅ J' ⋙ V)
    (e : H ⋙ J ≅ H' ⋙ J') : F ⋙ G ≅ F' ⋙ G' :=
  let s : CatCommSq E.functor (H ⋙ J) (F ⋙ G) V := CatCommSq.vComp' ⟨a⟩ ⟨b⟩
  let s' : CatCommSq E.functor (H' ⋙ J') (F' ⋙ G') V := CatCommSq.vComp' ⟨c⟩ ⟨d⟩
  cancelEquivalence E (s.iso ≪≫ Functor.isoWhiskerRight e V ≪≫ s'.iso.symm)

@[instance_reducible]
private def scalarProjectiveSquare (f : A ⟶ B) :
    CatCommSq (scalarProjectives f) (proj A).ι (proj B).ι (scalarHomotopy f) :=
  ⟨Iso.refl _⟩

@[instance_reducible]
private def liftProjectiveSquare (A : CommDGAlgebra.{u,v} k) :
    CatCommSq (liftProjectives.{u,v,t} A) (proj A).ι (proj (liftAlgebra.{u,v,t} A)).ι
      (ambientHomotopyInput.{u,v,t} A) :=
  ⟨Iso.refl _⟩

set_option maxHeartbeats 600000 in
private def scalarProjectiveLiftComp (f : A ⟶ B) :
    scalarProjectives f ⋙ liftProjectives.{u,v,t} B ≅
      liftProjectives.{u,v,t} A ⋙ scalarProjectives (liftAlgebraMap.{u,v,t} f) := by
  let f' := liftAlgebraMap.{u,v,t} f
  let b := CatCommSq.hComp' (scalarProjectiveSquare f) (liftProjectiveSquare.{u,v,t} B)
  let a := CatCommSq.hComp' (liftProjectiveSquare.{u,v,t} A) (scalarProjectiveSquare f')
  let e := Functor.isoWhiskerLeft (proj A).ι (scalarHomotopyLiftComp.{u,v,t} f)
  exact ((proj (liftAlgebra.{u,v,t} B)).fullyFaithfulι.whiskeringRight _).preimageIso
    (b.iso ≪≫ e ≪≫ a.iso.symm)

/-- Derived extension of scalars commutes with placing the diagram at a
common bound, via the strict comparison on projectives. -/
def extensionCoefficientComparison (f : A ⟶ B) :
    derivedExtension f ⋙ ambientInput.{u,v,t} B ≅
      ambientInput.{u,v,t} A ⋙ derivedExtension (liftAlgebraMap.{u,v,t} f) :=
  compareLocalizedComposites (localizedProjectives A)
    (scalarProjectiveComparison f) (liftProjectivesComparison.{u,v,t} B)
    (liftProjectivesComparison.{u,v,t} A) (scalarProjectiveComparison (liftAlgebraMap.{u,v,t} f))
    (scalarProjectiveLiftComp.{u,v,t} f)

set_option maxHeartbeats 850000 in
private theorem liftTensor_natural_second (f : A ⟶ B) (M : A.Module) {L N : B.Module}
    (p : L ⟶ N) :
    (liftInput.{u,v,t} B).map (mapSecond f M p) ≫ (liftTensorIso.{u,v,t} f M N).hom =
      (liftTensorIso.{u,v,t} f M L).hom ≫
        mapSecond (liftAlgebraMap.{u,v,t} f) ((liftInput.{u,v,t} A).obj M)
          ((liftInput.{u,v,t} B).map p) := by
  let I := liftInput.{u,v,t} A
  let J := liftInput.{u,v,t} B
  let f' := liftAlgebraMap.{u,v,t} f
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let E := (liftTensorDegree.{u,v,t} f M L n).toLinearMap
  let E' := (liftTensorDegree.{u,v,t} f M N n).toLinearMap
  let q := mapSecond f M p
  let q' := mapSecond f' (I.obj M) (J.map p)
  have e : E'.comp φ[q,n].hom = φ[q',n].hom.comp E := by
    apply pure_ext (f := f)
    intro i j h x y
    change liftTensorDegree.{u,v,t} f M N n (φ[q,n] (pure f i j n h x y)) =
      φ[q',n] (liftTensorDegree.{u,v,t} f M L n (pure f i j n h x y))
    rw [show φ[q,n] (pure f i j n h x y) = _ from map_second_pure f M p i j n h x y,
      liftTensorDegree_pure, liftTensorDegree_pure]
    exact (map_second_pure f' (I.obj M) (J.map p) i j n h (ULift.up x) (ULift.up y)).symm
  exact LinearMap.congr_fun e z.down

set_option maxHeartbeats 950000 in
private def liftStrictTensor (f : A ⟶ B) :
    strictTensor f ⋙ liftInput.{u,v,t} B ≅
      (liftInput.{u,v,t} A).prod (liftInput.{u,v,t} B) ⋙ strictTensor (liftAlgebraMap.{u,v,t} f) :=
  NatIso.ofComponents
    (fun X => liftTensorIso.{u,v,t} f X.1 X.2)
    (by
      intro X Y g
      let I := liftInput.{u,v,t} A
      let J := liftInput.{u,v,t} B
      let f' := liftAlgebraMap.{u,v,t} f
      let a := (extension f X.2).map g.1
      let b := mapSecond f Y.1 g.2
      let a' := (extension f' (J.obj X.2)).map (I.map g.1)
      let b' := mapSecond f' (I.obj Y.1) (J.map g.2)
      let eX := (liftTensorIso.{u,v,t} f X.1 X.2).hom
      let eZ := (liftTensorIso.{u,v,t} f Y.1 X.2).hom
      let eY := (liftTensorIso.{u,v,t} f Y.1 Y.2).hom
      change J.map (a ≫ b) ≫ eY = eX ≫ a' ≫ b'
      have e₁ : J.map a ≫ eZ = eX ≫ a' := liftTensor_natural.{u,v,t} f X.2 g.1
      have e₂ : J.map b ≫ eY = eZ ≫ b' := liftTensor_natural_second.{u,v,t} f Y.1 g.2
      rw [J.map_comp, Category.assoc, e₂, ← Category.assoc (J.map a), e₁, Category.assoc])

open private commute_heq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleCoefficientCompatibility

set_option maxHeartbeats 800000 in
@[instance_reducible]
private def tensorHomotopySquare (f : A ⟶ B) :
    CatCommSq (prodQuotient A B) (strictTensor f) (homotopyTensor f)
      (toHomotopyCategory (dgCat B)) := by
  let F := prodQuotient A B ⋙ homotopyTensor f
  let G := tensorClass f
  let h (X : A.Module × B.Module) : F.obj X = G.obj X := rfl
  have hm (X Y : A.Module × B.Module) (g : X ⟶ Y) :
      HEq (F.map g) (G.map g) := heq_of_eq (tensorClassMap_on_strict f g)
  exact ⟨NatIso.ofComponents (F := F) (G := G) (fun X => eqToIso (h X))
    (fun {X Y} g => commute_heq (C := K (dgCat B)) (h X) (h Y) (hm X Y g))⟩

set_option maxHeartbeats 650000 in
@[instance_reducible]
private def liftHomotopySquare (A : CommDGAlgebra.{u,v} k) :
    CatCommSq (toHomotopyCategory (dgCat A)) (liftInput.{u,v,t} A)
      (ambientHomotopyInput.{u,v,t} A) (toHomotopyCategory (dgCat (liftAlgebra.{u,v,t} A))) := by
  let F := toHomotopyCategory (dgCat A) ⋙ ambientHomotopyInput.{u,v,t} A
  let G := liftInput.{u,v,t} A ⋙ toHomotopyCategory (dgCat (liftAlgebra.{u,v,t} A))
  let e (X : A.Module) : F.obj X ≅ G.obj X := Iso.refl (G.obj X)
  refine ⟨NatIso.ofComponents e ?_⟩
  intro X Y g
  change F.map g ≫ 𝟙 (G.obj Y) = 𝟙 (F.obj X) ≫ G.map g
  exact (Category.comp_id (F.map g)).trans
    ((homotopyLift_map_class.{u,v,0,max v t} g).trans (Category.id_comp (G.map g)).symm)

@[instance_reducible]
private def productLiftHomotopySquare (A B : CommDGAlgebra.{u,v} k) :
    CatCommSq (prodQuotient A B) ((liftInput.{u,v,t} A).prod (liftInput.{u,v,t} B))
      ((ambientHomotopyInput.{u,v,t} A).prod (ambientHomotopyInput.{u,v,t} B))
      (prodQuotient (liftAlgebra.{u,v,t} A) (liftAlgebra.{u,v,t} B)) :=
  ⟨NatIso.prod (liftHomotopySquare.{u,v,t} A).iso (liftHomotopySquare.{u,v,t} B).iso⟩

private def descendTensorIso {X : Type*} [Category* X]
    (F G : K (dgCat A) × K (dgCat B) ⥤ X)
    (e : prodQuotient A B ⋙ F ≅ prodQuotient A B ⋙ G) : F ≅ G :=
  NatIso.ofComponents (fun P => e.app (show A.Module × B.Module from P)) (by
    intro P R g
    let g₀ := tensorRepresentative (X := P) (Y := R) g
    have hg : (prodQuotient A B).map g₀ = g := tensorRepresentative_class g
    have hn : F.map ((prodQuotient A B).map g₀) ≫ e.hom.app R =
        e.hom.app P ≫ G.map ((prodQuotient A B).map g₀) := e.hom.naturality g₀
    rw [hg] at hn
    exact hn)

set_option maxHeartbeats 700000 in
private def liftHomotopyTensor (f : A ⟶ B) :
    homotopyTensor f ⋙ ambientHomotopyInput.{u,v,t} B ≅
      (ambientHomotopyInput.{u,v,t} A).prod (ambientHomotopyInput.{u,v,t} B) ⋙
        homotopyTensor (liftAlgebraMap.{u,v,t} f) := by
  let f' := liftAlgebraMap.{u,v,t} f
  let HA := ambientHomotopyInput.{u,v,t} A
  let HB := ambientHomotopyInput.{u,v,t} B
  let H := toHomotopyCategory (dgCat (liftAlgebra.{u,v,t} B))
  let l := CatCommSq.vComp' (tensorHomotopySquare f) (liftHomotopySquare.{u,v,t} B)
  let r := CatCommSq.vComp' (productLiftHomotopySquare.{u,v,t} A B) (tensorHomotopySquare f')
  let e : prodQuotient A B ⋙ (homotopyTensor f ⋙ HB) ≅
      prodQuotient A B ⋙ (HA.prod HB ⋙ homotopyTensor f') :=
    l.iso ≪≫ Functor.isoWhiskerRight (liftStrictTensor.{u,v,t} f) H ≪≫ r.iso.symm
  exact descendTensorIso (homotopyTensor f ⋙ HB) (HA.prod HB ⋙ homotopyTensor f') e

private def liftHomotopyOver (A : CommDGAlgebra.{u,v} k) :
    homotopyTensor (𝟙 A) ⋙ ambientHomotopyInput.{u,v,t} A ≅
      (ambientHomotopyInput.{u,v,t} A).prod (ambientHomotopyInput.{u,v,t} A) ⋙
        homotopyTensor (𝟙 (liftAlgebra.{u,v,t} A)) :=
  liftHomotopyTensor.{u,v,t} (𝟙 A) ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (congrArg homotopyTensor
      ((liftAlgebraFunctor.{u,v,t} k).map_id A)))

private theorem tensor_projective {M N : A.Module} (hM : IsKProjective M)
    (hN : IsKProjective N) : IsKProjective (over M N) := by
  let T := signedBimodule (𝟙 A) N
  exact DGBimodule.tensorPreservesKProjectives.{u,v,0,0}
    (DGBimodule.tensorModel T) (DGBimodule.internalHomModel T) (DGBimodule.curryIso.{u,v,0,0} T)
    (fun _ => hN) M hM

private def tensorProjectives (A : CommDGAlgebra.{u,v} k) :
    (proj A).FullSubcategory × (proj A).FullSubcategory ⥤ (proj A).FullSubcategory :=
  (proj A).lift (((proj A).ι.prod (proj A).ι) ⋙ homotopyTensor (𝟙 A))
    (fun P => tensor_projective P.1.property P.2.property)

private def tensorProjectiveComparison (A : CommDGAlgebra.{u,v} k) :
    ((localizedProjectives A).functor.prod (localizedProjectives A).functor) ⋙ derivedTensor A ≅
      tensorProjectives A ⋙ (localizedProjectives A).functor :=
  let e := Functor.isoWhiskerRight (localizedProjectives A).unitIso.symm (proj A).ι
  Functor.isoWhiskerRight (NatIso.prod e e) (homotopyTensor (𝟙 A) ⋙ Q (dgCat A) (laws A))

@[instance_reducible]
private def tensorProjectiveSquare (A : CommDGAlgebra.{u,v} k) :
    CatCommSq (tensorProjectives A) ((proj A).ι.prod (proj A).ι) (proj A).ι
      (homotopyTensor (𝟙 A)) :=
  ⟨Iso.refl _⟩

@[instance_reducible]
private def prodLiftProjectiveSquare (A : CommDGAlgebra.{u,v} k) :
    CatCommSq ((liftProjectives.{u,v,t} A).prod (liftProjectives.{u,v,t} A))
      ((proj A).ι.prod (proj A).ι)
      ((proj (liftAlgebra.{u,v,t} A)).ι.prod (proj (liftAlgebra.{u,v,t} A)).ι)
      ((ambientHomotopyInput.{u,v,t} A).prod (ambientHomotopyInput.{u,v,t} A)) :=
  let e := (liftProjectiveSquare.{u,v,t} A).iso
  ⟨NatIso.prod e e⟩

set_option maxHeartbeats 700000 in
private def tensorProjectiveLiftComp (A : CommDGAlgebra.{u,v} k) :
    tensorProjectives A ⋙ liftProjectives.{u,v,t} A ≅
      (liftProjectives.{u,v,t} A).prod (liftProjectives.{u,v,t} A) ⋙
        tensorProjectives (liftAlgebra.{u,v,t} A) := by
  let A' := liftAlgebra.{u,v,t} A
  let b := CatCommSq.hComp' (tensorProjectiveSquare A) (liftProjectiveSquare.{u,v,t} A)
  let a := CatCommSq.hComp' (prodLiftProjectiveSquare.{u,v,t} A) (tensorProjectiveSquare A')
  let e := Functor.isoWhiskerLeft ((proj A).ι.prod (proj A).ι) (liftHomotopyOver.{u,v,t} A)
  exact ((proj A').fullyFaithfulι.whiskeringRight _).preimageIso (b.iso ≪≫ e ≪≫ a.iso.symm)

private def productCompIso {V W X Y Z U : Type*} [Category* V] [Category* W]
    [Category* X] [Category* Y] [Category* Z] [Category* U]
    (F : V ⥤ X) (G : W ⥤ Y) (H : X ⥤ Z) (I : Y ⥤ U) :
    F.prod G ⋙ H.prod I ≅ (F ⋙ H).prod (G ⋙ I) := Iso.refl _

set_option maxHeartbeats 850000 in
/-- Derived tensor commutes with transport of a diagram to the common bound. -/
def tensorCoefficientComparison (A : CommDGAlgebra.{u,v} k) :
    derivedTensor A ⋙ ambientInput.{u,v,t} A ≅
      (ambientInput.{u,v,t} A).prod (ambientInput.{u,v,t} A) ⋙ derivedTensor (liftAlgebra.{u,v,t} A) := by
  let A' := liftAlgebra.{u,v,t} A
  let E := (localizedProjectives A).prod (localizedProjectives A)
  let E' := (localizedProjectives A').prod (localizedProjectives A')
  let L := (localizedProjectives A).functor
  let L' := (localizedProjectives A').functor
  let J := liftProjectives.{u,v,t} A
  let I := ambientInput.{u,v,t} A
  let e := liftProjectivesComparison.{u,v,t} A
  have e₂ : E.functor ⋙ I.prod I ≅ J.prod J ⋙ E'.functor :=
    productCompIso L L I I ≪≫ NatIso.prod e e ≪≫ (productCompIso J J L' L').symm
  exact compareLocalizedComposites E (tensorProjectiveComparison A) e e₂
    (tensorProjectiveComparison A') (tensorProjectiveLiftComp.{u,v,t} A)

private def ambientDescent (A : CommDGAlgebra.{u,v} k) :
    DerivedCoefficientLift.Descent (laws A) (laws (liftAlgebra.{u,v,t} A)) (liftInput.{u,v,t} A) :=
  ⟨ambientHomotopyInput.{u,v,t} A, ambientInput.{u,v,t} A, fun _ => rfl,
    fun f => heq_of_eq (homotopyLift_map_class.{u,v,0,max v t} f),
    ambientInputSquare.{u,v,t} A⟩

private def tensorResolution (A : CommDGAlgebra.{u,v} k) :
    TensorResolution (moduleTensorModel.{u,v} k) A (laws A) :=
  ⟨homotopyModel (𝟙 A), kProjectiveLocalization_isEquivalence.{u,v,0} (dgCat A) (laws A)⟩

theorem coefficientDerived : CoefficientDerived.{u,v,t} := by
  intro k _ _
  refine ⟨moduleTensorModel k, moduleTensorModel k, moduleTensor_formulas, moduleTensor_formulas, ?_⟩
  intro h h'
  refine ⟨tensorResolution, tensorResolution, (fun f => scalarExtensionModel f),
    (fun f => scalarExtensionModel f), ambientDescent, ?_, ?_⟩
  · intro A
    exact ⟨tensorCoefficientComparison.{u,v,t} A⟩
  · intro A B f
    exact ⟨extensionCoefficientComparison.{u,v,t} f⟩

end Coefficients

end
end DerivedFormalization.Affine.DerivedTensor
