import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.PretriangulatedHull
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.FiniteCellConstructions
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoproducts
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactFiniteCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

set_option linter.style.haveILetI false
open Specs.DerivedFormalization.DG

universe u v w j t

namespace DerivedFormalization.RightDGModule

open Basic (classOf cycleId cycleComp cyclesZero boundariesZero h0Hom h0Map)
open FiniteCellConstructions (pretr pretrInclusion pretrRepresentable WrittenObject writtenModule
  WrittenObjectsLaws CanonicalFiniteCellLaws LiftedHullLaws finiteSum zeroModule FiniteIndex)
open PretriangulatedHull (HullTheorem RepresentedUpToHomotopy IsWrittenYoneda liftCycle
  InheritsTriangulation FiniteConstructionsInDerived perfect)
open Derived (HomotopyCategoryLaws)
open DG.CoefficientLift (homotopyLift homotopyLiftFullyFaithful homotopyLift_map_class
  shiftIso coneIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true in
private theorem inheritsTriangulation_of_essImage {C D : Type*} [Category* C] [Category* D]
    [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (F : C ⥤ D) (hF : F.FullyFaithful) (hP : F.essImage.IsTriangulated) :
    InheritsTriangulation F := by
  classical
  letI := hP
  letI := hF.full
  letI := hF.faithful
  let P := F.essImage
  have hz : ∃ X : C, IsZero (F.obj X) := by
    obtain ⟨Z, hZ, ⟨X, ⟨e⟩⟩⟩ := hP.toContainsZero.exists_zero
    exact ⟨X, hZ.of_iso e⟩
  letI AC := Preadditive.ofFullyFaithful hF
  letI : F.Additive := hF.additive_ofFullyFaithful
  letI ZC : HasZeroObject C := (IsZero.of_full_of_faithful_of_isZero F _ hz.choose_spec).hasZeroObject
  let S (n : ℤ) := Functor.essImage.liftFunctor (F ⋙ shiftFunctor D n) F
    (fun X => P.le_shift n _ ⟨X, ⟨Iso.refl _⟩⟩)
  let eS (n : ℤ) : S n ⋙ F ≅ F ⋙ shiftFunctor D n :=
    Functor.essImage.liftFunctorCompIso _ _ _
  letI SC := hF.hasShift S eS
  letI eF := Functor.CommShift.ofHasShiftOfFullyFaithful hF S eS
  letI LC (n : ℤ) : (shiftFunctor C n).Additive := by
    letI : (S n ⋙ F).Additive := (Functor.additive_iff_of_iso (eS n)).2 inferInstance
    exact Functor.additive_of_comp_faithful (S n) F
  letI TC : Pretriangulated C := {
    distinguishedTriangles := F.mapTriangle.obj ⁻¹' (distTriang D)
    isomorphic_distinguished := fun T hT T' e =>
      isomorphic_distinguished _ hT _ (F.mapTriangle.mapIso e)
    contractible_distinguished := fun X =>
      isomorphic_distinguished _ (contractible_distinguished (F.obj X)) _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) F.mapZeroObject
          (by simp [Functor.mapTriangle, contractibleTriangle])
          (by simp [Functor.mapTriangle, contractibleTriangle])
          (by simp [Functor.mapTriangle, contractibleTriangle]))
    distinguished_cocone_triangle := fun {X Y} f => by
      obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (F.map f)
      obtain ⟨W, ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃ (Triangle.mk (F.map f) g h) hT
        ⟨X, ⟨Iso.refl _⟩⟩ ⟨Y, ⟨Iso.refl _⟩⟩
      refine ⟨W, hF.preimage (g ≫ e.inv),
        hF.preimage (e.hom ≫ h ≫ (F.commShiftIso (1 : ℤ)).inv.app X), ?_⟩
      change F.mapTriangle.obj (Triangle.mk _ _ _) ∈ distTriang D
      exact isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
          (by simp [Functor.mapTriangle])
          (by simp [Functor.mapTriangle, hF.map_preimage])
          (by simp [Functor.mapTriangle, hF.map_preimage]))
    rotate_distinguished_triangle := fun T =>
      (rotate_distinguished_triangle (F.mapTriangle.obj T)).trans
        (distinguished_iff_of_iso (F.mapTriangleRotateIso.app T))
    complete_distinguished_triangle_morphism := fun T₁ T₂ h₁ h₂ a b hab => by
      obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism
        (F.mapTriangle.obj T₁) (F.mapTriangle.obj T₂) h₁ h₂ (F.map a) (F.map b)
        (by simpa using F.congr_map hab)
      refine ⟨hF.preimage c, ⟨hF.map_injective ?_, hF.map_injective ?_⟩⟩
      · simpa [Functor.mapTriangle, Functor.map_comp, hF.map_preimage] using hc₁
      · rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app T₂.obj₁)]
        simpa [Functor.mapTriangle, Functor.map_comp, Category.assoc, hF.map_preimage,
          F.commShiftIso_hom_naturality a (1 : ℤ)] using hc₂ }
  letI : F.IsTriangulated := ⟨fun _ hT => hT⟩
  exact ⟨SC, AC, ZC, LC, eF, TC,
    IsTriangulated.of_fully_faithful_triangulated_functor F, inferInstance, inferInstance,
    fun _ => Iff.rfl⟩

section Cohomology

variable {k : Type u} [CommRing k]
variable {C : ModuleCochain.{u,v} k} {C' : ModuleCochain.{u,w} k}

/-- Transport cycles and boundaries across a degreewise linear comparison. -/
private def cycleEquiv (e : ∀ i, C.X i ≃ₗ[k] C'.X i)
    (comm : ∀ i q x, e q (C.d i q x) = C'.d i q (e i x)) :
    cyclesZero C ≃ₗ[k] cyclesZero C' where
  toFun x := ⟨e 0 x.val, by
    change C'.d 0 1 (e 0 x.val) = 0
    have hx : C.d 0 1 x.val = 0 := x.property
    rw [← comm, hx, map_zero]⟩
  invFun y := ⟨(e 0).symm y.val, (e 1).injective (by
    change e 1 (C.d 0 1 ((e 0).symm y.val)) = e 1 0
    rw [comm, LinearEquiv.apply_symm_apply, map_zero]
    exact y.property)⟩
  left_inv x := Subtype.ext ((e 0).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((e 0).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((e 0).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((e 0).map_smul r x.val)

private def cohomologyEquiv (e : ∀ i, C.X i ≃ₗ[k] C'.X i)
    (comm : ∀ i q x, e q (C.d i q x) = C'.d i q (e i x)) :
    h0Hom C ≃ₗ[k] h0Hom C' := by
  refine Submodule.Quotient.equiv _ _ (cycleEquiv e comm) ?_
  ext z
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e (-1) x, Subtype.ext (comm (-1) 0 x).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(Basic.zeroShort C).moduleCatToCycles ((e (-1)).symm y), ⟨_, rfl⟩, Subtype.ext ?_⟩
    change e 0 (C.d (-1) 0 ((e (-1)).symm y)) = C'.d (-1) 0 y
    rw [comm, LinearEquiv.apply_symm_apply]

private theorem cohomologyEquiv_class (e : ∀ i, C.X i ≃ₗ[k] C'.X i)
    (comm : ∀ i q x, e q (C.d i q x) = C'.d i q (e i x)) (x : cyclesZero C) :
    cohomologyEquiv e comm (classOf x) = classOf (cycleEquiv e comm x) := rfl

end Cohomology

section OriginalYoneda

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

private def h0LiftEquiv (a b : A.Obj) : h0Hom (A.hom a b) ≃ₗ[k]
    h0Hom ((Yoneda.liftCategory A).hom a b) :=
  cohomologyEquiv (fun _ => ULift.moduleEquiv.symm) (fun _ _ _ => rfl)

private theorem h0LiftEquiv_class {a b : A.Obj} (f : cyclesZero (A.hom a b)) :
    h0LiftEquiv a b (classOf f) = classOf (liftCycle f) := rfl

private def h0Lift (A : DGCategoryModel.{u,v,w} k) :
    DGCategory.H0 A ⥤ DGCategory.H0 (Yoneda.liftCategory A) where
  obj a := a
  map {a b} := h0LiftEquiv a b
  map_id a := rfl
  map_comp {a b c} f g := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ g
    change h0LiftEquiv a c (Basic.h0Comp A (classOf g) (classOf f)) =
      Basic.h0Comp (Yoneda.liftCategory A) (h0LiftEquiv b c (classOf g))
        (h0LiftEquiv a b (classOf f))
    rw [DGCategory.h0Comp_mk A, h0LiftEquiv_class, h0LiftEquiv_class, h0LiftEquiv_class,
      DGCategory.h0Comp_mk]
    rfl

private theorem h0_map_bijective_of_iso {B : DGCategoryModel.{u,v,w'} k}
    (F : DGFunctorModel A B) {a b : A.Obj} [IsIso (F.map a b)] :
    Function.Bijective ((DGFunctor.H0 F).map (X := a) (Y := b)) := by
  let e := asIso (F.map a b)
  let φ (i : ℤ) := (HomologicalComplex.eval _ _ i |>.mapIso e).toLinearEquiv
  have hc i q x : φ q ((A.hom a b).d i q x) =
      (B.hom (F.obj a) (F.obj b)).d i q (φ i x) := by
    exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((F.map a b).comm i q)) x).symm
  have h : ((DGFunctor.H0 F).map (X := a) (Y := b)) =
      (cohomologyEquiv φ hc : _ → _) := by
    funext f
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    exact (DGFunctor.h0Map_mk F f).trans (cohomologyEquiv_class φ hc f).symm
  rw [h]
  exact (cohomologyEquiv φ hc).bijective

private def originalYonedaH0 (Y : DGFunctorModel (Yoneda.liftCategory A) (pretr A)) :
    DGCategory.H0 A ⥤ DGCategory.H0 (pretr A) :=
  h0Lift A ⋙ DGFunctor.H0 Y

private def hullInHomotopy (A : DGCategoryModel.{u,v,w} k) : DGCategory.H0 (pretr A) ⥤ K A :=
  DGFunctor.H0 (pretrInclusion A)

private theorem hullInHomotopy_map {X Y : DGCategory.H0 (pretr A)} (f : X ⟶ Y) :
    (hullInHomotopy A).map f = f := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
  exact (DGFunctor.h0Map_mk (pretrInclusion A) f).trans (congrArg classOf (Subtype.ext rfl))

private def hullInHomotopyFullyFaithful (A : DGCategoryModel.{u,v,w} k) :
    (hullInHomotopy A).FullyFaithful where
  preimage f := f
  map_preimage := hullInHomotopy_map
  preimage_map := hullInHomotopy_map

private theorem yonedaCriterion (Y : DGFunctorModel (Yoneda.liftCategory A) (pretr A))
    (hY : IsWrittenYoneda Y) (hC : CanonicalFiniteCellLaws.{u,v,w,j} A)
    (hW : WrittenObjectsLaws A) (h : HomotopyCategoryLaws A) :
    Basic.quasiEquivalence Y ↔ RepresentedUpToHomotopy A h := by
  rw [← show DGFunctor.IsQuasiEquivalence Y = Basic.quasiEquivalence Y from rfl,
    DGFunctor.isQuasiEquivalence_iff]
  have hLoc : ∀ a b, QuasiIso (Y.map a b) := fun a b => by
    letI := (hY.2.choose_spec.2 a b).2
    infer_instance
  let I := hullInHomotopy A
  let hI := hullInHomotopyFullyFaithful A
  constructor
  · intro H P hP
    obtain ⟨X, ⟨e⟩⟩ := hC.represents P hP
    obtain ⟨a, ⟨f⟩⟩ := H.2.mem_essImage X
    have eq : I.obj (Y.obj a) = Yoneda.representable (A := A) a :=
      (congrArg (writtenModule A) (congrFun hY.1 a)).trans (hW.yoneda a)
    let e' : @Iso (K A) (instCategoryK A) (Yoneda.representable a) (I.obj (Y.obj a)) := eqToIso eq.symm
    have e'' : @Iso (K A) (instCategoryK A) (Yoneda.representable a) P :=
      e' ≪≫ I.mapIso f ≪≫ (toHomotopyCategory A).mapIso e
    exact ⟨a, ⟨e''⟩⟩
  · intro H
    refine ⟨hLoc, ⟨fun X => ?_⟩⟩
    obtain ⟨a, ⟨e⟩⟩ := H (writtenModule A X) (hC.finiteCell X)
    have e' : @Iso (K A) (instCategoryK A) (Yoneda.representable a) (I.obj X) := e
    have eq : I.obj (Y.obj a) = Yoneda.representable (A := A) a :=
      (congrArg (writtenModule A) (congrFun hY.1 a)).trans (hW.yoneda a)
    exact ⟨a, ⟨hI.preimageIso (eqToIso eq ≪≫ e')⟩⟩

private theorem originalYonedaH0_isEquivalence
    (Y : DGFunctorModel (Yoneda.liftCategory A) (pretr A)) (hY : IsWrittenYoneda Y)
    (hQ : Basic.quasiEquivalence Y) :
    (originalYonedaH0 Y).IsEquivalence := by
  have hB (a b : A.Obj) : Function.Bijective ((originalYonedaH0 Y).map (X := a) (Y := b)) := by
    letI := (hY.2.choose_spec.2 a b).2
    exact (h0_map_bijective_of_iso Y (a := a) (b := b)).comp (h0LiftEquiv a b).bijective
  exact ⟨⟨fun {a b} => (hB a b).injective⟩, ⟨fun {a b} => (hB a b).surjective⟩,
    ⟨(DGFunctor.isQuasiEquivalence_iff Y).mp hQ |>.2.mem_essImage⟩⟩

end OriginalYoneda

section DerivedHull

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

set_option hygiene false in
set_option quotPrecheck false in
local notation "B" => (AmbientDerived.category.{u,v,w,t} A)

set_option hygiene false in
set_option quotPrecheck false in
local notation "U" => (AmbientDerived.strictInput.{u,v,w,t} A)

local notation "H" => DGCategory.H0 (pretr A)

variable (h : HomotopyCategoryLaws B)

private def strictToDerived : RightDGModuleModel A ⥤ D B h :=
  (U) ⋙ (toHomotopyCategory B ⋙ Q B h)

private def hullInDerived : H ⥤ D B h :=
  hullInHomotopy A ⋙ homotopyLift.{u,v,w,max w t} A ⋙ Q B h

private theorem hullInDerived_map_class {X Y : H} (f : writtenModule A X ⟶ writtenModule A Y) :
    (hullInDerived h).map (homotopyClass f) = (Q B h).map (homotopyClass ((U).map f)) := by
  change (Q B h).map ((homotopyLift.{u,v,w,max w t} A).map
    ((hullInHomotopy A).map (homotopyClass f))) = _
  have hI := hullInHomotopy_map (A := A) (X := X) (Y := Y) (homotopyClass f)
  exact congrArg (fun g => (Q B h).map
      ((homotopyLift.{u,v,w,max w t} A).map g)) hI |>.trans
    (congrArg (Q B h).map (homotopyLift_map_class f))

private theorem writtenKProjective (hw : LiftedHullLaws.{u,v,w,max w t} A) (X : H) :
    IsKProjective ((U).obj (writtenModule A X)) := by
  obtain ⟨P, _⟩ := (hw.represents ((U).obj (writtenModule A X))).2 ⟨X, ⟨Iso.refl _⟩⟩
  exact SemiFreePresentation.isKProjective P

private noncomputable def hullInDerivedFullyFaithful (hp : ∀ X : H,
    IsKProjective ((U).obj (writtenModule A X))) : (hullInDerived h).FullyFaithful := by
  let I := hullInHomotopyFullyFaithful A
  let L := homotopyLiftFullyFaithful.{u,v,w,max w t} A
  have hb (X Y : H) : Function.Bijective ((hullInDerived h).map (X := X) (Y := Y)) :=
    ((hp X).Q_map_bijective h).comp ((L.map_bijective _ _).comp (I.map_bijective X Y))
  letI : (hullInDerived h).Full := ⟨fun {X Y} => (hb X Y).surjective⟩
  letI : (hullInDerived h).Faithful := ⟨fun {X Y} => (hb X Y).injective⟩
  exact Functor.FullyFaithful.ofFullyFaithful _

private theorem perfect_iff_finiteCellRetract (hw : CanonicalFiniteCellLaws.{u,v,w,j} A) (X : D B h) :
    perfect A h X ↔ CompactFiniteCells.IsFiniteCellRetract (U) h X := by
  constructor
  · rintro ⟨P, ⟨r⟩⟩
    exact ⟨writtenModule A P, hw.finiteCell P, ⟨r⟩⟩
  · rintro ⟨P, hP, ⟨r⟩⟩
    obtain ⟨W, ⟨e⟩⟩ := hw.represents P hP
    let r' : Retract X ((strictToDerived h).obj P) := r
    let e' := (strictToDerived h).mapIso e.symm
    exact ⟨W, ⟨r'.trans (Retract.ofIso e')⟩⟩

private theorem writtenSum_isColimit {n : ℕ} (F : Fin n → WrittenObject A) :
    let M : Fin n → RightDGModuleModel A := writtenModule A ∘ F
    let FS : FiniteIndex.{v} n → RightDGModuleModel A := fun i => M i.down
    Nonempty (IsColimit (Cofan.mk (f := (strictToDerived h).obj ∘ FS)
      ((strictToDerived h).obj (finiteSum M))
      (fun i => (strictToDerived h).map (SemiFree.sumInclusion FS i)))) := by
  dsimp only
  let FS : FiniteIndex.{v} n → RightDGModuleModel A := fun i => writtenModule A (F i.down)
  let b := DG.IndexedSums.nativeSum FS
  obtain ⟨c, hc, _, ⟨col⟩⟩ := originalExistingDerivedCoproduct.{u,v,w,v,t} A h b
  have eq : DerivedCoproducts.derivedCofan h c =
      Cofan.mk (f := (strictToDerived h).obj ∘ FS) ((strictToDerived h).obj (SemiFree.directSum FS))
        (fun i => (strictToDerived h).map (SemiFree.sumInclusion FS i)) := by
    unfold DerivedCoproducts.derivedCofan
    congr 1
    funext i
    exact congrArg (fun f => (Q B h).map (homotopyClass f)) (hc i)
  exact ⟨eq ▸ col⟩

private theorem writtenZero_isZero [HasZeroObject (D B h)] :
    IsZero ((strictToDerived h).obj (zeroModule A)) := by
  obtain ⟨col⟩ := writtenSum_isColimit h (n := 0) Fin.elim0
  letI : IsEmpty (FiniteIndex.{v} 0) := ⟨fun i => Fin.elim0 i.down⟩
  let M : Fin 0 → RightDGModuleModel A := writtenModule A ∘ Fin.elim0
  have hM : M = Fin.elim0 := funext (fun i => Fin.elim0 i)
  let init : IsInitial ((strictToDerived h).obj (finiteSum M)) :=
    IsInitial.ofUniqueHom (fun Y => col.desc (Cofan.mk Y (fun i => isEmptyElim i))) (by
      intro Y f
      apply Cofan.IsColimit.hom_ext col
      intro i
      exact isEmptyElim i)
  have hzero := isZero_zero (D B h)
  exact hzero.of_iso (eqToIso (congrArg (fun F => (strictToDerived h).obj (finiteSum F)) hM.symm) ≪≫
    (hzero.isoIsInitial init).symm)

private def writtenShift_iso [SK : HasShift (K B) ℤ] [SD : HasShift (D B h) ℤ] [qS : (Q B h).CommShift ℤ]
    (hs : ∀ M n, (shiftFunctor (K B) n).obj M = shift M n) (M : RightDGModuleModel A) (n : ℤ) :
    ((strictToDerived h).obj (shift M n)) ≅ (shiftFunctor (D B h) n).obj ((strictToDerived h).obj M) :=
  (Q B h).mapIso (((toHomotopyCategory B).mapIso (shiftIso.{u,v,w,max w t} M n)) ≪≫
    eqToIso (hs ((U).obj M) n).symm) ≪≫ ((Q B h).commShiftIso n).app ((U).obj M)

private def writtenCone_iso [SK : HasShift (K B) ℤ] [_SD : HasShift (D B h) ℤ] [_qS : (Q B h).CommShift ℤ]
    (hs : ∀ M n, (shiftFunctor (K B) n).obj M = shift M n)
    {M N : RightDGModuleModel A} (f : M ⟶ N) :
    (strictToDerived h).obj (cone f) ≅ ((Q B h).mapTriangle.obj
      (DerivedTriangles.coneTriangle h SK (hs ((U).obj M) 1) ((U).map f))).obj₃ :=
  (Q B h).mapIso ((toHomotopyCategory B).mapIso (coneIso.{u,v,w,max w t} f))

private theorem finiteConstructionsInDerived [SK : HasShift (K B) ℤ]
    (hs : ∀ M n, (shiftFunctor (K B) n).obj M = shift M n)
    [SD : HasShift (D B h) ℤ] [HasZeroObject (D B h)] [qS : (Q B h).CommShift ℤ] :
    FiniteConstructionsInDerived.{u,v,w,t} A h SK hs SD qS :=
  ⟨writtenZero_isZero h, fun X n => ⟨writtenShift_iso h hs (writtenModule A X) n⟩,
    fun F => writtenSum_isColimit h F, fun f => ⟨writtenCone_iso h hs f⟩⟩

private theorem hullInDerived_image_isTriangulated
    [SK : HasShift (K B) ℤ] (hs : ∀ M n, (shiftFunctor (K B) n).obj M = shift M n)
    [SD : HasShift (D B h) ℤ] [Preadditive (D B h)] [HasZeroObject (D B h)]
    [∀ n : ℤ, (shiftFunctor (D B h) n).Additive] [Pretriangulated (D B h)]
    [qS : (Q B h).CommShift ℤ]
    (hCone : ∀ {M N : RightDGModuleModel B} (f : M ⟶ N),
      (Q B h).mapTriangle.obj (DerivedTriangles.coneTriangle h SK (hs M 1) f) ∈
        distTriang (D B h))
    (hc : (hullInDerived h).FullyFaithful) (hw : WrittenObjectsLaws A) :
    (hullInDerived h).essImage.IsTriangulated := by
  let E := hullInDerived h
  let P := E.essImage
  have hW (X : WrittenObject A) : writtenModule A X ∈ FiniteCellConstructions.writtenSet A :=
    hw.range_eq ▸ Set.mem_range_self X
  have hCode (M : RightDGModuleModel A) (hm : M ∈ FiniteCellConstructions.writtenSet A) :
      ∃ X : WrittenObject A, writtenModule A X = M := by
    rwa [← hw.range_eq] at hm
  letI : P.IsStableUnderShift ℤ := ⟨fun n => ⟨fun M hM => by
    obtain ⟨X, ⟨e⟩⟩ := hM
    obtain ⟨Y, hY⟩ := hCode _ (hw.shift (hW X) n)
    refine ⟨Y, ⟨?_⟩⟩
    exact eqToIso (congrArg (strictToDerived h).obj hY) ≪≫
      writtenShift_iso h hs (writtenModule A X) n ≪≫ (shiftFunctor _ n).mapIso e⟩⟩
  letI : P.IsTriangulatedClosed₃ := ObjectProperty.IsTriangulatedClosed₃.mk' (by
    intro T hT hX hY
    obtain ⟨X, ⟨eX⟩⟩ := hX
    obtain ⟨Y, ⟨eY⟩⟩ := hY
    let g := hc.preimage (eX.hom ≫ T.mor₁ ≫ eY.inv)
    obtain ⟨f, hf⟩ := homotopyClass_surjective
      (M := writtenModule A X) (N := writtenModule A Y) g
    let T' := (Q B h).mapTriangle.obj (DerivedTriangles.coneTriangle h SK
      (hs ((U).obj (writtenModule A X)) 1) ((U).map f))
    have hT' : T' ∈ distTriang (D B h) := hCone _
    have eq : T'.mor₁ ≫ eY.hom = eX.hom ≫ T.mor₁ := by
      change (Q B h).map (homotopyClass ((U).map f)) ≫ eY.hom = _
      rw [← hullInDerived_map_class h f, hf, hc.map_preimage]
      exact (Category.assoc _ _ _).trans (congrArg (eX.hom ≫ ·)
        ((Category.assoc _ _ _).trans
          ((congrArg (T.mor₁ ≫ ·) eY.inv_hom_id).trans (Category.comp_id _))))
    let e := isoTriangleOfIso₁₂ T' T hT' hT eX eY eq
    obtain ⟨Z, hZ⟩ := hCode _ (hw.cone (hW X) (hW Y) f)
    exact ⟨Z, ⟨eqToIso (congrArg (strictToDerived h).obj hZ) ≪≫
      writtenCone_iso h hs f ≪≫ Triangle.π₃.mapIso e⟩⟩)
  obtain ⟨Z, hZ⟩ := hCode (zeroModule A) hw.zero
  exact { toContainsZero := ⟨⟨(strictToDerived h).obj (zeroModule A),
            writtenZero_isZero h, ⟨Z, ⟨eqToIso (congrArg (strictToDerived h).obj hZ)⟩⟩⟩⟩
          toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃ }

end DerivedHull

open private specConeTriangle_eq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles
open CompactFiniteCells
  (AmbientCompactnessComparison NativeCompactFiniteCells NativeCompactnessComparison OriginalCompactFiniteCells)
open CompactRepresentables (LocalizationMapAdditive)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The full finite-cell hull in the adequate localization, conditional on the
compactness theorems in the specified dependency contract. -/
theorem pretriangulatedHull_conditional.{u',v',w',j',t'}
    (_ambient : AmbientCompactnessComparison.{u',v',w',t',j'})
    (_nativeCells : NativeCompactFiniteCells.{u',v',w',j'})
    (_nativeComparison : NativeCompactnessComparison.{u',v',w',j'})
    (originalCells : OriginalCompactFiniteCells.{u',v',w',j',t'}) :
    HullTheorem.{u',v',w',j',t'} := by
  intro k _ A B₀ U₀ h₀ h
  let B := AmbientDerived.category.{u',v',w',t'} A
  let W := quasiIsomorphisms B
  let L := W.Q
  have hw := writtenObjects.{u',v',w'} A
  have hc := canonicalFiniteCells.{u',v',w',j'} A
  have hl := liftedHull.{u',v',w',max w' t'} A
  obtain ⟨ν, hν, Y, hYobj, hYmap, hYiso⟩ := yonedaFactorization.{u',v',w'} A
  have hY : IsWrittenYoneda Y := ⟨hYobj, ν, hν, fun a b => ⟨hYmap a b, hYiso a b⟩⟩
  let G := originalYonedaH0 Y
  let E := hullInDerived.{u',v',w',t'} h
  have hp := writtenKProjective hl
  let ff := hullInDerivedFullyFaithful h hp
  refine ⟨hw, hc, hl, Y, inferInstanceAs (Category (DGCategory.H0 (pretr A))),
    inferInstanceAs (Category (DGCategory.H0 A)), rfl, rfl, hY,
    yonedaCriterion Y hY hc hw h₀, G, E, rfl, ?_, ⟨ff⟩, fun _ => rfl, ?_, hp, ?_⟩
  · intro a b f
    refine ⟨classOf f, HEq.rfl, ?_⟩
    change HEq ((DGFunctor.H0 Y).map (h0LiftEquiv a b (classOf f))) _
    rw [h0LiftEquiv_class]
    rfl
  · intro X Y f
    exact ⟨homotopyClass f, HEq.rfl, heq_of_eq (hullInDerived_map_class h f)⟩
  · letI SD : HasShift W.Localization ℤ := inferInstance
    letI AD : Preadditive W.Localization := inferInstance
    letI ZD : HasZeroObject W.Localization := inferInstance
    letI LD (n : ℤ) : (shiftFunctor W.Localization n).Additive := inferInstance
    letI qS : L.CommShift ℤ := inferInstance
    letI TD : Pretriangulated W.Localization := inferInstance
    have hTri : IsTriangulated W.Localization := inferInstance
    have hL : L.IsTriangulated := Triangulated.Localization.isTriangulated_functor L W
    have hadd : LocalizationMapAdditive h AD := by
      intro M N f g
      exact L.map_add
    have hCone {M N : RightDGModuleModel B} (f : M ⟶ N) :
        L.mapTriangle.obj (DerivedTriangles.coneTriangle h homotopyHasShift rfl f) ∈
          distTriang W.Localization := by
      letI := hL
      rw [specConeTriangle_eq]
      exact L.map_distinguished _ (coneTriangle_distinguished f)
    letI : HasShift (D B h) ℤ := SD
    letI : Preadditive (D B h) := AD
    letI : HasZeroObject (D B h) := ZD
    letI (n : ℤ) : (shiftFunctor (D B h) n).Additive := LD n
    letI : (Q B h).CommShift ℤ := qS
    letI : Pretriangulated (D B h) := TD
    letI : IsTriangulated (D B h) := hTri
    have hIm : E.essImage.IsTriangulated :=
      hullInDerived_image_isTriangulated h (fun _ _ => rfl) hCone ff hw
    refine ⟨homotopyHasShift, homotopyPreadditive, homotopyHasZeroObject,
      homotopyShiftAdditive, fun _ _ => rfl, homotopyPretriangulated, SD, AD, ZD, LD, qS, TD,
      hTri, hL, hadd, hCone, finiteConstructionsInDerived h (fun _ _ => rfl), hIm,
      inheritsTriangulation_of_essImage E ff hIm, ?_, ?_⟩
    · intro X
      have hR := perfect_iff_finiteCellRetract h hc X
      obtain ⟨h₁, h₂⟩ := originalCells A h AD hadd X
      exact ⟨h₁.trans hR.symm, fun hX => h₂ (hR.mp hX)⟩
    · intro hYq
      letI : G.IsEquivalence := originalYonedaH0_isEquivalence Y hY hYq
      letI := ff.full
      letI := ff.faithful
      have hi : (G ⋙ E).essImage = E.essImage := by
        ext X
        constructor
        · rintro ⟨a, ⟨e⟩⟩
          exact ⟨G.obj a, ⟨e⟩⟩
        · rintro ⟨P, ⟨e⟩⟩
          exact ⟨G.objPreimage P, ⟨E.mapIso (G.objObjPreimageIso P) ≪≫ e⟩⟩
      exact ⟨inferInstance, inheritsTriangulation_of_essImage (G ⋙ E)
        (Functor.FullyFaithful.ofFullyFaithful _) (hi.symm ▸ hIm)⟩

end
end DerivedFormalization.RightDGModule

universe v8_closure_bd1e777ffbf39041_u0 v8_closure_bd1e777ffbf39041_u1 v8_closure_bd1e777ffbf39041_u2 v8_closure_bd1e777ffbf39041_u3 v8_closure_bd1e777ffbf39041_u4
theorem _root_.«DerivedFormalization».«RightDGModule».«pretriangulatedHull» : _root_.«Specs».«DerivedFormalization».«DG».«PretriangulatedHull».«HullTheorem».{v8_closure_bd1e777ffbf39041_u0, v8_closure_bd1e777ffbf39041_u1, v8_closure_bd1e777ffbf39041_u2, v8_closure_bd1e777ffbf39041_u3, v8_closure_bd1e777ffbf39041_u4} :=
  @_root_.«DerivedFormalization».«RightDGModule».«pretriangulatedHull_conditional».{v8_closure_bd1e777ffbf39041_u0, v8_closure_bd1e777ffbf39041_u1, v8_closure_bd1e777ffbf39041_u2, v8_closure_bd1e777ffbf39041_u3, v8_closure_bd1e777ffbf39041_u4} (@_root_.«DerivedFormalization».«RightDGModule».«ambientCompactnessComparison».{v8_closure_bd1e777ffbf39041_u0, v8_closure_bd1e777ffbf39041_u1, v8_closure_bd1e777ffbf39041_u2, v8_closure_bd1e777ffbf39041_u4, v8_closure_bd1e777ffbf39041_u3}) (@_root_.«DerivedFormalization».«RightDGModule».«nativeCompactFiniteCells».{v8_closure_bd1e777ffbf39041_u0, v8_closure_bd1e777ffbf39041_u1, v8_closure_bd1e777ffbf39041_u2, v8_closure_bd1e777ffbf39041_u3}) (@_root_.«DerivedFormalization».«RightDGModule».«nativeCompactnessComparison».{v8_closure_bd1e777ffbf39041_u0, v8_closure_bd1e777ffbf39041_u1, v8_closure_bd1e777ffbf39041_u2, v8_closure_bd1e777ffbf39041_u3}) (@_root_.«DerivedFormalization».«RightDGModule».«originalCompactFiniteCells».{v8_closure_bd1e777ffbf39041_u0, v8_closure_bd1e777ffbf39041_u1, v8_closure_bd1e777ffbf39041_u2, v8_closure_bd1e777ffbf39041_u3, v8_closure_bd1e777ffbf39041_u4})
