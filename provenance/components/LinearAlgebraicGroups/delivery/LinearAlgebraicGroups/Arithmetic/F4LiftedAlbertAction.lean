import Specs.LinearAlgebraicGroups.Arithmetic.F4LiftedAlbertAction
import LinearAlgebraicGroups.Albert.IntegralSmoothness
import LinearAlgebraicGroups.Albert.IntrinsicCubic
import LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.F4LiftedAlbertAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open LinearAlgebraicGroups.Specs
open IntegralSemisimpleModel (Integers fibre)
open IntegralCentralQuotient (HopfSpectrum)
open RelativeFormComparison (fieldTest fieldMap)
open Albert.AutomorphismTypeSpecification (IntegralSplitIdentification chevalleyChange)
open Albert.TrialitySpecification (Model modelOp)
open Albert.IdempotentSpecification (IsSplitAutomorphism)
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct Matrix

noncomputable section
universe u v w

set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open private pullbackPointGroupEquiv pullbackPointEquiv pullbackPointEquiv_left
  from LinearAlgebraicGroups.Albert.IntegralSmoothness

private abbrev SpecRing (R : Type u) [CommRing R] := Spec (CommRingCat.of R)

private abbrev specAlg {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] :
    Over (SpecRing R) :=
  (SpecRing B).asOver (SpecRing R)

/-- A point of the scalar extension of a Hopf spectrum is an algebra homomorphism
from the original coordinate algebra to the test algebra. -/
private def basePoints {R B C T : Type u}
    [CommRing R] [CommRing B] [CommRing C] [HopfAlgebra R C] [Algebra R B] [CommRing T] [Algebra R T]
    (D : Over (SpecRing B)) (i : specAlg (R := R) (B := T) ≅
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj D) :
    (D ⟶ (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapGrp).obj
      (HopfSpectrum R C)).X) ≃* WithConv (C →ₐ[R] T) :=
  (pullbackPointGroupEquiv _ D (HopfSpectrum R C)).trans
    ((((yonedaGrpObj (HopfSpectrum R C).X).mapIso i.op).groupIsoToMulEquiv).trans
      Spec.mapMulEquiv.symm)

section Convolution

open Algebra.TensorProduct

variable {R : Type v} {S : Type u} {A : Type w} {B : Type*}
variable [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [HopfAlgebra R A]
variable [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- Restriction to the right factor identifies convolution over the extended
base with convolution on the original Hopf algebra. -/
private def restrictPoints :
    WithConv ((S ⊗[R] A) →ₐ[S] B) ≃* WithConv (A →ₐ[R] B) where
  toFun f := toConv ((liftEquivRight R S A B).symm f.ofConv)
  invFun f := toConv (liftEquivRight R S A B f.ofConv)
  left_inv f := by
    exact congrArg toConv ((liftEquivRight R S A B).apply_symm_apply f.ofConv)
  right_inv f := by
    exact congrArg toConv ((liftEquivRight R S A B).symm_apply_apply f.ofConv)
  map_mul' f g := by
    apply WithConv.ext
    ext x
    change (f * g) ((1 : S) ⊗ₜ[R] x) =
      (toConv ((liftEquivRight R S A B).symm f.ofConv) *
        toConv ((liftEquivRight R S A B).symm g.ofConv)) x
    rw [AlgHom.convMul_apply, AlgHom.convMul_apply,
      Bialgebra.TensorProduct.comul_eq_algHom_toLinearMap]
    simp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      map_one, Bialgebra.comulAlgHom_apply]
    generalize Coalgebra.comul (R := R) x = z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        change lift f.ofConv g.ofConv _ (tensorTensorTensorComm R S R S S S A A
          (((1 : S) ⊗ₜ[S] (1 : S)) ⊗ₜ[R] (x ⊗ₜ[R] y))) = _
        rw [tensorTensorTensorComm_tmul]
        simp [liftEquivRight_symm_apply]
    | add a b ha hb =>
        simp only [TensorProduct.tmul_add, map_add]
        rw [← ha, ← hb]

end Convolution

section ScalarPoints

private lemma specRingMap_injective {B C : Type u} [CommRing B] [CommRing C] :
    Function.Injective (fun f : B →+* C => Spec.map (CommRingCat.ofHom f)) := by
  intro f g h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)


private def testBaseIso {R B T : Type u} [CommRing R] [CommRing B] [CommRing T]
    [Algebra R B] [Algebra B T] [Algebra R T] [IsScalarTower R B T] :
    specAlg (R := R) (B := T) ≅
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj (specAlg (R := B) (B := T)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap B T)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B))) =
      Spec.map (CommRingCat.ofHom (algebraMap R T))
    rw [Category.id_comp, ← Spec.map_comp, IsScalarTower.algebraMap_eq R B T]
    rfl)

private lemma basePoints_spec {R B C T : Type u} [CommRing R] [CommRing B] [CommRing C]
    [HopfAlgebra R C] [Algebra R B] [CommRing T] [Algebra R T]
    {D : Over (SpecRing B)}
    (i : specAlg (R := R) (B := T) ≅
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj D)
    (p : D ⟶ _) :
    Spec.map (CommRingCat.ofHom (basePoints (C := C) D i p).ofConv.toRingHom) =
      i.hom.left ≫ p.left ≫ pullback.fst (HopfSpectrum R C).X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  change (Spec.mapMulEquiv (Spec.mapMulEquiv.symm
    (i.hom ≫ pullbackPointEquiv _ D (HopfSpectrum R C).X p))).left = _
  rw [MulEquiv.apply_symm_apply, Over.comp_left, pullbackPointEquiv_left]

private lemma integerAlgebra_apply {B : Type w} [CommRing B] [Algebra Integers.{v} B]
    (r : Integers.{v}) : algebraMap Integers.{v} B r = (r.down : B) :=
  map_intCast (algebraMap Integers.{v} B) r.down

private instance integerTower (B T : Type*) [CommRing B] [CommRing T] [hBT : Algebra B T]
    [hRB : Algebra Integers.{v} B] [hRT : Algebra Integers.{v} T] :
    @IsScalarTower Integers.{v} B T hRB.toSMul hBT.toSMul hRT.toSMul :=
  IsScalarTower.of_algebraMap_eq (R := Integers.{v}) (S := B) (A := T) fun x => by
    rw [integerAlgebra_apply, integerAlgebra_apply, map_intCast]

private def integerMap {B C : Type*} [CommRing B] [CommRing C]
    [Algebra Integers.{v} B] [Algebra Integers.{v} C] (f : B →+* C) : B →ₐ[Integers.{v}] C :=
  ⟨f, fun r => by
    change f (algebraMap Integers.{v} B r) = algebraMap Integers.{v} C r
    rw [integerAlgebra_apply, integerAlgebra_apply, map_intCast]⟩

private def asIntegerHom {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) :
    CommAlgCat.of ℤ B ⟶ CommAlgCat.of ℤ C :=
  CommAlgCat.ofHom ⟨f, fun r => map_intCast f r⟩

section SmallPoints

variable (S : IntegralSplitIdentification) {A : Type} [CommRing A] [HopfAlgebra Integers.{0} A]
variable (i : HopfSpectrum Integers.{0} A ≅ S.chevalley.group)
variable (B : Type) [CommRing B] [Algebra Integers.{0} B]

private abbrev smallTest := (algSpec (CommRingCat.of ℤ)).obj (op (CommAlgCat.of ℤ B))

private def smallPoints : (smallTest B ⟶ S.split.group.X) ≃* WithConv (A →ₐ[Integers.{0}] B) :=
  letI : Algebra Integers.{0} ℤ := IntegralSemisimpleModel.integerAlgebra ℤ
  let e := S.comparison ≪≫ (chevalleyChange ℤ).mapIso i.symm
  (((yonedaGrp.mapIso e).app (op (smallTest B))).groupIsoToMulEquiv).trans
    (basePoints (smallTest B) (testBaseIso (R := Integers.{0}) (B := ℤ) (T := B)))

private lemma smallPoints_spec (p : smallTest B ⟶ S.split.group.X) :
    Spec.map (CommRingCat.ofHom (smallPoints S i B p).ofConv.toRingHom) =
      (p ≫ (Grp.forget _).map (S.comparison ≪≫ (chevalleyChange ℤ).mapIso i.symm).hom).left ≫
        pullback.fst (HopfSpectrum Integers.{0} A).X.hom
          (Spec.map (CommRingCat.ofHom (@algebraMap Integers.{0} ℤ _ _ (IntegralSemisimpleModel.integerAlgebra ℤ)))) := by
  letI : Algebra Integers.{0} ℤ := IntegralSemisimpleModel.integerAlgebra ℤ
  rw [show smallPoints S i B p =
    basePoints (smallTest B) (testBaseIso (R := Integers.{0}) (B := ℤ) (T := B))
      (p ≫ (Grp.forget _).map (S.comparison ≪≫ (chevalleyChange ℤ).mapIso i.symm).hom) from rfl,
    basePoints_spec]
  exact Category.id_comp _

private lemma smallPoints_natural {B C : Type} [CommRing B] [CommRing C]
    [Algebra Integers.{0} B] [Algebra Integers.{0} C]
    (f : B →ₐ[Integers.{0}] C) (p : smallTest B ⟶ S.split.group.X) :
    smallPoints S i C ((algSpec (CommRingCat.of ℤ)).map (asIntegerHom f.toRingHom).op ≫ p) =
      toConv (f.comp (smallPoints S i B p).ofConv) := by
  apply WithConv.ext
  apply AlgHom.toRingHom_injective
  apply specRingMap_injective
  change Spec.map (CommRingCat.ofHom (smallPoints S i C _).ofConv.toRingHom) =
    Spec.map (CommRingCat.ofHom (f.toRingHom.comp (smallPoints S i B p).ofConv.toRingHom))
  rw [smallPoints_spec, CommRingCat.ofHom_comp, Spec.map_comp, smallPoints_spec]
  simp only [Category.assoc, Over.comp_left]
  rfl

end SmallPoints

section LiftedPoints

open F4LiftedAlbertActionSpecification (integerLift LiftedCoordinates liftedCommRing liftedHopf)
attribute [local instance] integerLift liftedCommRing liftedHopf

private abbrev highIntegerAlgebra (B : Type u) [Field B] : Algebra Integers.{u} B :=
  IntegralSemisimpleModel.integerAlgebra B

attribute [local instance] highIntegerAlgebra

private abbrev lowIntegerAlgebra (B : Type u) [Field B] : Algebra Integers.{0} B :=
  ((Int.castRingHom B).comp ULift.ringEquiv.toRingHom).toAlgebra

attribute [local instance 50] lowIntegerAlgebra

variable (A : Type) [CommRing A] [HopfAlgebra Integers.{0} A]
variable (k K : Type u) [Field k] [Field K] [Algebra k K]

private abbrev liftedFibre := (fibre k).obj (HopfSpectrum Integers.{u} (LiftedCoordinates.{u} A))

private def actualPoints : (fieldTest k K ⟶ (liftedFibre A k).X) ≃*
    WithConv (A →ₐ[Integers.{0}] K) :=
  (basePoints (fieldTest k K) (testBaseIso (R := Integers.{u}) (B := k) (T := K))).trans
    (restrictPoints (R := Integers.{0}) (S := Integers.{u}) (A := A) (B := K))

private lemma actualPoints_natural (σ : Gal(K/k)) (p : fieldTest k K ⟶ (liftedFibre A k).X) :
    actualPoints A k K (fieldMap k K σ ≫ p) =
      toConv ((integerMap.{0} σ.toRingHom).comp (actualPoints A k K p).ofConv) := by
  let i := testBaseIso (R := Integers.{u}) (B := k) (T := K)
  let e := basePoints (C := LiftedCoordinates.{u} A) (fieldTest k K) i
  have he : e (fieldMap k K σ ≫ p) =
      toConv ((integerMap.{u} σ.toRingHom).comp (e p).ofConv) := by
    apply WithConv.ext
    apply AlgHom.toRingHom_injective
    apply specRingMap_injective
    change Spec.map (CommRingCat.ofHom (basePoints (fieldTest k K) i _).ofConv.toRingHom) =
      Spec.map (CommRingCat.ofHom (σ.toRingHom.comp (basePoints (fieldTest k K) i p).ofConv.toRingHom))
    rw [basePoints_spec, CommRingCat.ofHom_comp, Spec.map_comp, basePoints_spec]
    change 𝟙 _ ≫ (fieldMap k K σ).left ≫ p.left ≫ _ =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ 𝟙 _ ≫ p.left ≫ _
    simp only [Category.id_comp]
    rfl
  change restrictPoints (e _) = _
  rw [he]
  rfl

end LiftedPoints

end ScalarPoints

section Coordinates

open Albert.IdempotentSpecification (CoordinateIndex modelVariables modelOfVariables)
open LinearAlgebraicGroups.Composition (Zorn)
open Albert.CubicSpecification (cubicUnit)
open private mapModel modelVariables_map modelOfVariables_map modelOp_map mapModel_unit
  from LinearAlgebraicGroups.Albert.IdempotentCharts

private def conjugateEquiv {R V W : Type*} [CommRing R] [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W] (e : V ≃ₗ[R] W) : (V ≃ₗ[R] V) ≃* (W ≃ₗ[R] W) where
  toFun g := e.symm.trans (g.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' g h := by ext x; simp [LinearEquiv.mul_apply]

private def modelCoordinates (B : Type v) [CommRing B] : Model B ≃ₗ[B] (CoordinateIndex → B) where
  toFun := modelVariables
  invFun := modelOfVariables
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      exact (Zorn.pairedFunctions B).symm_apply_apply (x.2 i)
  right_inv z := by
    funext i
    rcases i with i | ⟨i, j⟩
    · rfl
    · exact congrFun ((Zorn.pairedFunctions B).apply_symm_apply _) j
  map_add' x y := by
    funext i
    rcases i with i | ⟨i, j⟩
    · rfl
    · exact congrFun (map_add (Zorn.pairedFunctions B) (x.2 i) (y.2 i)) j
  map_smul' r x := by
    funext i
    rcases i with i | ⟨i, j⟩
    · rfl
    · exact congrFun (map_smul (Zorn.pairedFunctions B) r (x.2 i)) j

private abbrev ModelGL (B : Type v) [CommRing B] := Matrix.GeneralLinearGroup CoordinateIndex B

private def matrixEquiv (B : Type v) [CommRing B] : ModelGL B ≃* (Model B ≃ₗ[B] Model B) :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv B (CoordinateIndex → B))).trans
    (conjugateEquiv (modelCoordinates B).symm)

private lemma matrixEquiv_coordinates {B : Type v} [CommRing B] (m : ModelGL B) (x : Model B) :
    modelVariables (matrixEquiv B m x) = m.val *ᵥ modelVariables x := by
  change modelCoordinates B ((modelCoordinates B).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Matrix.GeneralLinearGroup.toLin_apply m _

private lemma matrixEquiv_map {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    (f : B →+* C) (m : ModelGL B) (x : Model B) :
    mapModel f (matrixEquiv B m x) =
      matrixEquiv C (Matrix.GeneralLinearGroup.map f m) (mapModel f x) := by
  apply (modelCoordinates C).injective
  funext i
  change modelVariables _ i = modelVariables _ i
  simp only [modelVariables_map, matrixEquiv_coordinates, Matrix.mulVec, dotProduct,
    map_sum, map_mul, Matrix.GeneralLinearGroup.map_apply]

private lemma mapModel_injective {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    {f : B →+* C} (hf : Function.Injective f) : Function.Injective (mapModel f) := by
  intro x y h
  apply (modelCoordinates B).injective
  funext j
  change modelVariables x j = modelVariables y j
  apply hf
  simp only [← modelVariables_map, h]

private lemma matrixEquiv_map_unique {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    (f : B →+* C) (m : ModelGL B) (n : ModelGL C)
    (h : ∀ x, mapModel f (matrixEquiv B m x) = matrixEquiv C n (mapModel f x)) :
    Matrix.GeneralLinearGroup.map f m = n := by
  classical
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hj : f ∘ (Pi.single j 1 : CoordinateIndex → B) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst k; simp
    · simp [hk]
  have hx := h (modelOfVariables (Pi.single j 1))
  rw [matrixEquiv_map, ← modelOfVariables_map, hj] at hx
  have he : modelVariables (matrixEquiv C (Matrix.GeneralLinearGroup.map f m)
      (modelOfVariables (Pi.single j 1))) i =
      modelVariables (matrixEquiv C n (modelOfVariables (Pi.single j 1))) i :=
    congrArg (fun x => modelVariables x i) hx
  simp only [matrixEquiv_coordinates, show ∀ z : CoordinateIndex → C,
    modelVariables (modelOfVariables z) = z from (modelCoordinates C).apply_symm_apply,
    Matrix.mulVec_single] at he
  simpa [Matrix.col] using he



section SmallAction

private abbrev IntegerBase := Integers.{0}
local notation "R₀" => IntegerBase

private structure CoordinateAction (A : Type) [CommRing A] [HopfAlgebra R₀ A] where
  action (B : Type) [CommRing B] [Algebra R₀ B] : WithConv (A →ₐ[R₀] B) →* ModelGL B
  injective (B : Type) [CommRing B] [Algebra R₀ B] : Function.Injective (action B)
  image (B : Type) [CommRing B] [Algebra R₀ B] (m : ModelGL B) :
    m ∈ Set.range (action B) ↔ IsSplitAutomorphism (matrixEquiv B m)
  natural {B C : Type} [CommRing B] [CommRing C] [Algebra R₀ B] [Algebra R₀ C]
    (f : B →ₐ[R₀] C) (p : WithConv (A →ₐ[R₀] B)) :
    Matrix.GeneralLinearGroup.map f.toRingHom (action B p) = action C (toConv (f.comp p.ofConv))

variable (S : IntegralSplitIdentification) {A : Type} [CommRing A] [HopfAlgebra R₀ A]
variable (i : HopfSpectrum R₀ A ≅ S.chevalley.group)

private def smallAction : CoordinateAction A where
  action B := (matrixEquiv B).symm.toMonoidHom.comp
    ((S.split.action (CommAlgCat.of ℤ B)).comp (smallPoints S i B).symm.toMonoidHom)
  injective B _ _ := (matrixEquiv B).symm.injective.comp
    ((S.split.injective (CommAlgCat.of ℤ B)).comp (smallPoints S i B).symm.injective)
  image B _ _ m := by
    have h := Set.ext_iff.mp (S.split.image (CommAlgCat.of ℤ B)) (matrixEquiv B m)
    change _ ↔ (matrixEquiv B m) ∈ {g | IsSplitAutomorphism g}
    rw [← h]
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨(smallPoints S i B).symm p, ?_⟩
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        using congrArg (matrixEquiv B) hp
    · rintro ⟨p, hp⟩
      refine ⟨smallPoints S i B p, ?_⟩
      change (matrixEquiv B).symm (S.split.action _ ((smallPoints S i B).symm
        (smallPoints S i B p))) = m
      rw [MulEquiv.symm_apply_apply, hp, MulEquiv.symm_apply_apply]
  natural {B C} _ _ _ _ f p := by
    let q := (smallPoints S i B).symm p
    have hq : (smallPoints S i C).symm (toConv (f.comp p.ofConv)) =
        (algSpec (CommRingCat.of ℤ)).map (asIntegerHom f.toRingHom).op ≫ q := by
      apply (smallPoints S i C).injective
      rw [MulEquiv.apply_symm_apply, smallPoints_natural, MulEquiv.apply_symm_apply]
    apply matrixEquiv_map_unique
    intro x
    change mapModel f.toRingHom
      (matrixEquiv B ((matrixEquiv B).symm (S.split.action _ q)) x) =
      matrixEquiv C ((matrixEquiv C).symm
        (S.split.action _ ((smallPoints S i C).symm (toConv (f.comp p.ofConv))))) (mapModel f.toRingHom x)
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hq]
    exact S.split.natural (asIntegerHom f.toRingHom) q x

end SmallAction

section LiftAction

local notation "R₀" => IntegerBase
variable {A : Type} [CommRing A] [HopfAlgebra R₀ A]
variable (ρ : CoordinateAction A)

private abbrev universalMatrix := ρ.action A (toConv (AlgHom.id R₀ A))

private def evaluatedMatrix {B : Type v} [CommRing B] [Algebra R₀ B]
    (p : WithConv (A →ₐ[R₀] B)) : ModelGL B :=
  Matrix.GeneralLinearGroup.map p.ofConv.toRingHom (universalMatrix ρ)

private lemma evaluatedMatrix_natural {B : Type v} {C : Type w}
    [CommRing B] [CommRing C] [Algebra R₀ B] [Algebra R₀ C]
    (f : B →ₐ[R₀] C) (p : WithConv (A →ₐ[R₀] B)) :
    Matrix.GeneralLinearGroup.map f.toRingHom (evaluatedMatrix ρ p) =
      evaluatedMatrix ρ (toConv (f.comp p.ofConv)) :=
  rfl

private lemma evaluatedMatrix_small {B : Type} [CommRing B] [Algebra R₀ B]
    (p : WithConv (A →ₐ[R₀] B)) : evaluatedMatrix ρ p = ρ.action B p := by
  simpa only [evaluatedMatrix, universalMatrix, AlgHom.comp_id, WithConv.toConv_ofConv] using
    ρ.natural p.ofConv (toConv (AlgHom.id R₀ A))

private lemma conv_post_one {B : Type v} {C : Type w}
    [CommRing B] [CommRing C] [Algebra R₀ B] [Algebra R₀ C] (f : B →ₐ[R₀] C) :
    toConv (f.comp (1 : WithConv (A →ₐ[R₀] B)).ofConv) = 1 := by
  apply WithConv.ext
  ext x
  exact f.commutes _

private def evaluatedAction (B : Type v) [CommRing B] [Algebra R₀ B] :
    WithConv (A →ₐ[R₀] B) →* ModelGL B where
  toFun := evaluatedMatrix ρ
  map_one' := by
    let f := Algebra.ofId R₀ B
    have h : evaluatedMatrix ρ (1 : WithConv (A →ₐ[R₀] R₀)) = 1 :=
      (evaluatedMatrix_small ρ _).trans (map_one _)
    rw [← conv_post_one f, ← evaluatedMatrix_natural, h, map_one]
  map_mul' p q := by
    letI : Module R₀ A := Algebra.toModule
    let l : A →ₐ[R₀] A ⊗[R₀] A := Algebra.TensorProduct.includeLeft
    let r : A →ₐ[R₀] A ⊗[R₀] A := Algebra.TensorProduct.includeRight
    let f := Algebra.TensorProduct.lift p.ofConv q.ofConv (fun _ _ => Commute.all _ _)
    have hl : toConv (f.comp l) = p := by simp [f, l]
    have hr : toConv (f.comp r) = q := by simp [f, r]
    have hm : toConv (f.comp (toConv l * toConv r).ofConv) = p * q := by
      rw [AlgHom.comp_convMul_distrib]
      exact congrArg₂ (· * ·) hl hr
    rw [← hm, ← evaluatedMatrix_natural, evaluatedMatrix_small, map_mul, map_mul,
      ← evaluatedMatrix_small, ← evaluatedMatrix_small, evaluatedMatrix_natural,
      evaluatedMatrix_natural, hl, hr]

/-- Any small family of coefficients in an algebra is contained in a small
subalgebra. The shrinking equivalence keeps the specified scalar structure. -/
private lemma exists_small_subalgebra {I : Type*} [Small.{0} I]
    {B : Type v} [CommRing B] [Algebra R₀ B] (z : I → B) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra R₀ C) (f : C →ₐ[R₀] B),
      Function.Injective f ∧ Set.range z ⊆ Set.range f := by
  let D := Algebra.adjoin R₀ (Set.range z)
  haveI : Small.{0} D := Algebra.small_adjoin
  let e : Shrink.{0} D ≃ₐ[R₀] D := Shrink.algEquiv R₀ D
  refine ⟨Shrink.{0} D, inferInstance, inferInstance, D.val.comp e.toAlgHom,
    Subtype.val_injective.comp e.injective, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact ⟨e.symm ⟨z j, Algebra.subset_adjoin ⟨j, rfl⟩⟩,
    congrArg Subtype.val (e.apply_symm_apply _)⟩

private lemma algHom_factors {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    [Algebra R₀ B] [Algebra R₀ C] {f : C →ₐ[R₀] B} (hf : Function.Injective f)
    (p : A →ₐ[R₀] B) (hp : Set.range p ⊆ Set.range f) :
    ∃ q : A →ₐ[R₀] C, f.comp q = p := by
  let e := AlgEquiv.ofInjective f hf
  refine ⟨e.symm.toAlgHom.comp (p.codRestrict f.range (fun x => hp ⟨x, rfl⟩)), ?_⟩
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply ⟨p x, hp ⟨x, rfl⟩⟩)

private lemma evaluatedMatrix_injective {B : Type v} [CommRing B] [Algebra R₀ B] :
    Function.Injective (evaluatedMatrix (B := B) ρ) := by
  intro p q h
  obtain ⟨C, _, _, f, hf, hz⟩ :=
    exists_small_subalgebra (Sum.elim p.ofConv q.ofConv : A ⊕ A → B)
  obtain ⟨p', hp⟩ := algHom_factors hf p.ofConv (by
    rintro _ ⟨x, rfl⟩
    exact hz ⟨Sum.inl x, rfl⟩)
  obtain ⟨q', hq⟩ := algHom_factors hf q.ofConv (by
    rintro _ ⟨x, rfl⟩
    exact hz ⟨Sum.inr x, rfl⟩)
  have h' : evaluatedMatrix ρ (toConv p') = evaluatedMatrix ρ (toConv q') := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    apply hf
    have hnat₁ := evaluatedMatrix_natural ρ f (toConv p')
    have hnat₂ := evaluatedMatrix_natural ρ f (toConv q')
    rw [ofConv_toConv, hp] at hnat₁
    rw [ofConv_toConv, hq] at hnat₂
    exact congrArg (fun m : ModelGL B => m.val i j) (hnat₁.trans (h.trans hnat₂.symm))
  rw [evaluatedMatrix_small, evaluatedMatrix_small] at h'
  exact ofConv_injective (hp.symm.trans (hq ▸ congrArg (fun z => f.comp (ofConv z))
    (ρ.injective C h')))

private lemma model_factors {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    (f : C →+* B) (x : Model B) (hx : Set.range (modelVariables x) ⊆ Set.range f) :
    ∃ y : Model C, mapModel f y = x := by
  classical
  let z (j : CoordinateIndex) := (hx ⟨j, rfl⟩).choose
  refine ⟨modelOfVariables z, ?_⟩
  rw [← modelOfVariables_map]
  have h : f ∘ z = modelVariables x := funext fun j => (hx ⟨j, rfl⟩).choose_spec
  rw [h]
  exact (modelCoordinates B).symm_apply_apply x

private lemma evaluatedMatrix_preserves {B : Type v} [CommRing B] [Algebra R₀ B]
    (p : WithConv (A →ₐ[R₀] B)) : IsSplitAutomorphism (matrixEquiv B (evaluatedMatrix ρ p)) := by
  constructor
  · have h := (ρ.image A _).mp (Set.mem_range_self (toConv (AlgHom.id R₀ A)))
    have he := congrArg (mapModel p.ofConv.toRingHom) h.1
    simpa only [evaluatedMatrix, universalMatrix, matrixEquiv_map, mapModel_unit] using he
  · intro x y
    obtain ⟨C, _, _, f, hf, hz⟩ := exists_small_subalgebra
      (Sum.elim p.ofConv (Sum.elim (modelVariables x) (modelVariables y)) :
        A ⊕ (CoordinateIndex ⊕ CoordinateIndex) → B)
    obtain ⟨q, hq⟩ := algHom_factors hf p.ofConv (by
      rintro _ ⟨z, rfl⟩
      exact hz ⟨Sum.inl z, rfl⟩)
    obtain ⟨x', rfl⟩ := model_factors f.toRingHom x (by
      rintro _ ⟨j, rfl⟩
      exact hz ⟨Sum.inr (Sum.inl j), rfl⟩)
    obtain ⟨y', rfl⟩ := model_factors f.toRingHom y (by
      rintro _ ⟨j, rfl⟩
      exact hz ⟨Sum.inr (Sum.inr j), rfl⟩)
    have h := (ρ.image C _).mp (Set.mem_range_self (toConv q))
    have he := congrArg (mapModel f.toRingHom) (h.2 x' y')
    simp only [modelOp_map, matrixEquiv_map] at he
    rw [← evaluatedMatrix_small ρ (toConv q), evaluatedMatrix_natural, ofConv_toConv, hq] at he
    exact he

end LiftAction

section Image

local notation "R₀" => IntegerBase

private lemma matrix_factors {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    (f : C →+* B) (hf : Function.Injective f) (m : ModelGL B)
    (h : ∀ (b : Bool) (i j : CoordinateIndex),
      (if b then m.val else m.inv) i j ∈ Set.range f) :
    ∃ n : ModelGL C, Matrix.GeneralLinearGroup.map f n = m := by
  classical
  let entry (b : Bool) (i j : CoordinateIndex) := (h b i j).choose
  let x : Matrix CoordinateIndex CoordinateIndex C := entry true
  let y : Matrix CoordinateIndex CoordinateIndex C := entry false
  have hx : f.mapMatrix x = m.val := by
    ext i j
    exact (h true i j).choose_spec
  have hy : f.mapMatrix y = m.inv := by
    ext i j
    exact (h false i j).choose_spec
  have hi : Function.Injective (RingHom.mapMatrix (m := CoordinateIndex) f) := by
    intro a b hab
    ext i j
    exact hf (congrArg (fun c : Matrix CoordinateIndex CoordinateIndex B => c i j) hab)
  have hxy : x * y = 1 := hi (by rw [map_mul, hx, hy, m.val_inv, map_one])
  have hyx : y * x = 1 := hi (by rw [map_mul, hy, hx, m.inv_val, map_one])
  exact ⟨⟨x, y, hxy, hyx⟩, Units.ext hx⟩

private lemma splitAutomorphism_of_map {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    (f : C →+* B) (hf : Function.Injective f) (n : ModelGL C)
    (h : IsSplitAutomorphism (matrixEquiv B (Matrix.GeneralLinearGroup.map f n))) :
    IsSplitAutomorphism (matrixEquiv C n) := by
  have hi := mapModel_injective hf
  constructor
  · apply hi
    rw [matrixEquiv_map, mapModel_unit, h.1]
  · intro x y
    apply hi
    simp only [matrixEquiv_map, modelOp_map, h.2]

variable {A : Type} [CommRing A] [HopfAlgebra R₀ A]
variable (ρ : CoordinateAction A)

private lemma evaluatedMatrix_range {B : Type v} [CommRing B] [Algebra R₀ B] (m : ModelGL B) :
    m ∈ Set.range (evaluatedMatrix ρ) ↔ IsSplitAutomorphism (matrixEquiv B m) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact evaluatedMatrix_preserves ρ p
  · intro hm
    obtain ⟨C, _, _, f, hf, hz⟩ := exists_small_subalgebra
      (fun (bij : Bool × CoordinateIndex × CoordinateIndex) =>
        (if bij.1 then m.val else m.inv) bij.2.1 bij.2.2)
    obtain ⟨n, hn⟩ := matrix_factors f.toRingHom hf m (fun b i j => hz ⟨(b, i, j), rfl⟩)
    have ha := splitAutomorphism_of_map f.toRingHom hf n (hn.symm ▸ hm)
    obtain ⟨q, hq⟩ := (ρ.image C n).mpr ha
    refine ⟨toConv (f.comp q.ofConv), ?_⟩
    rw [← evaluatedMatrix_natural, evaluatedMatrix_small, hq, hn]

end Image

section AlbertLaw

open Albert.SplitSpecification
open Albert.IntrinsicCubicSpecification (SplitChart)
open Albert.LowerRankSpecification (untwisted)
open Descent (SemilinearAction)
open private modelBaseChange modelBaseChange_tmul modelBaseChange_operator
  from LinearAlgebraicGroups.Albert.IntrinsicCubic
open private ground_operator from LinearAlgebraicGroups.Albert.QuadraticOperators
open private mapModel_add mapModel_scalar from LinearAlgebraicGroups.Albert.IdempotentCharts

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

private abbrev splitLaw : ParaQuadratic k (Model k) :=
  ParaQuadratic.ofJordan (Albert.weightedHermitianJordan (untwisted k) (Zorn.isOctonion k))

private lemma splitLaw_isSplit : IsSplitModel (splitLaw k) .octonion :=
  ⟨LinearEquiv.refl k _, rfl, ground_operator _ (Zorn.isOctonion k)⟩

private def splitChart : SplitChart (splitLaw k) K where
  coordinates := modelBaseChange k K
  unit := by
    change modelBaseChange k K (1 ⊗ₜ[k] (cubicUnit : Model k)) = _
    rw [modelBaseChange_tmul, one_smul]
    exact mapModel_unit (algebraMap k K)
  op x y := modelBaseChange_operator x y

private lemma splitChart_galois (σ : Gal(K/k)) (x : K ⊗[k] Model k) :
    (splitChart k K).coordinates ((SemilinearAction.scalarExtension (Model k)).act σ x) =
      mapModel σ.toRingHom ((splitChart k K).coordinates x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      change modelBaseChange k K
        ((SemilinearAction.scalarExtension (Model k)).act σ (r ⊗ₜ[k] x)) =
        mapModel σ.toRingHom (modelBaseChange k K (r ⊗ₜ[k] x))
      rw [SemilinearAction.scalarExtension_act_tmul, modelBaseChange_tmul, modelBaseChange_tmul,
        mapModel_scalar]
      congr 1
      apply (modelCoordinates K).injective
      funext j
      change modelVariables (mapModel (algebraMap k K) x) j =
        modelVariables (mapModel σ.toRingHom (mapModel (algebraMap k K) x)) j
      simp only [modelVariables_map]
      exact (σ.commutes (modelVariables x j)).symm
  | add x y hx hy => simp only [map_add, hx, hy, mapModel_add]

attribute [local instance] highIntegerAlgebra lowIntegerAlgebra

/-- The lifted Chevalley coordinates give the full split Albert action on
the specified field fibre, with the scalar Galois action on its points. -/
theorem liftedAlbertAction : F4LiftedAlbertActionSpecification.Statement.{u} := by
  intro S A _ _ i k K _ _ _
  let ρ := smallAction S i
  let e := actualPoints A k K
  let c := splitChart k K
  let j := conjugateEquiv c.coordinates.symm
  let a := j.toMonoidHom.comp ((matrixEquiv K).toMonoidHom.comp
    ((evaluatedAction ρ K).comp e.toMonoidHom))
  refine ⟨splitLaw k, c, splitLaw_isSplit k, a, ?_, ?_, ?_⟩
  · exact j.injective.comp ((matrixEquiv K).injective.comp
      ((evaluatedMatrix_injective ρ).comp e.injective))
  · ext g
    have hc (m : ModelGL K) : IsSplitAutomorphism (matrixEquiv K m) ↔
        j (matrixEquiv K m) (1 ⊗ₜ[k] (splitLaw k).unit) = 1 ⊗ₜ[k] (splitLaw k).unit ∧
          ∀ x y, j (matrixEquiv K m) ((splitLaw k).op K x y) =
            (splitLaw k).op K (j (matrixEquiv K m) x) (j (matrixEquiv K m) y) := by
      let b := matrixEquiv K m
      have hb (x) : c.coordinates (j b x) = b (c.coordinates x) :=
        c.coordinates.apply_symm_apply _
      constructor
      · intro h
        constructor
        · apply c.coordinates.injective
          rw [hb, c.unit, h.1]
        · intro x y
          apply c.coordinates.injective
          rw [hb, c.op, c.op, hb, hb]
          exact h.2 _ _
      · rintro ⟨hu, ho⟩
        constructor
        · have hh := congrArg c.coordinates hu
          rwa [hb, c.unit] at hh
        · intro x y
          obtain ⟨x', rfl⟩ := c.coordinates.surjective x
          obtain ⟨y', rfl⟩ := c.coordinates.surjective y
          have hh := congrArg c.coordinates (ho x' y')
          rwa [hb, c.op, c.op, hb, hb] at hh
    constructor
    · rintro ⟨p, rfl⟩
      exact (hc _).mp (evaluatedMatrix_preserves ρ (e p))
    · intro hg
      let m := (matrixEquiv K).symm (j.symm g)
      have he : j (matrixEquiv K m) = g := by simp [m]
      obtain ⟨q, hq⟩ := (evaluatedMatrix_range ρ m).mpr ((hc m).mpr (he.symm ▸ hg))
      refine ⟨e.symm q, ?_⟩
      change j (matrixEquiv K (evaluatedMatrix ρ (e (e.symm q)))) = g
      rw [e.apply_symm_apply, hq, he]
  · intro σ p x
    apply c.coordinates.injective
    let m := evaluatedMatrix ρ (e p)
    change c.coordinates ((SemilinearAction.scalarExtension (Model k)).act σ
      (c.coordinates.symm (matrixEquiv K m (c.coordinates x)))) =
      c.coordinates (c.coordinates.symm
        (matrixEquiv K (evaluatedMatrix ρ (e (fieldMap k K σ ≫ p)))
          (c.coordinates ((SemilinearAction.scalarExtension (Model k)).act σ x))))
    simp only [show ∀ y, c.coordinates ((SemilinearAction.scalarExtension (Model k)).act σ y) =
      mapModel σ.toRingHom (c.coordinates y) from splitChart_galois k K σ,
      c.coordinates.apply_symm_apply, matrixEquiv_map]
    change matrixEquiv K (Matrix.GeneralLinearGroup.map σ.toRingHom (evaluatedMatrix ρ (e p))) _ = _
    rw [show σ.toRingHom = (integerMap.{0} σ.toRingHom).toRingHom from rfl,
      evaluatedMatrix_natural]
    rw [← actualPoints_natural]

end AlbertLaw

end Coordinates

end

end LinearAlgebraicGroups.Arithmetic.F4LiftedAlbertAction
