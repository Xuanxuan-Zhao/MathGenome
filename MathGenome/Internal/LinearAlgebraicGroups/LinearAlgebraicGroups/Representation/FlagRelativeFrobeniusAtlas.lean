import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagRelativeFrobeniusAtlas
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FiniteDistributions
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatCells
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.KrullDimension.Field

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.FlagRelativeFrobeniusAtlas

open Specs.FlagRelativeFrobeniusAtlas (baseFrobenius IsRelativeFrobenius)
open TopCat TopologicalSpace

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p]

/-- Iterated Frobenius uses only the vanishing of p in the ring, so this
construction also applies to sections over the empty open. -/
private def ringPower (R : CommRingCat.{u}) (h : (p : R) = 0) : R ⟶ R :=
  CommRingCat.ofHom
    { toFun := fun a => a ^ (p ^ r)
      map_zero' := zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      map_one' := one_pow _
      map_mul' := fun a b => mul_pow a b _
      map_add' := fun a b => by
        obtain ⟨t, ht⟩ := exists_add_pow_prime_pow_eq (Fact.out : p.Prime) a b r
        simpa [h] using ht }

omit [Fact p.Prime] in
private theorem sectionChar (X : SchemeOver k) (U : X.left.Opens) :
    (p : Γ(X.left, U)) = 0 := by
  let f := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    X.hom.appLE ⊤ U (by simp)
  rw [← map_natCast f.hom, CharP.cast_eq_zero k p, map_zero]

omit [Fact p.Prime] in
private theorem stalkChar (X : SchemeOver k) (x : X.left) :
    (p : X.left.presheaf.stalk x) = 0 := by
  let f := X.left.presheaf.germ ⊤ x (by simp)
  rw [← map_natCast f.hom, sectionChar p X ⊤, map_zero]

/-- The identity continuous map, with the iterated Frobenius on sections. -/
private def absolutePresheaf (X : SchemeOver k) :
    X.left.toPresheafedSpace ⟶ X.left.toPresheafedSpace where
  base := 𝟙 _
  c :=
    { app := fun U => ringPower p r (Γ(X.left, U.unop)) (sectionChar p X U.unop)
      naturality := by
        intro U V f
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro s
        exact (map_pow (X.left.presheaf.map f).hom s _).symm }

/-- Absolute Frobenius on a scheme over the characteristic-p field. -/
def absoluteFrobenius (X : SchemeOver k) : X.left ⟶ X.left :=
  ⟨⟨absolutePresheaf p r X, fun x => by
    have hh : (absolutePresheaf p r X).stalkMap x =
        ringPower p r (X.left.presheaf.stalk x) (stalkChar p X x) := by
      apply X.left.presheaf.stalk_hom_ext
      intro U hx
      rw [PresheafedSpace.stalkMap_germ]
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro s
      exact map_pow (X.left.presheaf.germ U x hx).hom s _
    rw [hh]
    constructor
    intro a ha
    exact (isUnit_pow_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp ha⟩⟩

@[simp] theorem absoluteFrobenius_apply (X : SchemeOver k) (x : X.left) :
    absoluteFrobenius p r X x = x := rfl

theorem absoluteFrobenius_natural {X Y : SchemeOver k} (f : X.left ⟶ Y.left) :
    f ≫ absoluteFrobenius p r Y = absoluteFrobenius p r X ≫ f := by
  apply Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_injective
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.hext _ _ ?_ ?_
  · rfl
  · apply heq_of_eq
    change (f ≫ absoluteFrobenius p r Y).c = (absoluteFrobenius p r X ≫ f).c
    apply NatTrans.ext
    funext U
    change (f ≫ absoluteFrobenius p r Y).app U.unop =
      (absoluteFrobenius p r X ≫ f).app U.unop
    rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact map_pow (f.app U.unop).hom a _


private theorem absoluteFrobenius_spec (R : CommRingCat.{u})
    (t : Spec R ⟶ Spec (CommRingCat.of k)) :
    absoluteFrobenius p r (Over.mk t) =
      Spec.map (ringPower p r R (by
        obtain ⟨f, rfl⟩ := Spec.map_surjective t
        rw [← map_natCast f.hom, CharP.cast_eq_zero k p, map_zero])) := by
  letI : IsAffine (Over.mk t).left := inferInstanceAs (IsAffine (Spec R))
  apply AlgebraicGeometry.ext_of_isAffine
  refine (cancel_mono (Scheme.ΓSpecIso R).hom).mp ?_
  rw [Scheme.ΓSpecIso_naturality]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact map_pow (Scheme.ΓSpecIso R).hom.hom a _

variable [IsAlgClosed k]

abbrev twist : SchemeOver k ⥤ SchemeOver k := Specs.FlagRelativeFrobeniusAtlas.twist p r

private abbrev inverseBaseFrobenius : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (iterateFrobeniusEquiv k p r).symm.toRingHom)

@[reassoc, simp] private theorem baseFrobenius_inverse :
    baseFrobenius (k := k) p r ≫ inverseBaseFrobenius (k := k) p r = 𝟙 _ := by
  rw [baseFrobenius, ← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (iterateFrobeniusEquiv k p r).apply_symm_apply

@[reassoc, simp] private theorem inverse_baseFrobenius :
    inverseBaseFrobenius (k := k) p r ≫ baseFrobenius (k := k) p r = 𝟙 _ := by
  rw [baseFrobenius, ← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (iterateFrobeniusEquiv k p r).symm_apply_apply

theorem twistIsBaseChange : Specs.FlagRelativeFrobeniusAtlas.TwistIsBaseChange.{u} := by
  intro k _ p r _ _ _ X
  let e : Spec (CommRingCat.of k) ≅ Spec (CommRingCat.of k) :=
    ⟨baseFrobenius p r, inverseBaseFrobenius p r, baseFrobenius_inverse p r,
      inverse_baseFrobenius p r⟩
  letI : IsIso (baseFrobenius (k := k) p r) := e.isIso_hom
  apply IsPullback.of_horiz_isIso
  constructor
  change (𝟙 _ : X.left ⟶ X.left) ≫ X.hom = (X.hom ≫ e.inv) ≫ e.hom
  simp

/-- The relative map has underlying morphism absolute Frobenius and is
linear over the unchanged base of the twisted model. -/
def relativeFrobenius : 𝟭 (SchemeOver k) ⟶ twist p r where
  app X := Over.homMk (absoluteFrobenius p r X) (by
    change absoluteFrobenius p r X ≫ X.hom ≫ inverseBaseFrobenius p r = X.hom
    rw [← Category.assoc, ← absoluteFrobenius_natural p r (Y := Over.mk (𝟙 _)) X.hom]
    have hb : absoluteFrobenius p r (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
        baseFrobenius (k := k) p r := absoluteFrobenius_spec p r _ _
    rw [hb, Category.assoc, baseFrobenius_inverse]
    exact Category.comp_id _)
  naturality X Y f := by
    apply Over.OverMorphism.ext
    exact absoluteFrobenius_natural p r f.left

theorem relativeFrobenius_formula (X : SchemeOver k) :
    IsRelativeFrobenius p r X ((relativeFrobenius p r).app X) := by
  refine ⟨fun _ => rfl, fun U h s => ?_⟩
  change (ringPower p r Γ(X.left, U) (sectionChar p X U) ≫ X.left.presheaf.map (homOfLE h).op) s = _
  rw [show homOfLE h = 𝟙 U from Subsingleton.elim _ _, op_id, (X.left.presheaf).map_id, Category.comp_id]
  rfl

theorem relativeFrobeniusNaturality : Specs.FlagRelativeFrobeniusAtlas.RelativeFrobeniusNaturality.{u} :=
  fun {_} _ p r _ _ _ => ⟨relativeFrobenius p r, relativeFrobenius_formula p r⟩


/-- The scheme Frobenius is determined by its prescribed pullbacks on opens. -/
theorem relativeFrobenius_unique (X : SchemeOver k) (F : X ⟶ (twist p r).obj X)
    (hF : IsRelativeFrobenius p r X F) : F = (relativeFrobenius p r).app X := by
  apply Over.OverMorphism.ext
  have hb : F.left.base = ((relativeFrobenius p r).app X).left.base :=
    TopCat.ext hF.1
  apply Scheme.Hom.ext hb
  intro U
  have h : U ≤ F.left ⁻¹ᵁ U := by
    intro x hx
    change F.left x ∈ U
    rw [hF.1]
    exact hx
  change F.left.appLE U U h = _
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  exact hF.2 U h s

private theorem relativeFrobenius_of_algClosedField_isIso (K : Type u)
    [Field K] [Algebra k K] [IsAlgClosed K] :
    IsIso ((relativeFrobenius p r).app ((testSpec k).obj (op (CommAlgCat.of k K)))) := by
  let X := (testSpec k).obj (op (CommAlgCat.of k K))
  let f := (relativeFrobenius p r).app X
  letI : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
  let e := Scheme.Spec.mapIso (iterateFrobeniusEquiv K p r).toCommRingCatIso.op
  have he : f.left = e.hom := by
    let t := Spec.map (CommRingCat.ofHom (algebraMap k K))
    change absoluteFrobenius p r (Over.mk t) = Spec.map (CommRingCat.ofHom (iterateFrobenius K p r))
    rw [absoluteFrobenius_spec]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl
  letI : IsIso ((Over.forget _).map f) := by
    change IsIso f.left
    rw [he]
    exact e.isIso_hom
  exact isIso_of_reflects_iso f (Over.forget _)

/-- The relative map has a unique lift of each geometric point. -/
theorem relativeFrobenius_geometricFiber (X : SchemeOver k) (K : Type u)
    [Field K] [Algebra k K] [IsAlgClosed K]
    (y : Points ((twist p r).obj X) (CommAlgCat.of k K)) :
    ∃! x : Points X (CommAlgCat.of k K), x ≫ (relativeFrobenius p r).app X = y := by
  let T := twist (k := k) p r
  let S := (testSpec k).obj (op (CommAlgCat.of k K))
  let F := relativeFrobenius (k := k) p r
  let f := F.app S
  letI : IsIso f := relativeFrobenius_of_algClosedField_isIso p r K
  let x : S ⟶ X := T.preimage (inv f ≫ y)
  have hx : T.map x = inv f ≫ y := T.map_preimage _
  have he : x ≫ F.app X = y :=
    (F.naturality x).trans ((congrArg (f ≫ ·) hx).trans (IsIso.hom_inv_id_assoc f y))
  refine ⟨x, he, fun z hz => ?_⟩
  apply T.map_injective
  apply (cancel_epi f).mp
  exact ((F.naturality z).symm.trans hz).trans ((F.naturality x).symm.trans he).symm


theorem uniqueGeometricFiberPoint :
    Specs.FlagRelativeFrobeniusAtlas.UniqueGeometricFiberPoint.{u} := by
  intro k _ p r _ _ _ X F hF K _ _ _ y
  rw [relativeFrobenius_unique p r X F hF]
  exact relativeFrobenius_geometricFiber p r X K y

section Groups

open Specs.FlagRelativeFrobeniusAtlas (twistGroup affineTwistProjection affineScalarProjection)
open LinearAlgebraicGroups.Specs (GroupScheme)
open private extendedGroupIso extendedSpecIso extendedSpecIso_hom_fst specGroupMap_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

/-- The Frobenius on group objects uses the same relative map on the underlying scheme. -/
def relativeGroupFrobenius : 𝟭 (GroupScheme k) ⟶ twistGroup p r :=
  (Functor.mapGrpIdIso (C := SchemeOver k)).inv ≫
    Functor.mapGrpNatTrans (relativeFrobenius p r)

@[simp] theorem relativeGroupFrobenius_hom (G : GroupScheme k) :
    ((relativeGroupFrobenius p r).app G).hom.hom =
      (relativeFrobenius p r).app G.X := by
  change 𝟙 _ ≫ (relativeFrobenius p r).app G.X = _
  exact Category.id_comp _

theorem relativeGroupNaturality : Specs.FlagRelativeFrobeniusAtlas.RelativeGroupNaturality.{u} := by
  intro k _ p r _ _ _
  refine ⟨relativeGroupFrobenius p r, ?_⟩
  intro G
  rw [relativeGroupFrobenius_hom]
  exact relativeFrobenius_formula p r G.X

private def twistObjectIso (X : SchemeOver k) :
    letI := (iterateFrobenius k p r).toAlgebra
    (twist p r).obj X ≅ (baseChange k k).obj X := by
  letI := (iterateFrobenius k p r).toAlgebra
  let h := twistIsBaseChange p r X
  let h' := IsPullback.of_hasPullback X.hom (fieldSpecMap k k)
  exact Over.isoMk (h.isoIsPullback _ _ h') (h.isoIsPullback_hom_snd _ _ h')

private theorem twistObjectIso_hom_fst (X : SchemeOver k) :
    letI := (iterateFrobenius k p r).toAlgebra
    (twistObjectIso p r X).hom.left ≫ pullback.fst X.hom (fieldSpecMap k k) = 𝟙 _ := by
  letI := (iterateFrobenius k p r).toAlgebra
  exact (twistIsBaseChange p r X).isoIsPullback_hom_fst _ _
    (IsPullback.of_hasPullback X.hom (fieldSpecMap k k))

/-- Compare with the scalar extension functor whose target is a chosen pullback. -/
def twistBaseChangeIso :
    letI := (iterateFrobenius k p r).toAlgebra
    twist p r ≅ baseChange k k := by
  letI := (iterateFrobenius k p r).toAlgebra
  refine NatIso.ofComponents (twistObjectIso p r) ?_
  intro X Y f
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (f.left ≫ (twistObjectIso p r Y).hom.left) ≫ pullback.fst Y.hom (fieldSpecMap k k) =
      ((twistObjectIso p r X).hom.left ≫ ((baseChange k k).map f).left) ≫
        pullback.fst Y.hom (fieldSpecMap k k)
    rw [Category.assoc, Category.assoc, twistObjectIso_hom_fst p r Y]
    have hm : ((baseChange k k).map f).left ≫ pullback.fst Y.hom (fieldSpecMap k k) =
        pullback.fst X.hom (fieldSpecMap k k) ≫ f.left := pullback.lift_fst _ _ _
    rw [hm, ← Category.assoc, twistObjectIso_hom_fst p r X, Category.id_comp]
    exact Category.comp_id _
  · exact (Over.w _).trans (Over.w _).symm

theorem twistBaseChangeIso_inv_left (X : SchemeOver k) :
    letI := (iterateFrobenius k p r).toAlgebra
    ((twistBaseChangeIso p r).inv.app X).left = pullback.fst X.hom (fieldSpecMap k k) := by
  letI := (iterateFrobenius k p r).toAlgebra
  let e := twistObjectIso p r X
  change e.inv.left = _
  have h := twistObjectIso_hom_fst p r X
  calc
    e.inv.left = e.inv.left ≫ (e.hom.left ≫ pullback.fst X.hom (fieldSpecMap k k)) :=
      (Category.comp_id _).symm.trans (congrArg (e.inv.left ≫ ·) h.symm)
    _ = _ := Iso.inv_hom_id_assoc ((Over.forget _).mapIso e) _

/-- Hopf scalar extension and the geometric twist describe the same group. -/
def affineTwistGroupIso (A : HopfAlgebraCategory k) :
    specGroup (FiniteDistributions.twistCoordinates k p r A) ≅
      (twistGroup p r).obj (specGroup A) :=
  letI := (iterateFrobenius k p r).toAlgebra
  extendedGroupIso k A ≪≫
    ((Functor.mapGrpNatIso (twistBaseChangeIso p r)).app (specGroup A)).symm

theorem affineTwistGroupIso_hom_left (A : HopfAlgebraCategory k) :
    (affineTwistGroupIso p r A).hom.hom.hom.left = affineTwistProjection p r A := by
  letI := (iterateFrobenius k p r).toAlgebra
  change (extendedSpecIso k A).hom.left ≫ ((twistBaseChangeIso p r).inv.app (specGroup A).X).left = _
  rw [twistBaseChangeIso_inv_left]
  exact extendedSpecIso_hom_fst k A

theorem affineFrobenius_agrees (A : HopfAlgebraCategory k) :
    specGroupMap (FiniteDistributions.frobeniusPullback p r A) ≫ (affineTwistGroupIso p r A).hom =
      (relativeGroupFrobenius p r).app (specGroup A) := by
  apply (Grp.forget (SchemeOver k)).map_injective
  apply Over.OverMorphism.ext
  change (specGroupMap (FiniteDistributions.frobeniusPullback p r A)).hom.hom.left ≫
    (affineTwistGroupIso p r A).hom.hom.hom.left =
    ((relativeGroupFrobenius p r).app (specGroup A)).hom.hom.left
  rw [relativeGroupFrobenius_hom, affineTwistGroupIso_hom_left]
  let t : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k A))
  letI := (iterateFrobenius k p r).toAlgebra
  change Spec.map (CommRingCat.ofHom
      (FiniteDistributions.frobeniusPullback p r A).hom.toAlgHom.toRingHom) ≫
    affineScalarProjection k A =
    absoluteFrobenius p r (Over.mk t)
  rw [absoluteFrobenius_spec, affineScalarProjection, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change (FiniteDistributions.frobeniusPullback p r A).hom
    (Specs.RelativeFrobenius.scalarTensor (iterateFrobenius k p r) A 1 a) = a ^ (p ^ r)
  exact (FiniteDistributions.frobeniusPullback_formula p r A 1 a).trans (one_smul _ _)

theorem affineFrobeniusComparison : Specs.FlagRelativeFrobeniusAtlas.AffineFrobeniusComparison.{u} := by
  intro k _ p r _ _ _ A
  refine ⟨(relativeGroupFrobenius p r).app (specGroup A), affineTwistGroupIso p r A,
    FiniteDistributions.frobeniusPullback p r A, ?_, affineTwistGroupIso_hom_left p r A,
    FiniteDistributions.frobeniusPullback_formula p r A, affineFrobenius_agrees p r A⟩
  rw [relativeGroupFrobenius_hom]
  exact relativeFrobenius_formula p r _



open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)

private def splitAlgebraScalarIso (K : Type u) [Field K] [Algebra k K]
    (M : Type u) [CommGroup M] :
    extendedHopf K (groupAlgebra k M) ≅ groupAlgebra K M :=
  CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k K M)

omit [IsAlgClosed k] in
private theorem splitAlgebraScalarIso_inv_of (K : Type u) [Field K] [Algebra k K]
    (M : Type u) [CommGroup M] (m : M) :
    (splitAlgebraScalarIso K M).inv.hom (MonoidAlgebra.of K M m) =
      (1 : K) ⊗ₜ[k] MonoidAlgebra.of k M m :=
  MonoidAlgebra.scalarTensorEquiv_symm_single (R := k) (A := K) m 1

private abbrev splitAlgebraTwistIso (M : Type u) [CommGroup M] :
    FiniteDistributions.twistCoordinates k p r (groupAlgebra k M) ≅ groupAlgebra k M :=
  letI := (iterateFrobenius k p r).toAlgebra
  splitAlgebraScalarIso k M

/-- The split group keeps the same group-algebra exponents under scalar base change. -/
def splitGroupTwistIso (M : Type u) [CommGroup M] :
    (twistGroup p r).obj (specGroup (groupAlgebra k M)) ≅ specGroup (groupAlgebra k M) :=
  (affineTwistGroupIso p r (groupAlgebra k M)).symm ≪≫
    (hopfSpec (CommRingCat.of k)).mapIso (splitAlgebraTwistIso p r M).symm.op

omit [IsAlgClosed k] in
private theorem affineScalarProjection_natural (K : Type u) [Field K] [Algebra k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    (specGroupMap (extendedHopfMap K f)).hom.hom.left ≫ affineScalarProjection K A =
      affineScalarProjection K B ≫ (specGroupMap f).hom.hom.left := by
  let m := Algebra.TensorProduct.map (AlgHom.id K K) f.hom.toAlgHom
  change Spec.map (CommRingCat.ofHom m.toRingHom) ≫ affineScalarProjection K A =
    affineScalarProjection K B ≫ Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)
  rw [affineScalarProjection, affineScalarProjection, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  rfl

private def affineTwistMap {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    FiniteDistributions.twistCoordinates k p r A ⟶
      FiniteDistributions.twistCoordinates k p r B :=
  letI := (iterateFrobenius k p r).toAlgebra
  extendedHopfMap k f

omit [IsAlgClosed k] in
private theorem affineTwistProjection_natural {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    (specGroupMap (affineTwistMap p r f)).hom.hom.left ≫ affineTwistProjection p r A =
      affineTwistProjection p r B ≫ (specGroupMap f).hom.hom.left := by
  letI := (iterateFrobenius k p r).toAlgebra
  exact affineScalarProjection_natural k f

private theorem affineTwistGroupIso_natural {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    specGroupMap (affineTwistMap p r f) ≫ (affineTwistGroupIso p r A).hom =
      (affineTwistGroupIso p r B).hom ≫ (twistGroup p r).map (specGroupMap f) := by
  apply (Grp.forget (SchemeOver k)).map_injective
  apply Over.OverMorphism.ext
  let m := (specGroupMap (affineTwistMap p r f)).hom.hom.left
  let n := (specGroupMap f).hom.hom.left
  calc
    m ≫ (affineTwistGroupIso p r A).hom.hom.hom.left = m ≫ affineTwistProjection p r A :=
      congrArg (m ≫ ·) (affineTwistGroupIso_hom_left p r A)
    _ = affineTwistProjection p r B ≫ n := affineTwistProjection_natural p r f
    _ = (affineTwistGroupIso p r B).hom.hom.hom.left ≫ n :=
      congrArg (· ≫ n) (affineTwistGroupIso_hom_left p r B).symm

open Specs.CharacterDescent (Character)
open private integerHopfHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

omit [IsAlgClosed k] in
private theorem specCharacter_eq_pow {A : HopfAlgebraCategory k}
    (φ ψ : groupAlgebra k IntegerCharacters ⟶ A) (n : ℕ)
    (h : φ.hom (MonoidAlgebra.of k _ integerGenerator) =
      ψ.hom (MonoidAlgebra.of k _ integerGenerator) ^ n) :
    specGroupMap φ = (specGroupMap ψ)^n := by
  let e := CharacterDescent.groupLikeCharacterEquiv A
  let i := integerHopfHomEquiv A
  let x := i.symm φ
  let y := i.symm ψ
  have hx : e x = specGroupMap φ := by
    change specGroupMap (i (i.symm φ)) = _
    rw [Equiv.apply_symm_apply]
  have hy : e y = specGroupMap ψ := by
    change specGroupMap (i (i.symm ψ)) = _
    rw [Equiv.apply_symm_apply]
  have hxy : x = y ^ n := by
    apply GroupLike.val_injective
    exact h
  calc
    specGroupMap φ = e x := hx.symm
    _ = e (y ^ n) := congrArg e hxy
    _ = (e y)^n := map_pow e y n
    _ = _ := congrArg (· ^ n) hy

private theorem relativeFrobenius_gm :
    (relativeGroupFrobenius p r).app (specGroup (groupAlgebra k IntegerCharacters)) ≫
        (splitGroupTwistIso p r IntegerCharacters).hom =
      (𝟙 (specGroup (groupAlgebra k IntegerCharacters))) ^ (p ^ r) := by
  let W := groupAlgebra k IntegerCharacters
  let i := splitAlgebraTwistIso (k := k) p r IntegerCharacters
  let f := FiniteDistributions.frobeniusPullback p r W
  let t := MonoidAlgebra.of k IntegerCharacters integerGenerator
  have hc : (i.inv ≫ f).hom t = t ^ (p ^ r) := by
    change f.hom (i.inv.hom t) = t ^ (p ^ r)
    have h : i.inv.hom t = Specs.RelativeFrobenius.scalarTensor (iterateFrobenius k p r) W 1 t := by
      letI := (iterateFrobenius k p r).toAlgebra
      exact splitAlgebraScalarIso_inv_of k IntegerCharacters integerGenerator
    exact (congrArg f.hom h).trans ((FiniteDistributions.frobeniusPullback_formula p r W 1 t).trans
      (one_smul k _))
  have hpow := specCharacter_eq_pow (i.inv ≫ f) (𝟙 W) (p ^ r) hc
  rw [← affineFrobenius_agrees p r W]
  change (specGroupMap f ≫ (affineTwistGroupIso p r W).hom) ≫
      (affineTwistGroupIso p r W).inv ≫ specGroupMap i.inv = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← specGroupMap_comp]
  change specGroupMap (i.inv ≫ f) = _
  have hid : specGroupMap (𝟙 W) = 𝟙 (specGroup W) := by
    change (hopfSpec (CommRingCat.of k)).map (𝟙 W).op = _
    exact (hopfSpec (CommRingCat.of k)).map_id (op W)
  exact hpow.trans (congrArg (· ^ (p ^ r)) hid)

/-- Transport a character to the corresponding character of the twisted group. -/
def twistCharacter {H : GroupScheme k} (χ : Character H) : Character ((twistGroup p r).obj H) :=
  (twistGroup p r).map χ ≫ (splitGroupTwistIso p r IntegerCharacters).hom

/-- The Frobenius pullback of the transported character is its q-th power. -/
theorem relativeFrobenius_character {H : GroupScheme k} (χ : Character H) :
    (relativeGroupFrobenius p r).app H ≫ twistCharacter p r χ = χ ^ (p ^ r) := by
  let M := specGroup (groupAlgebra k IntegerCharacters)
  let F := relativeGroupFrobenius (k := k) p r
  let e := splitGroupTwistIso (k := k) p r IntegerCharacters
  have hn := F.naturality χ
  calc
    F.app H ≫ twistCharacter p r χ = (F.app H ≫ (twistGroup p r).map χ) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = χ ≫ F.app M ≫ e.hom := by
      rw [← hn, Category.assoc]
      rfl
    _ = χ ≫ (𝟙 M) ^ (p ^ r) := congrArg (χ ≫ ·) (relativeFrobenius_gm p r)
    _ = _ := by
      apply Grp.hom_ext
      simp only [Grp.comp_hom_hom, Grp.Hom.hom_pow, Mon.Hom.hom_pow, Grp.id_hom_hom,
        MonObj.comp_pow]
      exact congrArg (· ^ (p ^ r)) (Category.comp_id χ.hom.hom)

theorem twistedCharacters : Specs.FlagRelativeFrobeniusAtlas.TwistedCharacters.{u} := by
  intro k _ p r _ _ _
  let W := groupAlgebra k IntegerCharacters
  let e := splitGroupTwistIso (k := k) p r IntegerCharacters
  refine ⟨e, ?_, ?_⟩
  · intro H χ F hF
    have h : F = (relativeGroupFrobenius p r).app H := by
      apply Grp.hom_ext
      rw [relativeGroupFrobenius_hom]
      exact relativeFrobenius_unique p r H.X F.hom.hom hF
    exact (congrArg (· ≫ twistCharacter p r χ) h).trans (relativeFrobenius_character p r χ)
  · intro D χ
    letI := (iterateFrobenius k p r).toAlgebra
    let d := affineTwistGroupIso p r D
    let i := splitAlgebraTwistIso (k := k) p r IntegerCharacters
    let χ' : W ⟶ FiniteDistributions.twistCoordinates k p r D := i.inv ≫ affineTwistMap p r χ
    have hcoordinate : χ'.hom (MonoidAlgebra.of k _ integerGenerator) =
        Specs.RelativeFrobenius.scalarTensor (iterateFrobenius k p r) D 1
          (χ.hom (MonoidAlgebra.of k _ integerGenerator)) := by
      change (extendedHopfMap k χ).hom (i.inv.hom (MonoidAlgebra.of k _ integerGenerator)) = _
      rw [show i.inv.hom (MonoidAlgebra.of k _ integerGenerator) =
          Specs.RelativeFrobenius.scalarTensor (iterateFrobenius k p r) W 1
            (MonoidAlgebra.of k _ integerGenerator) from
        splitAlgebraScalarIso_inv_of k IntegerCharacters integerGenerator]
      rfl
    refine ⟨d, χ', affineTwistGroupIso_hom_left p r D, ?_, hcoordinate, ?_⟩
    · change specGroupMap χ' = d.hom ≫
        (twistGroup p r).map (specGroupMap χ) ≫
          (affineTwistGroupIso p r W).inv ≫ specGroupMap i.inv
      change specGroupMap χ' = (affineTwistGroupIso p r D).hom ≫
        (twistGroup p r).map (specGroupMap χ) ≫
          (affineTwistGroupIso p r W).inv ≫ specGroupMap i.inv
      have hn := affineTwistGroupIso_natural p r χ
      rw [← Category.assoc _ ((twistGroup p r).map (specGroupMap χ)), ← hn,
        Category.assoc, Iso.hom_inv_id_assoc]
      change (hopfSpec (CommRingCat.of k)).map (i.inv ≫ affineTwistMap p r χ).op = _
      rw [op_comp, Functor.map_comp]
    · intro f hf
      rw [hcoordinate, hf, one_smul]


open Specs.FlagRelativeFrobeniusAtlas (primeFieldMap)

omit [IsAlgClosed k] in
private theorem frobenius_over_primeField :
    baseFrobenius (k := k) p r ≫ primeFieldMap p = primeFieldMap p := by
  rw [baseFrobenius, primeFieldMap, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  rw [← RingHom.cancel_right (f := (ULift.ringEquiv : ULift.{u} (ZMod p) ≃+* _).symm.toRingHom)
    (hf := ULift.ringEquiv.symm.surjective)]
  exact Subsingleton.elim _ _

/-- The prime-field flag model and its marked morphisms identify with their twists. -/
def primeFieldModelIso :
    Over.pullback (primeFieldMap (k := k) p) ⋙ twist p r ≅
      Over.pullback (primeFieldMap (k := k) p) :=
  Functor.isoWhiskerLeft _ (twistBaseChangeIso p r) ≪≫
    (Over.pullbackComp (baseFrobenius (k := k) p r) (primeFieldMap p)).symm ≪≫
    eqToIso (congrArg (fun f => Over.pullback f) (frobenius_over_primeField (k := k) p r))

theorem primeFieldModels : Specs.FlagRelativeFrobeniusAtlas.PrimeFieldModels.{u} :=
  fun {_} _ p r _ _ _ => ⟨primeFieldModelIso p r⟩

/-- The comparison on an identified scalar extension of a marked diagram. -/
def primeFieldMarkingIso {J : Type*} [Category J]
    (D₀ : J ⥤ Over (Spec (CommRingCat.of (ULift.{u} (ZMod p)))))
    (D : J ⥤ SchemeOver k)
    (i : D₀ ⋙ Over.pullback (primeFieldMap (k := k) p) ≅ D) : D ⋙ twist p r ≅ D :=
  Functor.isoWhiskerRight i.symm (twist p r) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft D₀ (primeFieldModelIso p r) ≪≫ i

theorem twistPreservesSplitTorus :
    Specs.FlagRelativeFrobeniusAtlas.TwistPreservesSplitTorus.{u} := by
  intro k _ p r _ _ _ T h
  obtain ⟨n, ⟨e⟩⟩ := h
  obtain ⟨j⟩ := CharacterDescent.standardSplitTorus (k := k) n
  refine ⟨n, ⟨(twistGroup p r).mapIso (e ≪≫ j.symm) ≪≫
    splitGroupTwistIso p r (Specs.CharacterDescent.StandardLattice.{u} n) ≪≫ j⟩⟩

theorem hopfKernelActsTrivially :
    Specs.FlagRelativeFrobeniusAtlas.HopfKernelActsTrivially.{u} := by
  intro k _ p r _ _ _ A f hf e F hF
  let Q := hopfQuotient A (Specs.kernelIdeal f)
  let q := hopfQuotientMap A (Specs.kernelIdeal f)
  let B := FiniteDistributions.twistCoordinates k p r A
  have hp := (Grp.forget (SchemeOver k)).map_isPullback (schemeKernel k f).1
  let e₀ : (specGroup (CommHopfAlgCat.of k k)).X ≅ 𝟙_ (SchemeOver k) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
      rw [Spec.map_id, Category.comp_id])
  have ht := (isTerminalTensorUnit (C := SchemeOver k)).ofIso e₀.symm
  have hw : (specGroupMap q).hom.hom ≫ (specGroupMap f).hom.hom = 1 := by
    change IsPullback (specGroupMap q).hom.hom (specGroupMap (hopfUnit Q)).hom.hom
      (specGroupMap f).hom.hom (specGroupMap (hopfCounit B)).hom.hom at hp
    rw [hp.w, ht.hom_ext (specGroupMap (hopfUnit Q)).hom.hom 1, MonObj.one_comp]
  rw [← hF, ← Category.assoc]
  change ((specGroupMap q).hom.hom ≫ (specGroupMap f).hom.hom) ≫ e.hom.hom.hom = 1
  rw [hw, MonObj.one_comp]

theorem affineFrobeniusKernel_toUnit (A : HopfAlgebraCategory k) :
    (FiniteDistributions.frobeniusKernelInclusion p r A ≫
      (relativeGroupFrobenius p r).app (specGroup A)).hom.hom = 1 := by
  letI := hopfKernelIdeal k (FiniteDistributions.frobeniusPullback p r A)
  exact hopfKernelActsTrivially p r A _ (affineTwistGroupIso p r A) _
    (affineFrobenius_agrees p r A)

open Specs.FlagRelativeFrobeniusAtlas (twistSubgroup twistAffineGroup)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.QuotientEmbedding (Presentation)
open Specs.HomogeneousQuotient (rightMultiplication)
open private projection_eq_iff_of_pullback compareRepresentatives compareRepresentatives_projection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private represent_of_fppf from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

theorem twistedFlagQuotient : Specs.FlagRelativeFrobeniusAtlas.TwistedFlagQuotient.{u} := by
  intro k _ p r _ _ _ G P Q
  let H := twistSubgroup p r P.negative
  let T := twist (k := k) p r
  let q := T.map Q.projection
  let e := PreservesLimitPair.iso T G.val.X P.negative.group.X
  have hfst : e.inv ≫ T.map prod.fst = prod.fst :=
    PreservesLimitPair.iso_inv_fst T _ _
  have hsnd : e.inv ≫ T.map prod.snd = prod.snd :=
    PreservesLimitPair.iso_inv_snd T _ _
  have hmul : e.inv ≫ T.map (rightMultiplication P.negative) = rightMultiplication H := by
    change e.inv ≫ T.map (prod.fst * (prod.snd ≫ P.negative.inclusion.hom.hom)) = _
    simp only [T.map_mul, T.map_comp, MonObj.comp_mul, ← Category.assoc, hfst, hsnd]
    rfl
  have hp : IsPullback prod.fst (rightMultiplication H) q q :=
    (T.map_isPullback (HomogeneousQuotient.quotientPullback Q)).of_iso' e.symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (hfst.trans (Category.comp_id _).symm) (hmul.trans (Category.comp_id _).symm)
      (by simp [q]) (by simp [q])
  letI : Flat q.left := Q.flat
  letI : Surjective q.left := Q.surjective
  letI : LocallyOfFinitePresentation q.left := Q.finitePresentation
  exact ⟨hp, represent_of_fppf H q (projection_eq_iff_of_pullback (H := H) q hp)⟩

theorem twistedFlagPresentation : Specs.FlagRelativeFrobeniusAtlas.TwistedFlagPresentation.{u} := by
  intro k _ p r _ _ _ G P Q
  let F := twistGroup (k := k) p r
  let H := twistSubgroup p r P.negative
  let G' := twistAffineGroup p r G
  obtain ⟨Q'⟩ := (HomogeneousQuotient.homogeneousQuotient k G' H).1
  obtain ⟨_, e, he⟩ := twistedFlagQuotient p r Q
  refine ⟨Q', compareRepresentatives Q' e, compareRepresentatives_projection Q' _ e he,
    twistPreservesSplitTorus p r P.torus.group P.split, ?_⟩
  intro b
  constructor
  · change F.map b.inclusion ≫ F.map P.negative.inclusion = F.map P.torus.inclusion
    rw [← F.map_comp, b.inclusion_comp]
  · change F.map b.inclusion ≫ F.map b.projection = 𝟙 _
    rw [← F.map_comp, b.section_projection, F.map_id]

open Functor.LaxMonoidal in
/-- Transport of an action along the scalar twist's product comparison. -/
@[instance_reducible] private def mapGroupAction {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (T : C ⥤ D) [T.Monoidal] {G : Grp C} {X : C} (a : ModObj G.X X) :
    ModObj (T.mapGrp.obj G).X (T.obj X) where
  smul := Functor.LaxMonoidal.μ T G.X X ≫ T.map a.smul
  one_smul := by
    change ((ε T ≫ T.map η[G.X]) ▷ T.obj X) ≫ Functor.LaxMonoidal.μ T G.X X ≫ T.map a.smul = _
    have h : η[G.X] ▷ X ≫ a.smul = (λ_ X).hom := a.one_smul
    simp only [comp_whiskerRight, Category.assoc, μ_natural_left_assoc]
    rw [← T.map_comp, h]
    exact (left_unitality T X).symm
  mul_smul := by
    change ((Functor.LaxMonoidal.μ T G.X G.X ≫ T.map μ[G.X]) ▷ T.obj X) ≫ Functor.LaxMonoidal.μ T G.X X ≫ T.map a.smul =
      (α_ (T.obj G.X) (T.obj G.X) (T.obj X)).hom ≫
        T.obj G.X ◁ (Functor.LaxMonoidal.μ T G.X X ≫ T.map a.smul) ≫ Functor.LaxMonoidal.μ T G.X X ≫ T.map a.smul
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc, μ_natural_left_assoc,
      μ_natural_right_assoc]
    have h : μ[G.X] ▷ X ≫ a.smul = (α_ G.X G.X X).hom ≫ G.X ◁ a.smul ≫ a.smul :=
      a.mul_smul
    rw [← T.map_comp, h]
    simp only [T.map_comp, associativity_assoc]


/-- The action on the scalar twist of a scheme with a group action. -/
abbrev twistAction {G : GroupScheme k} {X : SchemeOver k} (a : ModObj G.X X) :
    ModObj ((twistGroup p r).obj G).X ((twist p r).obj X) :=
  mapGroupAction (twist p r) a

open Functor.LaxMonoidal in
private theorem twistAction_quotient {M : GroupScheme k} {X : SchemeOver k}
    (a : ModObj M.X X) (q : M.X ⟶ X)
    (hq : μ[M.X] ≫ q = (𝟙 M.X ⊗ₘ q) ≫ a.smul) :
    μ[((twistGroup p r).obj M).X] ≫ (twist p r).map q =
      (𝟙 _ ⊗ₘ (twist p r).map q) ≫ (twistAction p r a).smul := by
  let T := twist (k := k) p r
  have hμ := μ_natural T (𝟙 M.X) q
  rw [T.map_id] at hμ
  change (Functor.LaxMonoidal.μ T M.X M.X ≫ T.map μ[M.X]) ≫ T.map q =
    (𝟙 _ ⊗ₘ T.map q) ≫ (Functor.LaxMonoidal.μ T M.X X ≫ T.map a.smul)
  rw [Category.assoc, ← T.map_comp, hq, T.map_comp, ← Category.assoc, ← Category.assoc, hμ]

private theorem relativeFrobenius_action {M : GroupScheme k} {X : SchemeOver k}
    (a : ModObj M.X X) :
    a.smul ≫ (relativeFrobenius p r).app X =
      ((relativeFrobenius p r).app M.X ⊗ₘ (relativeFrobenius p r).app X) ≫
        (twistAction p r a).smul := by
  let T := twist (k := k) p r
  let F := relativeFrobenius (k := k) p r
  have h := NatTrans.IsMonoidal.tensor (τ := F) M.X X
  change 𝟙 _ ≫ F.app (M.X ⊗ X) =
    (F.app M.X ⊗ₘ F.app X) ≫ Functor.LaxMonoidal.μ T M.X X at h
  have h' : F.app (M.X ⊗ X) =
    (F.app M.X ⊗ₘ F.app X) ≫ Functor.LaxMonoidal.μ T M.X X :=
    (Category.id_comp _).symm.trans h
  calc
    a.smul ≫ F.app X = F.app (M.X ⊗ X) ≫ T.map a.smul := F.naturality a.smul
    _ = ((F.app M.X ⊗ₘ F.app X) ≫ Functor.LaxMonoidal.μ T M.X X) ≫ T.map a.smul :=
      congrArg (· ≫ T.map a.smul) h'
    _ = _ := Category.assoc _ _ _

theorem twistedFlagActions : Specs.FlagRelativeFrobeniusAtlas.TwistedFlagActions.{u} := by
  intro k _ p r _ _ _ G P Q a ha
  let F := relativeFrobenius (k := k) p r
  let a' := twistAction p r a
  refine ⟨(relativeGroupFrobenius p r).app G.val, F.app _, a', ?_,
    relativeFrobenius_formula p r Q.scheme, rfl, twistAction_quotient p r a Q.projection ha,
    ?_, ?_, ?_, ?_⟩
  · rw [relativeGroupFrobenius_hom]
    exact relativeFrobenius_formula p r G.val.X
  · rw [relativeGroupFrobenius_hom]
    exact F.naturality Q.projection
  · rw [relativeGroupFrobenius_hom]
    exact relativeFrobenius_action p r a
  · intro N hN
    let Y := (twist p r).obj Q.scheme
    have h : N.inclusion.hom.hom ≫ ((relativeGroupFrobenius p r).app G.val).hom.hom = 1 := hN.w
    change lift (fst N.group.X Y ≫ N.inclusion.hom.hom ≫
      ((relativeGroupFrobenius p r).app G.val).hom.hom) (snd N.group.X Y) ≫ a'.smul = _
    rw [h, MonObj.comp_one]
    letI := a'
    exact one_smul (N.group.X ⊗ Y ⟶ ((twistGroup p r).obj G.val).X) (snd N.group.X Y)
  · intro S x y h
    rw [h]
    letI := a'
    exact one_smul (S ⟶ ((twistGroup p r).obj G.val).X) y

section SplitMarking

open Specs.GeometricRadicals (IsSplitTorus IsTorus IsMaximalTorus IsReductive
  IsSmoothConnectedNormal IsTrivialSubgroup IsUnipotentRadical GeometricGroup
  geometricUnipotentRadical)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel IsSmoothConnectedSolvable)
open Specs.SchemeDerivedGroup (IsSubgroupOf IsSolvable)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Unipotent (IsUnipotent closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open private extendSubgroup subgroup_extend fieldSpecMap_isIso groupObjectsFunctor_isEquivalence
  groupBaseChange_isEquivalence pullback_subgroup_over_closed_field same_of_inclusion_iso
  smooth_extend_iff connected_extend_iso_iff isKBorel_iff_of_isAlgClosed
  smoothConnectedSolvable_of_iso geometricMaximal_of_maximal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private normalSubgroup_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
open private maximalTorus_of_geometricallyMaximal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private split_of_torus torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isTorus_iff_coordinates torus_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private solvable_iff_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private trivial_of_subgroup_of_trivial from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private unipotent_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent


open Specs.AdjointRepresentation (GroupPoints dualMap reduction constants scale)
open Specs.CharacterPairing (characterValue adjointWeightVectors absoluteRoots)
open Specs.BorelsAndChambers (subgroupRoots)
open CocharacterDynamics (lieImage)

local notation "σ" => iterateFrobeniusEquiv k p r
local notation "W₁" => twist (k := k) p r
local notation "F₁" => twistGroup (k := k) p r
local notation "test" => (testSpec k)
local notation "dual" => fun (R : TestAlgebra k) => CommAlgCat.of k (DualNumber R)
local notation "base" => CommAlgCat.of k k


private instance twistGroupEquivalence : (F₁).IsEquivalence :=
  groupObjectsFunctor_isEquivalence W₁

private theorem twistSmooth (X : SchemeOver k) : Smooth ((W₁).obj X).hom ↔ Smooth X.hom := by
  let t := Spec.map (CommRingCat.ofHom (iterateFrobeniusEquiv k p r).symm.toRingHom)
  letI : IsIso t :=
    (Scheme.Spec.mapIso (iterateFrobeniusEquiv k p r).symm.toCommRingCatIso.op).isIso_hom
  exact MorphismProperty.cancel_right_of_respectsIso @Smooth X.hom t

private theorem twistGeometricallyConnected (X : SchemeOver k) :
    GeometricallyConnected ((W₁).obj X).hom ↔ GeometricallyConnected X.hom := by
  let t := Spec.map (CommRingCat.ofHom (iterateFrobeniusEquiv k p r).symm.toRingHom)
  letI : IsIso t :=
    (Scheme.Spec.mapIso (iterateFrobeniusEquiv k p r).symm.toCommRingCatIso.op).isIso_hom
  exact MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected X.hom t

private theorem twistSubgroupOf {G : GroupScheme k} {A B : ClosedSubgroup G} :
    IsSubgroupOf (twistSubgroup p r A) (twistSubgroup p r B) ↔ IsSubgroupOf A B := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(F₁).preimage f, (F₁).map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage]
    exact hf
  · rintro ⟨f, hf⟩
    exact ⟨(F₁).map f, ((F₁).map_comp f B.inclusion).symm.trans (congrArg (F₁).map hf)⟩

private theorem twistSubgroup_preimage {G : GroupScheme k}
    (B' : ClosedSubgroup ((F₁).obj G)) :
    ∃ (B : ClosedSubgroup G) (e : (F₁).obj B.group ≅ B'.group),
      e.hom ≫ B'.inclusion = (F₁).map B.inclusion := by
  let H := (F₁).asEquivalence.inverse.obj B'.group
  let e : (F₁).obj H ≅ B'.group := (F₁).asEquivalence.counitIso.app _
  let f : H ⟶ G := (F₁).preimage (e.hom ≫ B'.inclusion)
  have hf : (F₁).map f = e.hom ≫ B'.inclusion := (F₁).map_preimage _
  have hclosed : IsClosedImmersion f.hom.hom.left := by
    change IsClosedImmersion ((F₁).map f).hom.hom.left
    rw [hf]
    letI := B'.isClosedImmersion
    letI : IsIso e.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.hom
    exact IsClosedImmersion.comp e.hom.hom.hom.left B'.inclusion.hom.hom.left
  exact ⟨⟨H, f, hclosed⟩, e, hf.symm⟩

omit [IsAlgClosed k] in
private theorem subgroupOf_transitive {G : GroupScheme k} {A B C : ClosedSubgroup G}
    (h : IsSubgroupOf A B) (h' : IsSubgroupOf B C) : IsSubgroupOf A C := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  exact ⟨f ≫ g, by rw [Category.assoc, hg, hf]⟩


private def twistTestComparison {A B : TestAlgebra k} (e : A ≃+* B)
    (he : ∀ a : k, e (algebraMap k A a) = algebraMap k B (σ a)) :
    (test).obj (op B) ≅ (W₁).obj ((test).obj (op A)) := by
  let i := Scheme.Spec.mapIso e.toCommRingCatIso.op
  refine Over.isoMk i ?_
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫ inverseBaseFrobenius p r) =
      Spec.map (CommRingCat.ofHom (algebraMap k B))
  rw [← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change e (algebraMap k A ((σ).symm a)) = algebraMap k B a
  rw [he, RingEquiv.apply_symm_apply]

private theorem twistTestComparison_left {A B : TestAlgebra k} (e : A ≃+* B) (he) :
    (twistTestComparison p r e he).hom.left = Spec.map (CommRingCat.ofHom e.toRingHom) :=
  rfl

open scoped CategoryTheory.Obj in
private def twistSections {X Y : SchemeOver k} (e : Y ≅ (W₁).obj X) (G : GroupScheme k) :
    (X ⟶ G.X) ≃* (Y ⟶ ((F₁).obj G).X) := by
  let j := (Functor.FullyFaithful.ofFullyFaithful W₁).homMulEquiv (X := X) (M := G.X)
  refine j.trans
    { toFun := fun x => e.hom ≫ x
      invFun := fun x => e.inv ≫ x
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro x
    exact e.inv_hom_id_assoc x
  · intro x
    exact e.hom_inv_id_assoc x
  · intro x y
    exact MonObj.comp_mul _ x y

private theorem twistSections_apply {X Y : SchemeOver k} (e : Y ≅ (W₁).obj X)
    (G : GroupScheme k) (x : X ⟶ G.X) :
    twistSections p r e G x = e.hom ≫ (W₁).map x := rfl

private theorem twistSections_postcomp {X Y : SchemeOver k} (e : Y ≅ (W₁).obj X)
    {G H : GroupScheme k} (f : G ⟶ H) (x : X ⟶ G.X) :
    twistSections p r e H (x ≫ f.hom.hom) =
      twistSections p r e G x ≫ ((F₁).map f).hom.hom := by
  simp only [twistSections_apply, Functor.map_comp, Category.assoc]
  rfl

private theorem twistTestPoints_natural {A B A' B' : TestAlgebra k}
    {i : A ≃+* A'} {j : B ≃+* B'} (hi : ∀ a : k, i (algebraMap k A a) = algebraMap k A' (σ a))
    (hj : ∀ a : k, j (algebraMap k B a) = algebraMap k B' (σ a))
    (a : A ⟶ B) (a' : A' ⟶ B') (h : ∀ x : A, j (a.hom x) = a'.hom (i x))
    (G : GroupScheme k) (x : Points G.X A) :
    twistSections p r (twistTestComparison p r j hj) G (mapPoints a x) =
      mapPoints a' (twistSections p r (twistTestComparison p r i hi) G x) := by
  have hs : (twistTestComparison p r j hj).hom ≫ (W₁).map ((test).map a.op) =
      (test).map a'.op ≫ (twistTestComparison p r i hi).hom := by
    apply Over.OverMorphism.ext
    change (twistTestComparison p r j hj).hom.left ≫ Spec.map (CommRingCat.ofHom a.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom a'.hom.toRingHom) ≫ (twistTestComparison p r i hi).hom.left
    rw [twistTestComparison_left, twistTestComparison_left, ← Spec.map_comp, ← Spec.map_comp,
      Spec.map_inj]
    exact CommRingCat.hom_ext (RingHom.ext h)
  simp only [twistSections_apply, mapPoints, Functor.map_comp, ← Category.assoc, hs]

private abbrev restrictTwistTest (R : TestAlgebra k) : TestAlgebra k :=
  letI := (iterateFrobenius k p r).toAlgebra
  (restrictTestAlgebra k k).obj R

private abbrev twistTest (R : TestAlgebra k) :
    (test).obj (op R) ≅ (W₁).obj ((test).obj (op (restrictTwistTest p r R))) :=
  twistTestComparison p r (A := restrictTwistTest p r R) (B := R)
    (RingEquiv.refl R) (fun _ => rfl)

private abbrev twistDualTest (R : TestAlgebra k) :
    (test).obj (op (dual R)) ≅ (W₁).obj ((test).obj (op (dual (restrictTwistTest p r R)))) :=
  twistTestComparison p r (A := dual (restrictTwistTest p r R)) (B := dual R)
    (RingEquiv.refl (DualNumber R)) (fun _ => by apply TrivSqZeroExt.ext <;> rfl)

private def frobeniusDualEquiv : DualNumber k ≃+* DualNumber k :=
  RingEquiv.ofBijective (InfinitesimalCommutator.mapCoefficients (σ).toRingHom) (by
    constructor
    · intro a b h
      exact TrivSqZeroExt.ext ((σ).injective (congrArg TrivSqZeroExt.fst h))
        ((σ).injective (congrArg TrivSqZeroExt.snd h))
    · intro a
      exact ⟨((σ).symm a.fst, (σ).symm a.snd),
        TrivSqZeroExt.ext ((σ).apply_symm_apply _) ((σ).apply_symm_apply _)⟩)

private abbrev twistDualBase :
    (test).obj (op (dual base)) ≅ (W₁).obj ((test).obj (op (dual base))) :=
  twistTestComparison p r (A := dual base) (B := dual base) (frobeniusDualEquiv p r) (fun a => by
    apply TrivSqZeroExt.ext
    · rfl
    · exact map_zero σ)

private abbrev twistOrdinaryBase : (test).obj (op base) ≅ (W₁).obj ((test).obj (op base)) :=
  twistTestComparison p r (A := base) (B := base) σ (fun _ => rfl)

private abbrev twistTestPoints (G : GroupScheme k) (R : TestAlgebra k) :=
  twistSections p r (twistTest p r R) G

private abbrev twistDualPoints (G : GroupScheme k) (R : TestAlgebra k) :=
  twistSections p r (twistDualTest p r R) G

private theorem twistTangentPoints_reduction (G : GroupScheme k)
    (x : GroupPoints G (dual base)) :
    mapPoints (dualReduction k) (twistSections p r (twistDualBase p r) G x) =
      twistSections p r (twistOrdinaryBase p r) G (mapPoints (dualReduction k) x) :=
  (twistTestPoints_natural p r _ _ (dualReduction k) (dualReduction k) (fun _ => rfl) G x).symm

private def twistLie (G : GroupScheme k) : Lie k G ≃ Lie k ((F₁).obj G) := by
  let f := twistSections p r (twistDualBase p r) G
  let g := twistSections p r (twistOrdinaryBase p r) G
  refine ⟨fun v => ⟨f v.toMul.val, ?_⟩, fun v => ⟨f.symm v.toMul.val, ?_⟩, ?_, ?_⟩
  · change mapPoints (dualReduction k) (f v.toMul.val) = 1
    change mapPoints (dualReduction k) (twistSections p r (twistDualBase p r) G v.toMul.val) = 1
    rw [twistTangentPoints_reduction]
    change twistSections p r (twistOrdinaryBase p r) G (reduceTangentPoints G v.toMul.val) = 1
    rw [v.toMul.property, map_one]
  · change mapPoints (dualReduction k) (f.symm v.toMul.val) = 1
    apply g.injective
    rw [map_one]
    change twistSections p r (twistOrdinaryBase p r) G
      (mapPoints (dualReduction k) (f.symm v.toMul.val)) = _
    rw [← twistTangentPoints_reduction]
    change mapPoints (dualReduction k) (f (f.symm v.toMul.val)) = _
    rw [f.apply_symm_apply]
    exact v.toMul.property
  · intro v
    exact Subtype.ext (f.symm_apply_apply v.toMul.val)
  · intro v
    exact Subtype.ext (f.apply_symm_apply v.toMul.val)

private theorem twistLie_zero (G : GroupScheme k) : twistLie p r G 0 = 0 :=
  Subtype.ext ((twistSections p r (twistDualBase p r) G).map_one)

private theorem twistLie_natural {G H : GroupScheme k} (f : G ⟶ H) (v : Lie k G) :
    twistLie p r H (mapPointKernel f v) = mapPointKernel ((F₁).map f) (twistLie p r G v) :=
  Subtype.ext (twistSections_postcomp p r (twistDualBase p r) f v.toMul.val)

private theorem twistDualPoints_constants {G : GroupScheme k} (R : TestAlgebra k)
    (x : GroupPoints G (restrictTwistTest p r R)) :
    twistDualPoints p r G R (mapPoints (constants (restrictTwistTest p r R)) x) =
      mapPoints (constants R) (twistTestPoints p r G R x) :=
  twistTestPoints_natural p r _ _ _ _ (fun _ => rfl) G x

private theorem twistDualPoints_scale {G : GroupScheme k} (R : TestAlgebra k) (a : R)
    (x : GroupPoints G (dual (restrictTwistTest p r R))) :
    twistDualPoints p r G R (mapPoints (scale (restrictTwistTest p r R) a) x) =
      mapPoints (scale R a) (twistDualPoints p r G R x) :=
  twistTestPoints_natural p r _ _ _ _ (fun _ => rfl) G x

private abbrev baseToTest (R : TestAlgebra k) : base ⟶ R :=
  ConcreteCategory.ofHom (C := TestAlgebra k) (X := base) (Y := R) (Algebra.ofId k R)

private theorem twistDualPoints_lie {G : GroupScheme k} (R : TestAlgebra k) (v : Lie k G) :
    twistDualPoints p r G R (mapPoints (dualMap (baseToTest (restrictTwistTest p r R))) v.toMul.val) =
      mapPoints (dualMap (baseToTest R)) (twistLie p r G v).toMul.val :=
  twistTestPoints_natural p r _ _ _ _ (fun _ => rfl) G v.toMul.val

private theorem twistLie_mem_image {G : GroupScheme k} (B : ClosedSubgroup G) (v : Lie k G) :
    twistLie p r G v ∈ lieImage (twistSubgroup p r B) ↔ v ∈ lieImage B := by
  change (∃ x, mapPointKernel ((F₁).map B.inclusion) x = twistLie p r G v) ↔
    (∃ y, mapPointKernel B.inclusion y = v)
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (twistLie p r B.group).surjective x
    exact ⟨y, (twistLie p r G).injective ((twistLie_natural p r B.inclusion y).trans hx)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨twistLie p r B.group x, (twistLie_natural p r B.inclusion x).symm⟩


private theorem restrictTwistTest_surjective :
    Function.Surjective (restrictTwistTest (k := k) p r) := by
  intro R
  let a : Algebra k R := ((@algebraMap k R _ _ R.algebra).comp (σ).symm.toRingHom).toAlgebra
  let S := @CommAlgCat.of k _ R R.commRing a
  refine ⟨S, ?_⟩
  apply congrArg (fun b : Algebra k R => @CommAlgCat.of k _ R R.commRing b)
  apply Algebra.algebra_ext
  intro x
  change @algebraMap k R _ _ R.algebra ((σ).symm (σ x)) = @algebraMap k R _ _ R.algebra x
  exact congrArg (@algebraMap k R _ _ R.algebra) ((σ).symm_apply_apply x)

private theorem twistTestPoints_left (G : GroupScheme k) (R : TestAlgebra k)
    (x : GroupPoints G (restrictTwistTest p r R)) :
    (twistTestPoints p r G R x).left = x.left := by
  change ((twistTest p r R).hom ≫ (W₁).map x).left = _
  change (twistTest p r R).hom.left ≫ x.left = _
  rw [twistTestComparison_left]
  change Spec.map (𝟙 (CommRingCat.of R)) ≫ x.left = _
  rw [Spec.map_id, Category.id_comp]

private def scalarCoordinateInclusion (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) : A →+* extendedHopf K A :=
  (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom

private def twistCoordinateInclusion (A : HopfAlgebraCategory k) :
    A →+* FiniteDistributions.twistCoordinates k p r A :=
  letI := (iterateFrobenius k p r).toAlgebra
  scalarCoordinateInclusion k A

omit [IsAlgClosed k] in
private theorem affineTwistProjection_spec (A : HopfAlgebraCategory k) :
    affineTwistProjection p r A = Spec.map (CommRingCat.ofHom (twistCoordinateInclusion p r A)) :=
  rfl

private theorem gmTwist_inv_fixes_monomial :
    let A := groupAlgebra k IntegerCharacters
    ∃ a : A →+* A,
      (splitGroupTwistIso (k := k) p r IntegerCharacters).inv.hom.hom.left =
        Spec.map (CommRingCat.ofHom a) ∧
      a (MonoidAlgebra.of k _ integerGenerator) = MonoidAlgebra.of k _ integerGenerator := by
  let A := groupAlgebra k IntegerCharacters
  let e : FiniteDistributions.twistCoordinates k p r A ≅ A :=
    splitAlgebraTwistIso (k := k) p r IntegerCharacters
  let f := twistCoordinateInclusion p r A
  refine ⟨e.hom.hom.toAlgHom.toRingHom.comp f, ?_, ?_⟩
  · change (specGroupMap e.hom).hom.hom.left ≫
      (affineTwistGroupIso p r A).hom.hom.hom.left = _
    rw [affineTwistGroupIso_hom_left, affineTwistProjection_spec]
    change Spec.map (CommRingCat.ofHom e.hom.hom.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f) = _
    rw [← Spec.map_comp]
    rfl
  · let z : A := MonoidAlgebra.of k _ integerGenerator
    change e.hom.hom (f z) = z
    have h : e.inv.hom z = f z := by
      letI := (iterateFrobenius k p r).toAlgebra
      exact splitAlgebraScalarIso_inv_of k IntegerCharacters integerGenerator
    rw [← h]
    exact DFunLike.congr_fun (congrArg (fun f : A ⟶ A => f.hom) e.inv_hom_id) z

private theorem twistCharacterValue {G : GroupScheme k} (χ : Character G) (R : TestAlgebra k)
    (t : GroupPoints G (restrictTwistTest p r R)) :
    characterValue (twistCharacter p r χ) R (twistTestPoints p r G R t) =
      characterValue χ (restrictTwistTest p r R) t := by
  let A := groupAlgebra k IntegerCharacters
  let M := specGroup A
  let e := splitGroupTwistIso (k := k) p r IntegerCharacters
  let x : Points M.X (restrictTwistTest p r R) := t ≫ χ.hom.hom
  let y : Points M.X R := twistTestPoints p r G R t ≫ (twistCharacter p r χ).hom.hom
  obtain ⟨a, ha, hz⟩ := gmTwist_inv_fixes_monomial (k := k) p r
  have h : y ≫ e.inv.hom.hom = twistTestPoints p r M R x := by
    have he : (twistCharacter p r χ).hom.hom ≫ e.inv.hom.hom =
        ((F₁).map χ).hom.hom := by
      change (Grp.forget _).map ((twistCharacter p r χ) ≫ e.inv) =
        (Grp.forget _).map ((F₁).map χ)
      exact congrArg (Grp.forget _).map (show _ from by
        change (((F₁).map χ) ≫ e.hom) ≫ e.inv = _
        rw [Category.assoc, e.hom_inv_id, Category.comp_id])
    change (twistTestPoints p r G R t ≫ (twistCharacter p r χ).hom.hom) ≫ e.inv.hom.hom = _
    rw [Category.assoc, he]
    exact (twistSections_postcomp p r (twistTest p r R) χ t).symm
  have hl : y.left ≫ Spec.map (CommRingCat.ofHom a) = x.left := by
    rw [← ha]
    change (y ≫ e.inv.hom.hom).left = _
    rw [h, twistTestPoints_left]
  let U := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f := (U.preimage x).unop
  let g := (U.preimage y).unop
  let φ := ((commAlgCatEquivUnder (CommRingCat.of k)).functor.map f).right
  let ψ := ((commAlgCatEquivUnder (CommRingCat.of k)).functor.map g).right
  have hx : x.left = Spec.map φ :=
    congrArg Over.Hom.left (U.map_preimage x).symm
  have hy : y.left = Spec.map ψ :=
    congrArg Over.Hom.left (U.map_preimage y).symm
  rw [hx, hy, ← Spec.map_comp, Spec.map_inj] at hl
  let z : A := MonoidAlgebra.single integerGenerator 1
  have hh := congrArg (fun b : CommRingCat.of A ⟶ CommRingCat.of R => b z) hl
  change ψ (a z) = φ z at hh
  rw [show a z = z from hz] at hh
  exact hh

private def testsWeight {G : GroupScheme k} (T : ClosedSubgroup G) (χ : Character T.group)
    (R : TestAlgebra k) (t : GroupPoints T.group R) (v : Lie k G) : Prop :=
  let x := mapPoints (dualMap (baseToTest R)) v.toMul.val
  let g := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
  g * x * g⁻¹ = mapPoints (scale R (characterValue χ R t)) x

private theorem twist_testsWeight {G : GroupScheme k} (T : ClosedSubgroup G)
    (χ : Character T.group) (R : TestAlgebra k)
    (t : GroupPoints T.group (restrictTwistTest p r R)) (v : Lie k G) :
    testsWeight (twistSubgroup p r T) (twistCharacter p r χ) R
      (twistTestPoints p r T.group R t) (twistLie p r G v) ↔
      testsWeight T χ (restrictTwistTest p r R) t v := by
  let S := restrictTwistTest p r R
  let x := mapPoints (dualMap (baseToTest S)) v.toMul.val
  let g := mapPoints (constants S) (t ≫ T.inclusion.hom.hom)
  let x' := mapPoints (dualMap (baseToTest R)) (twistLie p r G v).toMul.val
  let g' := mapPoints (constants R)
    (twistTestPoints p r T.group R t ≫ ((F₁).map T.inclusion).hom.hom)
  have hx : x' = twistDualPoints p r G R x := (twistDualPoints_lie p r R v).symm
  have hg : g' = twistDualPoints p r G R g := by
    change mapPoints (constants R)
      (twistTestPoints p r T.group R t ≫ ((F₁).map T.inclusion).hom.hom) = _
    rw [← twistSections_postcomp p r (twistTest p r R)]
    exact (twistDualPoints_constants p r R (t ≫ T.inclusion.hom.hom)).symm
  change g' * x' * (g')⁻¹ = mapPoints
    (scale R (characterValue (twistCharacter p r χ) R (twistTestPoints p r T.group R t))) x' ↔
    g * x * g⁻¹ = mapPoints (scale S (characterValue χ S t)) x
  rw [hx, hg, twistCharacterValue, ← twistDualPoints_scale, ← map_inv _ g,
    ← map_mul, ← map_mul]
  exact (twistDualPoints p r G R).injective.eq_iff

private theorem twistLie_mem_weight {G : GroupScheme k} (T : ClosedSubgroup G)
    (χ : Character T.group) (v : Lie k G) :
    twistLie p r G v ∈ adjointWeightVectors (twistSubgroup p r T) (twistCharacter p r χ) ↔
      v ∈ adjointWeightVectors T χ := by
  change (∀ R t, testsWeight (twistSubgroup p r T) (twistCharacter p r χ) R t (twistLie p r G v)) ↔
    (∀ R t, testsWeight T χ R t v)
  constructor
  · intro h R
    obtain ⟨S, rfl⟩ := restrictTwistTest_surjective p r R
    intro t
    exact (twist_testsWeight p r T χ S t v).mp (h S (twistTestPoints p r T.group S t))
  · intro h R t
    obtain ⟨s, rfl⟩ := (twistTestPoints p r T.group R).surjective t
    exact (twist_testsWeight p r T χ R s v).mpr (h _ s)

private def twistCharacterEquiv (T : GroupScheme k) :
    Character T ≃ Character ((F₁).obj T) := by
  let Gm := specGroup (groupAlgebra k IntegerCharacters)
  let e := splitGroupTwistIso (k := k) p r IntegerCharacters
  refine ((Functor.FullyFaithful.ofFullyFaithful F₁).homEquiv (X := T) (Y := Gm)).trans
    { toFun := fun χ => χ ≫ e.hom
      invFun := fun χ => χ ≫ e.inv
      left_inv := fun χ => by simp
      right_inv := fun χ => by simp }

private theorem twistCharacter_one (T : GroupScheme k) :
    twistCharacter p r (1 : Character T) = 1 := by
  let Gm := specGroup (groupAlgebra k IntegerCharacters)
  let i := splitGroupTwistIso (k := k) p r IntegerCharacters
  change (F₁).map (0 : T ⟶ Gm) ≫ i.hom = (0 : (F₁).obj T ⟶ Gm)
  rw [Functor.map_zero, zero_comp]

private theorem twistCharacter_mem_roots {G : GroupScheme k} (T : ClosedSubgroup G)
    (χ : Character T.group) :
    twistCharacter p r χ ∈ absoluteRoots (twistSubgroup p r T) ↔ χ ∈ absoluteRoots T := by
  have hOne : twistCharacter p r χ = 1 ↔ χ = 1 := by
    rw [← twistCharacter_one p r T.group]
    exact (twistCharacterEquiv p r T.group).injective.eq_iff
  have hZero (v : Lie k G) : twistLie p r G v = 0 ↔ v = 0 := by
    rw [← twistLie_zero p r G]
    exact (twistLie p r G).injective.eq_iff
  change (twistCharacter p r χ ≠ 1 ∧ ∃ v ∈ _, v ≠ 0) ↔ (χ ≠ 1 ∧ ∃ v ∈ _, v ≠ 0)
  rw [ne_eq, ne_eq, hOne]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨w, hw, h0⟩
    obtain ⟨v, rfl⟩ := (twistLie p r G).surjective w
    exact ⟨v, (twistLie_mem_weight p r T χ v).mp hw, fun h => h0 ((hZero v).mpr h)⟩
  · rintro ⟨v, hv, h0⟩
    exact ⟨twistLie p r G v, (twistLie_mem_weight p r T χ v).mpr hv, fun h => h0 ((hZero v).mp h)⟩

private def twistRootEquiv {G : GroupScheme k} (T : ClosedSubgroup G) :
    ↥(absoluteRoots T) ≃ ↥(absoluteRoots (twistSubgroup p r T)) :=
  (twistCharacterEquiv p r T.group).subtypeEquiv fun χ => (twistCharacter_mem_roots p r T χ).symm

private theorem twistRoot_mem_subgroupRoots {G : GroupScheme k} (T B : ClosedSubgroup G)
    (α : ↥(absoluteRoots T)) :
    twistRootEquiv p r T α ∈ subgroupRoots (twistSubgroup p r T) (twistSubgroup p r B) ↔
      α ∈ subgroupRoots T B := by
  change adjointWeightVectors (twistSubgroup p r T) (twistCharacter p r α.val) ⊆
    lieImage (twistSubgroup p r B) ↔ adjointWeightVectors T α.val ⊆ lieImage B
  constructor
  · intro h v hv
    exact (twistLie_mem_image p r B v).mp (h ((twistLie_mem_weight p r T α.val v).mpr hv))
  · intro h w
    obtain ⟨v, rfl⟩ := (twistLie p r G).surjective w
    intro hv
    exact (twistLie_mem_image p r B v).mpr (h ((twistLie_mem_weight p r T α.val v).mp hv))

private theorem twistOpposite {G : GroupScheme k} {T B C : ClosedSubgroup G}
    (h : Specs.OpenCell.AreOpposite T B C) :
    Specs.OpenCell.AreOpposite (twistSubgroup p r T) (twistSubgroup p r B) (twistSubgroup p r C) := by
  change subgroupRoots (twistSubgroup p r T) (twistSubgroup p r C) =
    (subgroupRoots (twistSubgroup p r T) (twistSubgroup p r B))ᶜ
  ext a
  obtain ⟨α, rfl⟩ := (twistRootEquiv p r T).surjective a
  rw [Set.mem_compl_iff, twistRoot_mem_subgroupRoots, twistRoot_mem_subgroupRoots]
  exact Set.ext_iff.mp h α


private theorem twistSmoothConnectedSolvable (A : AffineAlgebraicGroup k) :
    (Smooth ((F₁).obj A.val).X.hom ∧ ConnectedSpace ((F₁).obj A.val).X.left ∧
      IsSolvable ((F₁).obj A.val)) ↔ (Smooth A.val.X.hom ∧ ConnectedSpace A.val.X.left ∧
      IsSolvable A.val) := by
  let e := twistSections p r (asIso (Functor.LaxMonoidal.ε W₁)) A.val
  have hs := twistSmooth p r A.val.X
  constructor
  · rintro ⟨h, hc, hsol⟩
    haveI : Group.IsSolvable (𝟙_ (SchemeOver k) ⟶ ((F₁).obj A.val).X) :=
      (solvable_iff_sections (twistAffineGroup p r A) h hc).mp hsol
    exact ⟨hs.mp h, hc, (solvable_iff_sections A (hs.mp h) hc).mpr
      (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)⟩
  · rintro ⟨h, hc, hsol⟩
    haveI := (solvable_iff_sections A h hc).mp hsol
    exact ⟨hs.mpr h, hc, (solvable_iff_sections (twistAffineGroup p r A) (hs.mpr h) hc).mpr
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)⟩

private theorem twistBorel {A : AffineAlgebraicGroup k} (B : ClosedSubgroup A.val)
    (hB : IsKBorel B) : IsKBorel (twistSubgroup p r B) := by
  apply (isKBorel_iff_of_isAlgClosed (twistAffineGroup p r A) _).mpr
  have hb := (isKBorel_iff_of_isAlgClosed A B).mp hB
  refine ⟨(twistSmoothConnectedSolvable p r (closedSubgroupAlgebraicGroup B)).mpr hb.1, ?_⟩
  intro C hC hBC
  obtain ⟨D, e, he⟩ := twistSubgroup_preimage p r C
  let D' := twistSubgroup p r D
  have hSame := same_of_inclusion_iso (B := D') (C := C) e he
  have hd' : IsSmoothConnectedSolvable D' :=
    smoothConnectedSolvable_of_iso (closedSubgroupAlgebraicGroup C)
      (closedSubgroupAlgebraicGroup (G := twistAffineGroup p r A) D') e.symm hC
  have hd : IsSmoothConnectedSolvable D :=
    (twistSmoothConnectedSolvable p r (closedSubgroupAlgebraicGroup D)).mp hd'
  have hBD := (twistSubgroupOf p r).mp (subgroupOf_transitive hBC hSame.2)
  exact subgroupOf_transitive hSame.2 ((twistSubgroupOf p r).mpr (hb.2 D hd hBD))

omit [IsAlgClosed k] in
private theorem isTorus_of_isSplit {A : AffineAlgebraicGroup k} (h : IsSplitTorus A.val) :
    IsTorus A.val :=
  (isTorus_iff_coordinates A).mpr (torus_of_split h)

private theorem twistGeometricallyMaximal {A : AffineAlgebraicGroup k} (T : ClosedSubgroup A.val)
    (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T) :
    IsGeometricallyMaximal (twistSubgroup p r T) := by
  let T' := twistSubgroup p r T
  have ht : IsTorus T.group := isTorus_of_isSplit (A := closedSubgroupAlgebraicGroup T) hs
  have hT := maximalTorus_of_geometricallyMaximal A T ht hm
  have ht' : IsTorus T'.group := isTorus_of_isSplit (A := closedSubgroupAlgebraicGroup (G := twistAffineGroup p r A) T')
    (twistPreservesSplitTorus p r T.group hs)
  apply geometricMaximal_of_maximal (twistAffineGroup p r A) T'
  refine ⟨ht', ?_⟩
  intro C hC hTC
  obtain ⟨D, e, he⟩ := twistSubgroup_preimage p r C
  let D' := twistSubgroup p r D
  have hSame := same_of_inclusion_iso (B := D') (C := C) e he
  have hD : IsTorus D.group := by
    have ⟨n, ⟨j⟩⟩ := split_of_torus (D := closedSubgroupAlgebraicGroup C)
      ((isTorus_iff_coordinates _).mp hC)
    let S := (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin n))).val
    have ⟨i⟩ := CharacterDescent.standardSplitTorus (k := k) n
    let eS : (F₁).obj S ≅ S :=
      (F₁).mapIso i.symm ≪≫ splitGroupTwistIso p r (Specs.CharacterDescent.StandardLattice.{u} n) ≪≫ i
    exact isTorus_of_isSplit (A := closedSubgroupAlgebraicGroup D)
      ⟨n, ⟨(Functor.FullyFaithful.ofFullyFaithful F₁).preimageIso (e ≪≫ j ≪≫ eS.symm)⟩⟩
  have hTD := (twistSubgroupOf p r).mp (subgroupOf_transitive hTC hSame.2)
  exact subgroupOf_transitive hSame.2 ((twistSubgroupOf p r).mpr (hT.2 D hD hTD))

private theorem twistUnipotent (A : AffineAlgebraicGroup k) :
    IsUnipotent (twistAffineGroup p r A) ↔ IsUnipotent A := by
  letI := (iterateFrobenius k p r).toAlgebra
  let e := (Functor.mapGrpNatIso (twistBaseChangeIso p r)).app A.val
  let B := baseChangedAlgebraicGroup k A
  have h : IsUnipotent B ↔ IsUnipotent A := Unipotent.unipotenceFieldExtension A
  exact ⟨fun hA => h.mp (unipotent_iso e hA), fun hA => unipotent_iso e.symm (h.mpr hA)⟩

private theorem twistNormal {G : GroupScheme k} (N : ClosedSubgroup G) :
    IsNormalSubgroup ((F₁).map N.inclusion) ↔ IsNormalSubgroup N.inclusion := by
  letI := (iterateFrobenius k p r).toAlgebra
  let e := Functor.mapGrpNatIso (twistBaseChangeIso (k := k) p r)
  have h := e.hom.naturality N.inclusion
  have hi : (groupBaseChange k k).map N.inclusion ≫ (e.app G).inv =
      (e.app N.group).inv ≫ (F₁).map N.inclusion := e.inv.naturality N.inclusion
  have hn := baseChangeNormalSubgroupIff k k N.inclusion N.isClosedImmersion
  exact ⟨fun hN => hn.mp (normalSubgroup_of_iso (e.app G).symm (e.app N.group).symm hi hN),
    fun hN => normalSubgroup_of_iso (e.app G) (e.app N.group) h (hn.mpr hN)⟩

private theorem twistSmoothConnectedNormal {A : AffineAlgebraicGroup k}
    (N : ClosedSubgroup A.val) :
    IsSmoothConnectedNormal (G := twistAffineGroup p r A) (twistSubgroup p r N) ↔
      IsSmoothConnectedNormal N :=
  and_congr (twistSmooth p r N.group.X) (and_congr Iff.rfl (twistNormal p r N))

omit [IsAlgClosed k] in
private theorem smoothConnectedNormal_of_square {A : AffineAlgebraicGroup k}
    {B N : ClosedSubgroup A.val} (e : B.group ≅ N.group)
    (he : e.hom ≫ N.inclusion = B.inclusion) (h : IsSmoothConnectedNormal N) :
    IsSmoothConnectedNormal B := by
  let i := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e
  letI : IsIso e.hom.hom.hom.left := i.isIso_hom
  have hs : Smooth B.group.X.hom := by
    haveI := h.1
    rw [← Over.w e.hom.hom.hom]
    exact smooth_comp _ _
  refine ⟨hs, i.hom.homeomorph.connectedSpace_iff.mpr h.2.1, ?_⟩
  apply normalSubgroup_of_iso (Iso.refl _) e _ h.2.2
  simpa only [Iso.refl_hom, Category.comp_id] using he.symm

private theorem trivialGroup_image_iff {C D : Type*} [Category C] [Category D]
    (E : C ⥤ D) [E.IsEquivalence] {X T : C} {U : D}
    (hT : IsTerminal T) (hU : IsTerminal U) :
    Nonempty (E.obj X ≅ U) ↔ Nonempty (X ≅ T) := by
  let i := (IsTerminal.isTerminalObj E T hT).uniqueUpToIso hU
  exact ⟨fun ⟨e⟩ => ⟨(Functor.FullyFaithful.ofFullyFaithful E).preimageIso (e ≪≫ i.symm)⟩,
    fun ⟨e⟩ => ⟨E.mapIso e ≪≫ i⟩⟩

private theorem twistTrivialGroup (H : GroupScheme k) :
    Nonempty ((F₁).obj H ≅ Grp.trivial (SchemeOver k)) ↔
      Nonempty (H ≅ Grp.trivial (SchemeOver k)) :=
  trivialGroup_image_iff F₁ (Grp.isZero_trivial _).isTerminal (Grp.isZero_trivial _).isTerminal

private theorem twistRadical {A : AffineAlgebraicGroup k} (N : ClosedSubgroup A.val)
    (hN : IsUnipotentRadical A N) :
    IsUnipotentRadical (twistAffineGroup p r A) (twistSubgroup p r N) := by
  refine ⟨(twistSmoothConnectedNormal p r N).mpr hN.1,
    (twistUnipotent p r (closedSubgroupAlgebraicGroup N)).mpr hN.2.1, ?_⟩
  intro C hC hCu
  obtain ⟨D, e, he⟩ := twistSubgroup_preimage p r C
  let D' := twistSubgroup p r D
  have hSame := same_of_inclusion_iso (B := D') (C := C) e he
  have hd := (twistSmoothConnectedNormal p r D).mp (smoothConnectedNormal_of_square e he hC)
  have hdu := (twistUnipotent p r (closedSubgroupAlgebraicGroup D)).mp
    (unipotent_iso (F := closedSubgroupAlgebraicGroup C)
      (H := closedSubgroupAlgebraicGroup (G := twistAffineGroup p r A) D') e.symm hCu)
  exact subgroupOf_transitive hSame.2 ((twistSubgroupOf p r).mpr (hN.2.2 D hd hdu))

private theorem geometricTrivialRadical_iff (A : AffineAlgebraicGroup k) :
    IsTrivialSubgroup (geometricUnipotentRadical A) ↔
      ∀ N : ClosedSubgroup A.val, IsSmoothConnectedNormal N →
        IsUnipotent (closedSubgroupAlgebraicGroup N) → IsTrivialSubgroup N := by
  let K := AlgebraicClosure k
  let E := groupBaseChange k K
  letI : IsIso (fieldSpecMap k K) := fieldSpecMap_isIso
  letI : E.IsEquivalence := groupBaseChange_isEquivalence
  have simpTrivial (H : GroupScheme k) :
      Nonempty (E.obj H ≅ Grp.trivial (SchemeOver K)) ↔
        Nonempty (H ≅ Grp.trivial (SchemeOver k)) :=
    trivialGroup_image_iff E (Grp.isZero_trivial _).isTerminal (Grp.isZero_trivial _).isTerminal
  have smoothConnectedNormal (N : ClosedSubgroup A.val) :
      IsSmoothConnectedNormal (G := GeometricGroup A) (extendSubgroup K N) ↔
        IsSmoothConnectedNormal N :=
    and_congr (smooth_extend_iff K N.group.X) (and_congr (connected_extend_iso_iff K N.group.X)
      (baseChangeNormalSubgroupIff k K N.inclusion N.isClosedImmersion))
  let R := geometricUnipotentRadical A
  have hR := GeometricRadicals.geometricUnipotentRadicalLargest A
  constructor
  · intro h N hn hu
    have hle := hR.2.2 (extendSubgroup K N) ((smoothConnectedNormal N).mpr hn)
      ((Unipotent.unipotenceFieldExtension (K := K) (closedSubgroupAlgebraicGroup N)).mpr hu)
    exact (simpTrivial N.group).mp (trivial_of_subgroup_of_trivial hle h)
  · intro h
    obtain ⟨N, e, he⟩ := pullback_subgroup_over_closed_field A R
    let N' := extendSubgroup K N
    have hn := (smoothConnectedNormal N).mp (smoothConnectedNormal_of_square e he hR.1)
    have hnu := (Unipotent.unipotenceFieldExtension (K := K) (closedSubgroupAlgebraicGroup N)).mp
      (unipotent_iso (F := closedSubgroupAlgebraicGroup R) (H := closedSubgroupAlgebraicGroup (G := GeometricGroup A) N')
        e.symm hR.2.1)
    obtain ⟨i⟩ := (simpTrivial N.group).mpr (h N hn hnu)
    exact ⟨e.symm ≪≫ i⟩

private theorem twistReductive (A : AffineAlgebraicGroup k) (h : IsReductive A) :
    IsReductive (twistAffineGroup p r A) := by
  refine ⟨(twistSmooth p r A.val.X).mpr h.1,
    (twistGeometricallyConnected p r A.val.X).mpr h.2.1,
    (geometricTrivialRadical_iff (twistAffineGroup p r A)).mpr ?_⟩
  intro C hC hCu
  obtain ⟨D, e, he⟩ := twistSubgroup_preimage p r C
  let D' := twistSubgroup p r D
  have hd := (twistSmoothConnectedNormal p r D).mp (smoothConnectedNormal_of_square e he hC)
  have hdu := (twistUnipotent p r (closedSubgroupAlgebraicGroup D)).mp
    (unipotent_iso (F := closedSubgroupAlgebraicGroup C)
      (H := closedSubgroupAlgebraicGroup (G := twistAffineGroup p r A) D') e.symm hCu)
  obtain ⟨i⟩ := (twistTrivialGroup p r D.group).mpr
    ((geometricTrivialRadical_iff A).mp h.2.2 D hd hdu)
  exact ⟨e.symm ≪≫ i⟩


open Specs.FlagLineBundle (BorelProjection)
open Specs.FlagRelativeFrobeniusAtlas (TwistedPairProperties MarkedFlagTwist)

/-- Scalar transport takes the pullback defining a scheme kernel to the
pullback of the transported unit. -/
private theorem twistSchemeKernel {G H : GroupScheme k} {f : G ⟶ H} {N : ClosedSubgroup G}
    (h : Specs.IsSchemeKernel f N) :
    Specs.IsSchemeKernel ((F₁).map f) (twistSubgroup p r N) := by
  let e := asIso (Functor.LaxMonoidal.ε W₁)
  refine ((W₁).map_isPullback h).of_iso' (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · rw [Iso.refl_hom, Category.id_comp]
    exact (Functor.Monoidal.toUnit_ε (F := W₁) N.group.X).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · rw [Iso.refl_hom, Category.comp_id]
    rfl

/-- The given torus and Borels make a split opposite pair on the actual
scalar twist of the group. -/
theorem twistPairProperties {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G) :
    TwistedPairProperties p r P where
  reductive := twistReductive p r G P.reductive
  split := twistPreservesSplitTorus p r P.torus.group P.split
  maximal := twistGeometricallyMaximal p r P.torus P.split P.maximal
  positiveBorel := twistBorel p r P.positive P.positiveBorel
  negativeBorel := twistBorel p r P.negative P.negativeBorel
  inPositive := (twistSubgroupOf p r).mpr P.inPositive
  inNegative := (twistSubgroupOf p r).mpr P.inNegative
  opposite := twistOpposite p r P.opposite

/-- On the twisted pair the Borel projection is the scalar transport of
the specified retraction, with the transported unipotent radical as kernel. -/
def twistBorelProjection {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (b : BorelProjection P) : BorelProjection ((twistPairProperties p r P).pair p r) where
  inclusion := (F₁).map b.inclusion
  inclusion_comp := ((F₁).map_comp _ _).symm.trans ((F₁).congr_map b.inclusion_comp)
  projection := (F₁).map b.projection
  section_projection := by
    change (F₁).map b.inclusion ≫ (F₁).map b.projection = 𝟙 ((F₁).obj P.torus.group)
    rw [← (F₁).map_comp, b.section_projection, (F₁).map_id]
  radical := twistSubgroup p r b.radical
  isRadical := by
    let B := closedSubgroupAlgebraicGroup P.negative
    change IsUnipotentRadical (twistAffineGroup p r B) (twistSubgroup p r b.radical)
    exact twistRadical p r (A := B) b.radical b.isRadical
  isKernel := twistSchemeKernel p r b.isKernel

/-- The quotient comparison equips the actual Frobenius target with the
transported split marking and the map of projected Borel characters. -/
theorem markedFlagTwist : Specs.FlagRelativeFrobeniusAtlas.HasMarkedFlagTwist.{u} := by
  intro k _ p r _ _ _ G P Q b
  let c := twistPairProperties p r P
  let b' := twistBorelProjection p r b
  obtain ⟨Q', e, hQ, _, _⟩ := twistedFlagPresentation (k := k) p r Q
  let f := relativeGroupFrobenius (k := k) p r
  let g := relativeFrobenius (k := k) p r
  have hGroup (H : GroupScheme k) : IsRelativeFrobenius p r H.X (f.app H).hom.hom := by
    rw [relativeGroupFrobenius_hom]
    exact relativeFrobenius_formula p r H.X
  refine ⟨{
    properties := c
    borel := b'
    inclusion_eq := rfl
    projection_eq := rfl
    radical_eq := rfl
    quotient := Q'
    comparison := e
    quotient_eq := hQ
    groupFrobenius := f.app G.val
    borelFrobenius := f.app P.negative.group
    torusFrobenius := f.app P.torus.group
    flagFrobenius := g.app Q.scheme ≫ e.inv
    group_formula := hGroup _
    borel_formula := hGroup _
    torus_formula := hGroup _
    flag_formula := ?_
    inclusion_square := f.naturality P.negative.inclusion
    torus_inclusion_square := ?_
    projection_square := ?_
    quotient_square := ?_
    multiplicativeComparison := splitGroupTwistIso p r IntegerCharacters
    multiplicativeCoordinate := gmTwist_inv_fixes_monomial p r
    characters := twistCharacterEquiv p r P.torus.group
    characters_eq := fun _ => rfl
    roots := twistRootEquiv p r P.torus
    root_character := fun _ => rfl
    positive_roots := twistRoot_mem_subgroupRoots p r P.torus P.positive
    negative_roots := twistRoot_mem_subgroupRoots p r P.torus P.negative
    character_pullback := ?_ }⟩
  · rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    exact relativeFrobenius_formula p r Q.scheme
  · change b.inclusion ≫ f.app P.negative.group =
      f.app P.torus.group ≫ (twistGroup p r).map b.inclusion
    exact f.naturality b.inclusion
  · change b.projection ≫ f.app P.torus.group =
      f.app P.negative.group ≫ (twistGroup p r).map b.projection
    exact f.naturality b.projection
  · apply (cancel_mono e.hom).mp
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id, hQ]
    exact g.naturality Q.projection
  · intro χ
    change f.app P.negative.group ≫ ((twistGroup p r).map b.projection ≫
      twistCharacter p r χ) = (b.projection ≫ χ) ^ (p ^ r)
    have hχ : (twistGroup p r).map b.projection ≫ twistCharacter p r χ =
        twistCharacter p r (b.projection ≫ χ) := by
      simp only [twistCharacter, Functor.map_comp, Category.assoc]
    rw [hχ]
    exact relativeFrobenius_character p r _

end SplitMarking

end Groups


section FlagCharts

open Specs.FlagRelativeFrobeniusAtlas
  (affineChart RootCellCoordinates translatedLift translatedChart powerMap powerMorphism chartGerm)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.QuotientEmbedding (Presentation)
open Specs.BruhatOrbitParametrization (conjugatePoint)
open Specs.OrderedRootProducts (Enumerates rootProduct)
open Specs.BorelsAndChambers (subgroupRoots)
open TopologicalSpace.IrreducibleCloseds
open private rootProductAffineIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatCells
open private radicalIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
open private existsEnumeration from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private sectionProduct sectionProduct_open sectionProduct_translate_open
  sectionProduct_radical_open polynomialChart from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle

private theorem dimension_of_open_cover {A X : Scheme.{u}} {I : Type*} [Nonempty I]
    (j : I → (A ⟶ X)) (hj : ∀ i, IsOpenImmersion (j i))
    (hcover : ∀ x, ∃ i, x ∈ Set.range (j i)) :
    topologicalKrullDim X = topologicalKrullDim A := by
  apply le_antisymm
  · unfold topologicalKrullDim
    rw [Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro Z
    obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
    obtain ⟨i, z, rfl⟩ := hcover x
    letI := hj i
    let hi := (j i).isOpenEmbedding
    let e := orderIsoOfIsOpenEmbedding (j i) hi
    let V := e.symm ⟨Z, z, hx⟩
    have he : map (j i) hi.continuous V = Z :=
      congrArg Subtype.val (e.apply_symm_apply ⟨Z, z, hx⟩)
    rw [← he, hi.coheight_map, Order.krullDim_eq_iSup_coheight]
    exact le_iSup (fun W : IrreducibleCloseds A => (Order.coheight W : WithBot ℕ∞)) V
  · let i := Classical.choice (inferInstance : Nonempty I)
    letI := hj i
    exact (j i).isOpenEmbedding.isInducing.topologicalKrullDim_le

private theorem affineChart_dimension (k : Type u) [Field k] (n : ℕ) :
    topologicalKrullDim (affineChart k n).left = n := by
  change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) = n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- All translates use a single ordered positive-root product, with its
scheme-theoretic lift to the group. -/
theorem flagCellCover : Specs.FlagRelativeFrobeniusAtlas.HasCellCover.{u} := by
  intro k _ G P Q
  classical
  obtain ⟨hComm, D, I, U, Bneg, Rpos, Rneg, c, b, hBneg, hTneg, hOpp,
    hRpos, hRneg, _, _, _, hReps, _, hCells⟩ :=
    Flag.BruhatCells.bruhatCells G P.reductive P.torus P.negative P.split P.maximal
      P.negativeBorel P.inNegative
  letI := hComm
  obtain ⟨_, _, _, _, _, _, hBorel⟩ :=
    RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  obtain ⟨R, j, _, hR, _, hj, _, _, hIso, _⟩ :=
    hBorel P.negative P.negativeBorel P.inNegative
  obtain ⟨hOpen, _, _⟩ := Flag.OpenCell.openCell G P.reductive P.torus P.split P.maximal
    P.negative Bneg P.negativeBorel hBneg P.inNegative hTneg hOpp Rneg R hRneg hR
  let s := (Rneg.inclusion ≫ Bneg.inclusion).hom.hom
  have hs : IsOpenImmersion (sectionProduct (H := P.negative) s).left :=
    sectionProduct_radical_open hj hIso hOpen
  letI := D.finiteRoots
  obtain ⟨l, hl⟩ := existsEnumeration (subgroupRoots P.torus Bneg)
  have hroots : subgroupRoots P.torus Bneg = subgroupRoots P.torus P.positive := by
    rw [hOpp, show subgroupRoots P.torus P.negative = _ from P.opposite, compl_compl]
  have hl' : Enumerates l (subgroupRoots P.torus P.positive) := hroots ▸ hl
  obtain ⟨Rb, _, _, hRb, _, _, _, _, _, hParam⟩ := hBorel Bneg hBneg hTneg
  obtain ⟨rad, hrad⟩ := radicalIso hRb hRneg
  obtain ⟨par, hpar⟩ := hParam U l hl
  let coords := polynomialChart k l.length ≪≫ (rootProductAffineIso U l).symm
  let C : RootCellCoordinates (P := P) := ⟨U, l, hl', coords⟩
  let a := coords ≪≫ par ≪≫ (Grp.forget _).mapIso rad
  have ha : a.hom ≫ s = coords.hom ≫ rootProduct U l := by
    change (coords.hom ≫ par.hom ≫ rad.hom.hom.hom) ≫
      (Rneg.inclusion.hom.hom ≫ Bneg.inclusion.hom.hom) = _
    have hr := congrArg (Grp.forget (SchemeOver k)).map hrad
    change rad.hom.hom.hom ≫ Rneg.inclusion.hom.hom = Rb.inclusion.hom.hom at hr
    simp only [Category.assoc]
    rw [← Category.assoc rad.hom.hom.hom, hr, hpar]
  have hchart (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
      translatedChart Q C g = a.hom ≫ (((toUnit _ ≫ g) * s) ≫ Q.projection) := by
    change ((toUnit _ ≫ g) * (coords.hom ≫ rootProduct U l)) ≫ Q.projection = _
    rw [← ha, ← Category.assoc, MonObj.comp_mul]
    have hunit : a.hom ≫ toUnit Rneg.group.X = toUnit (affineChart k l.length) :=
      toUnit_unique _ _
    have hg : a.hom ≫ toUnit Rneg.group.X ≫ g = toUnit (affineChart k l.length) ≫ g :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) hunit)
    exact congrArg (fun z => (z * (a.hom ≫ s)) ≫ Q.projection) hg.symm
  have opn (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
      IsOpenImmersion ((((toUnit _ ≫ g) * s) ≫ Q.projection)).left :=
    sectionProduct_open Q _ (sectionProduct_translate_open s g hs)
  have hopen (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
      IsOpenImmersion (translatedChart Q C g).left := by
    rw [hchart, Over.comp_left]
    letI := opn g
    infer_instance
  have hcover (y : Q.scheme.left) : ∃ g, y ∈ Set.range (translatedChart Q C g).left := by
    choose n hn using hReps
    obtain ⟨_, _, cover⟩ := hCells Q
    obtain ⟨A, cells, hFactor, _, _, hCover⟩ := cover n hn
    have hy : y ∈ ⋃ w, Set.range (cells w).orbitInclusion.left := by simp [hCover]
    obtain ⟨w, x, hx⟩ := Set.mem_iUnion.mp hy
    let g := n w ≫ I.normalizer.inclusion.hom.hom
    let t := (toUnit Rneg.group.X ≫ g) * s
    have hin : (A w).inclusion.hom.hom ∈ Specs.SubgroupSections (A w) (A w).group.X := by
      change ∃ f : (A w).group.X ⟶ (A w).group.X, f ≫ (A w).inclusion.hom.hom = _
      exact ⟨𝟙 _, Category.id_comp _⟩
    have hconj := (((hFactor w).1 (A w).group.X (A w).inclusion.hom.hom).mp hin).2
    change ∃ d : (A w).group.X ⟶ Rneg.group.X,
      d ≫ s = conjugatePoint g⁻¹ (A w).inclusion.hom.hom at hconj
    obtain ⟨d, hd⟩ := hconj
    have hdt : d ≫ t = (A w).inclusion.hom.hom * (toUnit (A w).group.X ≫ g) := by
      rw [show t = (toUnit Rneg.group.X ≫ g) * s from rfl, MonObj.comp_mul, comp_toUnit_assoc, hd]
      simp only [conjugatePoint, GrpObj.comp_inv, inv_inv]
      group
    have horb : d ≫ t ≫ Q.projection = (cells w).orbitIso.hom ≫ (cells w).orbitInclusion := by
      rw [← Category.assoc d, hdt, (cells w).orbitIso_eq]
    let f := (Over.forget _).mapIso a
    let wIso := (Over.forget _).mapIso (cells w).orbitIso
    refine ⟨g, f.inv (d.left (wIso.inv x)), ?_⟩
    have eq := congrArg (fun m : (A w).group.X ⟶ Q.scheme => m.left (wIso.inv x)) horb
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at eq
    have hf (z : Rneg.group.X.left) : f.hom (f.inv z) = z :=
      (Scheme.homeoOfIso f).apply_symm_apply z
    have hw : (cells w).orbitIso.hom.left (wIso.inv x) = x :=
      (Scheme.homeoOfIso wIso).apply_symm_apply x
    rw [hchart, Over.comp_left, Scheme.Hom.comp_apply]
    change (t ≫ Q.projection).left (f.hom (f.inv _)) = _
    calc
      _ = (t ≫ Q.projection).left (d.left (wIso.inv x)) := congrArg _ (hf _)
      _ = _ := eq.trans ((congrArg (cells w).orbitInclusion.left hw).trans hx)
  refine ⟨C, hopen, hcover, ?_, ?_⟩
  · change l.length = _
    have hSet : (↑l.toFinset : Set (Specs.AbstractPairing.Root P.torus)) =
        subgroupRoots P.torus P.positive := by
      ext α
      simpa only [Finset.mem_coe, List.mem_toFinset] using hl'.2 α
    rw [← hSet, Set.ncard_coe_finset, List.toFinset_card_of_nodup hl'.1]
  · rw [dimension_of_open_cover (fun g => (translatedChart Q C g).left) hopen hcover]
    exact affineChart_dimension k _


/-- Over the unchanged chart field, the relative map fixes scalars. -/
theorem powerMapFormula : Specs.FlagRelativeFrobeniusAtlas.PowerMapFormula.{u} := by
  intro k _ q n
  exact ⟨MvPolynomial.expand_C q, MvPolynomial.expand_X q⟩

theorem powerMapStalkFormula : Specs.FlagRelativeFrobeniusAtlas.PowerMapStalkFormula.{u} := by
  intro k _ q n x
  let R := CommRingCat.of (MvPolynomial (Fin n) k)
  let m : R ⟶ R := CommRingCat.ofHom (powerMap q n).toRingHom
  let f := (powerMorphism (k := k) q n).left
  have hg : chartGerm (f x) ≫ f.stalkMap x = m ≫ chartGerm x := by
    rw [chartGerm, chartGerm, Category.assoc, Scheme.Hom.germ_stalkMap]
    rw [← Category.assoc]
    let g := (Spec R).presheaf.germ ⊤ x (by simp)
    change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map m).appTop) ≫ g =
      m ≫ ((Scheme.ΓSpecIso R).inv ≫ g)
    exact (congrArg (· ≫ g) (Scheme.ΓSpecIso_inv_naturality m).symm).trans
      (Category.assoc _ _ _)
  have h (z : R) : f.stalkMap x (chartGerm (f x) z) = chartGerm x (powerMap q n z) :=
    ConcreteCategory.congr_hom hg z
  refine ⟨fun c => (h (MvPolynomial.C c)).trans (congrArg (chartGerm x) (MvPolynomial.expand_C q c)), ?_⟩
  intro i
  exact (h (MvPolynomial.X i)).trans
    ((congrArg (chartGerm x) (MvPolynomial.expand_X q i)).trans (map_pow (chartGerm x).hom _ q))

/-- The affine coordinates descend to the prime field, so their twist
has the same polynomial coordinates over the new scalar field. -/
def affineTwistIso (n : ℕ) : affineChart k n ≅ (twist p r).obj (affineChart k n) := by
  let e := MvPolynomial.mapEquiv (Fin n) (iterateFrobeniusEquiv k p r)
  refine Over.isoMk (Scheme.Spec.mapIso e.toCommRingCatIso.op) ?_
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)) ≫
        inverseBaseFrobenius p r) = Spec.map (CommRingCat.ofHom MvPolynomial.C)
  rw [← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change MvPolynomial.map (iterateFrobenius k p r)
    (MvPolynomial.C ((iterateFrobeniusEquiv k p r).symm c)) = MvPolynomial.C c
  rw [MvPolynomial.map_C]
  exact congrArg MvPolynomial.C ((iterateFrobeniusEquiv k p r).apply_symm_apply c)

theorem affineRelativeFrobenius (n : ℕ) :
    (relativeFrobenius p r).app (affineChart k n) =
      powerMorphism (p ^ r) n ≫ (affineTwistIso p r n).hom := by
  let σ := iterateFrobeniusEquiv k p r
  let R := CommRingCat.of (MvPolynomial (Fin n) k)
  let t : Spec R ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom MvPolynomial.C)
  apply Over.OverMorphism.ext
  change absoluteFrobenius p r (Over.mk t) =
    Spec.map (CommRingCat.ofHom (powerMap (k := k) (p ^ r) n).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.map σ.toRingHom))
  rw [absoluteFrobenius_spec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change MvPolynomial.C c ^ (p ^ r) =
      powerMap (k := k) (p ^ r) n (MvPolynomial.map σ.toRingHom (MvPolynomial.C c))
    rw [MvPolynomial.map_C, (powerMapFormula (k := k) (p ^ r) n).1, ← map_pow]
    rfl
  · intro j
    change MvPolynomial.X j ^ (p ^ r) =
      powerMap (k := k) (p ^ r) n (MvPolynomial.map σ.toRingHom (MvPolynomial.X j))
    rw [MvPolynomial.map_X, (powerMapFormula (k := k) (p ^ r) n).2]

private theorem twist_chart_range {X Y : SchemeOver k} (j : X ⟶ Y)
    {A : SchemeOver k} (e : A ≅ (twist p r).obj X) :
    Set.range (e.hom ≫ (twist p r).map j).left = Set.range j.left := by
  change Set.range (j.left ∘ e.hom.left) = Set.range j.left
  exact ((Over.forget _).mapIso e).hom.homeomorph.surjective.range_comp j.left

private theorem twist_chart_open {X Y A : SchemeOver k} (j : X ⟶ Y)
    (e : A ≅ (twist p r).obj X) (hj : IsOpenImmersion j.left) :
    IsOpenImmersion (e.hom ≫ (twist p r).map j).left := by
  letI : IsOpenImmersion ((twist p r).map j).left := hj
  letI : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  exact IsOpenImmersion.comp e.hom.left ((twist p r).map j).left

private theorem relativeFrobenius_openPullback {X Y : SchemeOver k} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.left) :
    IsPullback ((relativeFrobenius p r).app X).left j.left
      ((twist p r).map j).left ((relativeFrobenius p r).app Y).left := by
  letI := hj
  letI : IsOpenImmersion ((twist p r).map j).left := hj
  apply IsOpenImmersion.isPullback
  · exact congrArg Over.Hom.left ((relativeFrobenius p r).naturality j)
  · ext y
    exact Iff.rfl

private theorem affineCellPullback {Y : SchemeOver k} {n : ℕ} (j : affineChart k n ⟶ Y)
    (hj : IsOpenImmersion j.left) :
    IsPullback (powerMorphism (p ^ r) n).left j.left
      ((affineTwistIso p r n).hom ≫ (twist p r).map j).left
      ((relativeFrobenius p r).app Y).left := by
  let e := (Over.forget _).mapIso (affineTwistIso (k := k) p r n)
  have hf : ((relativeFrobenius p r).app (affineChart k n)).left =
      (powerMorphism (p ^ r) n).left ≫ e.hom :=
    congrArg Over.Hom.left (affineRelativeFrobenius p r n)
  exact (relativeFrobenius_openPullback p r j hj).of_iso' (Iso.refl _) e
    (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans hf)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    (Category.comp_id _).symm
    ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem flagFrobeniusCellCover : Specs.FlagRelativeFrobeniusAtlas.HasFrobeniusCellCover.{u} := by
  intro k _ p r _ _ _ G P Q _
  obtain ⟨C, hopen, hcover, hn, hdim⟩ := flagCellCover Q
  let e := affineTwistIso (k := k) p r C.order.length
  refine ⟨(relativeFrobenius p r).app Q.scheme, C, e,
    relativeFrobenius_formula p r Q.scheme, hn, hdim, ?_, ?_⟩
  · intro g
    let j := translatedChart Q C g
    refine ⟨hopen g, twist_chart_open p r j e (hopen g), ?_, affineCellPullback p r j (hopen g)⟩
    rw [Category.assoc, ← (twist p r).map_comp]
    rfl
  · intro y
    obtain ⟨g, hg⟩ := hcover y
    exact ⟨g, (twist_chart_range p r (translatedChart Q C g) e).symm ▸ hg⟩

theorem uniqueClosedFiberPoint : Specs.FlagRelativeFrobeniusAtlas.UniqueClosedFiberPoint.{u} := by
  intro k _ p r _ _ _ G P Q F hF y
  haveI : Smooth Q.scheme.hom := ((FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q).1
  let q := AlgebraicGeometry.pointOfClosedPoint Q.scheme.hom y.val y.prop
  let x : 𝟙_ (SchemeOver k) ⟶ Q.scheme :=
    Over.homMk q (pointOfClosedPoint_comp _ _ _)
  refine ⟨x, ?_, ?_⟩
  · exact (hF.1 _).trans (pointOfClosedPoint_apply _ _ _ _)
  · intro z hz
    apply Over.OverMorphism.ext
    apply AlgebraicGeometry.ext_of_apply_closedPoint_eq Q.scheme.hom (Over.w z) (Over.w x)
    rw [hF.1] at hz
    exact hz.trans (pointOfClosedPoint_apply _ _ _ _).symm

end FlagCharts

end
end LinearAlgebraicGroups.FlagRelativeFrobeniusAtlas
