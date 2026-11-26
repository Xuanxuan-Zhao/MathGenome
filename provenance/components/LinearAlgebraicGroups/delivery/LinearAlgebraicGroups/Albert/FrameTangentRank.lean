import Specs.LinearAlgebraicGroups.Albert.FrameTangentRank
import LinearAlgebraicGroups.Albert.Triality
import LinearAlgebraicGroups.Albert.AutomorphismScheme
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Localization.BaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.MonObj DualNumber

universe u

namespace LinearAlgebraicGroups.Albert.FrameTangent

open _root_.Specs.LinearAlgebraicGroups.Albert
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open _root_.LinearAlgebraicGroups.Composition (Zorn)
open Composition.Zorn (norm)
open SplitSpinSpecification (integralForm hyperbolicBasis)
open TrialitySpecification (Model modelOp modelBaseChange mapModel FixesFrame)
open FrameSpecification (frameAxis)
open CubicSpecification (cubicUnit)
open FrameTangentSpecification (FrameRepresentation FrameTangentRank)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- The submodule of all quadratic derivations killing the three ordered frame axes. -/
def frameDerivations : FrameTangentSpecification.FrameDerivationsType.{u} :=
  fun J => FrameTangentSpecification.frameDerivations J


local instance (k : Type u) [Field k] :
    (algSpec (CommRingCat.of k)).Braided := AlgebraicGeometry.braidedAlgSpec

section Representation
open private integralZornIsometry scalarIsometry scalarIsometry_spin scalarIsometry_natural
  zornBasis spinRelatedEquiv spinRelated_naturality from LinearAlgebraicGroups.Albert.Triality

private abbrev spinForm := integralForm 4
private abbrev spinBasis := hyperbolicBasis ℤ 4
private abbrev integralCoordinates := SpinFunctor.CoordinateRing spinForm spinBasis

variable (k : Type u) [Field k]

/-- Coordinate algebra of the split spin scheme after extension from the integers. -/
private abbrev coordinates := k ⊗[ℤ] integralCoordinates

private abbrev coordinateObject : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (coordinates k))

private def spinPointsFunctor : ((CommAlgCat k)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{u} where
  obj S := GrpCat.of (SpinFunctor.Spin spinForm S.unop.unop spinBasis)
  map f := GrpCat.ofHom (SpinFunctor.map spinForm spinBasis (f.unop.unop.hom.restrictScalars ℤ))
  map_id S := by
    apply GrpCat.ext
    intro a
    exact SpinFunctor.map_id spinForm spinBasis a
  map_comp f g := by
    apply GrpCat.ext
    intro a
    exact SpinFunctor.map_comp spinForm spinBasis
      (f.unop.unop.hom.restrictScalars ℤ) (g.unop.unop.hom.restrictScalars ℤ) a

private def spinAlgebraPoints (S : CommAlgCat k) :
    (coordinates k →ₐ[k] S) ≃ SpinFunctor.Spin spinForm S spinBasis :=
  (Algebra.TensorProduct.liftEquivRight ℤ k integralCoordinates S).symm.trans
    (SpinFunctor.pointEquiv spinForm spinBasis S)

private theorem spinAlgebraPoints_natural {S T : CommAlgCat k} (f : S ⟶ T)
    (a : coordinates k →ₐ[k] S) :
    spinAlgebraPoints k T (f.hom.comp a) =
      SpinFunctor.map spinForm spinBasis (f.hom.restrictScalars ℤ) (spinAlgebraPoints k S a) := by
  exact SpinFunctor.pointEquiv_natural spinForm spinBasis (f.hom.restrictScalars ℤ)
    ((Algebra.TensorProduct.liftEquivRight ℤ k integralCoordinates S).symm a)

private def coordinateRepresentation :
    (spinPointsFunctor k ⋙ forget _).RepresentableBy (coordinateObject k) where
  homEquiv {S} :=
    { toFun := fun f => spinAlgebraPoints k S.unop f.unop.hom
      invFun := fun a => (CommAlgCat.ofHom ((spinAlgebraPoints k S.unop).symm a)).op
      left_inv := by intro f; simp
      right_inv := by intro a; exact (spinAlgebraPoints k S.unop).apply_symm_apply a }
  homEquiv_comp f g := spinAlgebraPoints_natural k f.unop g.unop.hom

local instance coordinateGroup : GrpObj (coordinateObject k) :=
  GrpObj.ofRepresentableBy _ _ (coordinateRepresentation k)

private def frameGroup : LinearAlgebraicGroups.Specs.GroupScheme k :=
  ((algSpec (CommRingCat.of k)).mapGrp).obj (Grp.mk (coordinateObject k))

private theorem frameGroup_affine : IsAffine (frameGroup k).X.left := by
  change IsAffine (Spec (CommRingCat.of (coordinates k)))
  infer_instance

private def representedSpinPoints (S : CommAlgCat k) :
    ((groupPointsFunctor k).obj (frameGroup k)).obj S ≃*
      SpinFunctor.Spin spinForm S spinBasis :=
  let F := algSpec (CommRingCat.of k)
  let i : (op S ⟶ coordinateObject k) ≃*
      ((groupPointsFunctor k).obj (frameGroup k)).obj S :=
    { (algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv with
      map_mul' := fun f g => F.map_mul f g }
  i.symm.trans ((yonedaGrpObjIsoOfRepresentableBy _ _ (coordinateRepresentation k)).app
    (op (op S))).groupIsoToMulEquiv

private theorem representedSpinPoints_onSpec {S : CommAlgCat k} (p : op S ⟶ coordinateObject k) :
    representedSpinPoints k S ((algSpec (CommRingCat.of k)).map p) =
      spinAlgebraPoints k S p.unop.hom := by
  let e := (algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv
    (X := op S) (Y := coordinateObject k)
  exact congrArg ((coordinateRepresentation k).homEquiv (X := op S)) (e.symm_apply_apply p)

private theorem representedSpinPoints_natural {S T : CommAlgCat k} (f : S ⟶ T)
    (p : ((groupPointsFunctor k).obj (frameGroup k)).obj S) :
    representedSpinPoints k T (((groupPointsFunctor k).obj (frameGroup k)).map f p) =
      SpinFunctor.map spinForm spinBasis (f.hom.restrictScalars ℤ) (representedSpinPoints k S p) := by
  let F := algSpec (CommRingCat.of k)
  obtain ⟨g, rfl⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv.surjective
    (show F.obj (op S) ⟶ F.obj (coordinateObject k) from p)
  change representedSpinPoints k T (F.map f.op ≫ F.map g) = _
  calc
    _ = representedSpinPoints k T (F.map (f.op ≫ g)) :=
      congrArg (representedSpinPoints k T) (F.map_comp f.op g).symm
    _ = spinAlgebraPoints k T (f.hom.comp g.unop.hom) := representedSpinPoints_onSpec k _
    _ = SpinFunctor.map spinForm spinBasis (f.hom.restrictScalars ℤ)
        (spinAlgebraPoints k S g.unop.hom) := spinAlgebraPoints_natural k f g.unop.hom
    _ = _ := congrArg _ (representedSpinPoints_onSpec k g).symm

private def octonionSpinEquiv (S : Type*) [CommRing S] [Algebra ℤ S] :
    SpinFunctor.Spin spinForm S spinBasis ≃*
      SpinFunctor.Spin (norm ℤ) S (zornBasis ℤ) := by
  let d := integralZornIsometry
  let m := Units.map (scalarIsometry S d).toMonoidHom
  let f := (m.comp (SpinFunctor.spinSubgroup spinForm S spinBasis).subtype).codRestrict
    (SpinFunctor.spinSubgroup (norm ℤ) S (zornBasis ℤ)) fun a =>
      scalarIsometry_spin S d a.property
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    apply Units.ext
    exact (scalarIsometry S d).injective (congrArg (fun t => Units.val t.val) h)
  · intro b
    let a := Units.map (scalarIsometry S d.symm).toMonoidHom b.val
    refine ⟨⟨a, scalarIsometry_spin S d.symm b.property⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact (scalarIsometry S d).apply_symm_apply b.val.val

private theorem octonionSpinEquiv_natural {S T : Type*}
    [CommRing S] [Algebra ℤ S] [CommRing T] [Algebra ℤ T]
    (f : S →ₐ[ℤ] T) (a : SpinFunctor.Spin spinForm S spinBasis) :
    octonionSpinEquiv T (SpinFunctor.map spinForm spinBasis f a) =
      SpinFunctor.map (norm ℤ) (zornBasis ℤ) f (octonionSpinEquiv S a) := by
  apply Subtype.ext
  apply Units.ext
  exact scalarIsometry_natural S integralZornIsometry f a.val.val

private def representedFramePoints (S : CommAlgCat k) :
    ((groupPointsFunctor k).obj (frameGroup k)).obj S ≃*
    TrialitySpecification.frameStabilizer (R := S) :=
  (representedSpinPoints k S).trans ((octonionSpinEquiv S).trans
    ((spinRelatedEquiv ℤ S).trans (Triality.frameTriality S).choose))

private def frameRepresentation : FrameRepresentation k where
  group := frameGroup k
  affine := frameGroup_affine k
  points := representedFramePoints k
  natural := by
    intro S T f p x
    let a := octonionSpinEquiv S (representedSpinPoints k S p)
    let b := octonionSpinEquiv T
      (representedSpinPoints k T (((groupPointsFunctor k).obj (frameGroup k)).map f p))
    have hb : b = SpinFunctor.map (norm ℤ) (zornBasis ℤ) (f.hom.restrictScalars ℤ) a :=
      (congrArg (octonionSpinEquiv T) (representedSpinPoints_natural k f p)).trans
        (octonionSpinEquiv_natural (f.hom.restrictScalars ℤ) _)
    change mapModel f.hom.toRingHom (((Triality.frameTriality S).choose (spinRelatedEquiv ℤ S a)).val x) =
      ((Triality.frameTriality T).choose (spinRelatedEquiv ℤ T b)).val (mapModel f.hom.toRingHom x)
    rw [hb, (Triality.frameTriality S).choose_spec, (Triality.frameTriality T).choose_spec]
    exact Prod.ext rfl (funext fun i =>
      spinRelated_naturality ℤ (f.hom.restrictScalars ℤ) a i (x.2 i))

end Representation

section Tangent

open TensorProduct LinearMap.GeneralLinearGroup
open private modelBaseChange_tmul modelBaseChange_operator mapModel_add
  from LinearAlgebraicGroups.Albert.IntrinsicCubic
open private ground_operator from LinearAlgebraicGroups.Albert.QuadraticOperators
open private map_octonion_smul map_octonion_zero from LinearAlgebraicGroups.Albert.Triality
open private infinitesimal_apply infinitesimalUnit infinitesimal_reduction infinitesimal_injective
  exists_infinitesimal infinitesimal_fixes infinitesimal_quadratic_iff infinitesimal_add
  scalar_eps_tmul scaled_epsilon tensorOne_ext
  from LinearAlgebraicGroups.Albert.AutomorphismScheme

variable {k : Type u} [Field k]

private theorem split_operator (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (S : Type u) [CommRing S] [Algebra k S] (x y : S ⊗[k] Model k) :
    TrialitySpecification.modelBaseChange k S (J.op S x y) =
      modelOp (TrialitySpecification.modelBaseChange k S x)
        (TrialitySpecification.modelBaseChange k S y) := by
  let J₀ := weightedHermitianJordan (LowerRankSpecification.untwisted k)
    (Composition.Zorn.isOctonion k)
  let K := SplitSpecification.ParaQuadratic.ofJordan J
  let K₀ := SplitSpecification.ParaQuadratic.ofJordan J₀
  have he : K.IsIso K₀ (LinearEquiv.refl k (Model k)) := by
    apply (K.isIso_iff_ground K₀ _).mpr
    exact ⟨hu, fun a b => (ho a b).trans (ground_operator _ _ a b).symm⟩
  have h := he.2 S x y
  rw [LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id] at h
  change J.op S x y = J₀.op S x y at h
  rw [h]
  exact modelBaseChange_operator x y

private theorem modelBaseChange_onPure (S : Type u) [CommRing S] [Algebra k S]
    (a : S) (x : Model k) :
    TrialitySpecification.modelBaseChange k S (a ⊗ₜ[k] x) =
      a • TrialitySpecification.mapModel (algebraMap k S) x :=
  modelBaseChange_tmul a x

private theorem baseChange_axis (S : Type u) [CommRing S] [Algebra k S] (i : Fin 3) :
    TrialitySpecification.modelBaseChange k S (1 ⊗ₜ[k] (frameAxis i : Model k)) = frameAxis i := by
  rw [modelBaseChange_onPure, one_smul]
  apply Prod.ext
  · funext j
    change algebraMap k S ((Pi.single i 1 : Fin 3 → k) j) = (Pi.single i 1 : Fin 3 → S) j
    by_cases h : j = i <;> simp [h]
  · funext j
    change Composition.ZornSpecification.mapCoordinates (algebraMap k S) (0 : Zorn k) = 0
    exact map_octonion_zero (algebraMap k S)

private theorem point_preservation (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (S : Type u) [CommRing S] [Algebra k S] (g : (Module.End S (S ⊗[k] Model k))ˣ) :
    FixesFrame (generalLinearEquiv S (Model S)
        (congrLinearEquiv (TrialitySpecification.modelBaseChange k S) g)) ↔
      PreservesQuadratic J S g.val ∧ ∀ i : Fin 3,
        g.val (1 ⊗ₜ[k] (frameAxis i : Model k)) = 1 ⊗ₜ[k] frameAxis i := by
  let B := TrialitySpecification.modelBaseChange k S
  let e := generalLinearEquiv S (Model S) (congrLinearEquiv B g)
  have he (x : S ⊗[k] Model k) : e (B x) = B (g.val x) := by
    change B (g.val (B.symm (B x))) = _
    rw [B.symm_apply_apply]
  have hf : (∀ i, e (frameAxis i) = frameAxis i) ↔
      ∀ i : Fin 3, g.val (1 ⊗ₜ[k] (frameAxis i : Model k)) = 1 ⊗ₜ[k] frameAxis i := by
    constructor <;> intro h i
    · apply B.injective
      rw [← he, baseChange_axis, h]
    · rw [← baseChange_axis (k := k) S i, he, h]
  have hop : (∀ x y, e (modelOp x y) = modelOp (e x) (e y)) ↔
      ∀ x y, g.val (J.op S x y) = J.op S (g.val x) (g.val y) := by
    constructor
    · intro h x y
      apply B.injective
      rw [← he, split_operator J hu ho, h, he, he, split_operator J hu ho]
    · intro h x y
      obtain ⟨a, rfl⟩ := B.surjective x
      obtain ⟨b, rfl⟩ := B.surjective y
      rw [← split_operator J hu ho S a b, he, h, he, he, split_operator J hu ho]
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [hf, hop]
  constructor
  · rintro ⟨hframe, h⟩
    refine ⟨⟨?_, h⟩, hframe⟩
    have hsum : (∑ i : Fin 3, (frameAxis i : Model k)) = (cubicUnit : Model k) :=
      (hermitian_frame (norm k) (LowerRankSpecification.untwisted k)).1
    rw [hu, ← hsum, tmul_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => hframe i
  · rintro ⟨⟨_, h⟩, hframe⟩
    exact ⟨hframe, h⟩

variable (G : FrameRepresentation k)

private def coordinateActionEquiv (S : CommAlgCat k) :
    (Module.End S (S ⊗[k] Model k))ˣ ≃* (Model S ≃ₗ[S] Model S) :=
  (congrLinearEquiv (TrialitySpecification.modelBaseChange k S)).trans (generalLinearEquiv S (Model S))

private def pointAction (S : CommAlgCat k) :
    ((groupPointsFunctor k).obj G.group).obj S →* (Module.End S (S ⊗[k] Model k))ˣ :=
  (coordinateActionEquiv S).symm.toMonoidHom.comp
    ((TrialitySpecification.frameStabilizer (R := S)).subtype.comp (G.points S).toMonoidHom)

private theorem pointAction_apply (S : CommAlgCat k)
    (p : ((groupPointsFunctor k).obj G.group).obj S) (x : S ⊗[k] Model k) :
    TrialitySpecification.modelBaseChange k S ((pointAction G S p).val x) =
      (G.points S p).val (TrialitySpecification.modelBaseChange k S x) := by
  let B := TrialitySpecification.modelBaseChange k S
  change B (B.symm ((G.points S p).val (B x))) = _
  exact B.apply_symm_apply _

private theorem pointAction_injective (S : CommAlgCat k) :
    Function.Injective (pointAction G S) :=
  (coordinateActionEquiv S).symm.injective.comp (Subtype.val_injective.comp (G.points S).injective)

private theorem pointAction_range (S : CommAlgCat k) (g : (Module.End S (S ⊗[k] Model k))ˣ) :
    (∃ p, pointAction G S p = g) ↔ FixesFrame (coordinateActionEquiv S g) := by
  constructor
  · rintro ⟨p, hp⟩
    have he := congrArg (coordinateActionEquiv S) hp
    change coordinateActionEquiv S ((coordinateActionEquiv S).symm (G.points S p).val) = _ at he
    rw [MulEquiv.apply_symm_apply] at he
    exact he ▸ (G.points S p).property
  · intro h
    let a : TrialitySpecification.frameStabilizer (R := S) := ⟨coordinateActionEquiv S g, h⟩
    refine ⟨(G.points S).symm a, ?_⟩
    change (coordinateActionEquiv S).symm (G.points S ((G.points S).symm a)).val = g
    rw [MulEquiv.apply_symm_apply]
    exact (coordinateActionEquiv S).symm_apply_apply g

private theorem modelBaseChange_natural {S T : CommAlgCat k} (f : S ⟶ T)
    (x : S ⊗[k] Model k) :
    TrialitySpecification.modelBaseChange k T (f.hom.toLinearMap.rTensor (Model k) x) =
      TrialitySpecification.mapModel f.hom.toRingHom (TrialitySpecification.modelBaseChange k S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    rw [LinearMap.rTensor_tmul]
    rw [modelBaseChange_onPure, modelBaseChange_onPure]
    apply Prod.ext <;> funext i
    · change f.hom s * algebraMap k T (x.1 i) = f.hom (s * algebraMap k S (x.1 i))
      rw [map_mul, f.hom.commutes]
    · change f.hom s • Composition.ZornSpecification.mapCoordinates (algebraMap k T) (x.2 i) =
        Composition.ZornSpecification.mapCoordinates f.hom.toRingHom
          (s • Composition.ZornSpecification.mapCoordinates (algebraMap k S) (x.2 i))
      rw [map_octonion_smul]
      apply congrArg (f.hom s • ·)
      apply (Composition.Zorn.coordinates T).injective
      let z := Composition.Zorn.coordinates k (x.2 i)
      change
        (algebraMap k T z.1, (fun j => algebraMap k T (z.2.1 j)),
          (fun j => algebraMap k T (z.2.2.1 j)), algebraMap k T z.2.2.2) =
        (f.hom (algebraMap k S z.1), (fun j => f.hom (algebraMap k S (z.2.1 j))),
          (fun j => f.hom (algebraMap k S (z.2.2.1 j))), f.hom (algebraMap k S z.2.2.2))
      exact Prod.ext (f.hom.commutes z.1).symm
        (Prod.ext (funext fun j => (f.hom.commutes (z.2.1 j)).symm)
          (Prod.ext (funext fun j => (f.hom.commutes (z.2.2.1 j)).symm)
            (f.hom.commutes z.2.2.2).symm))
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    exact (mapModel_add f.hom.toRingHom _ _).symm

private theorem pointAction_natural {S T : CommAlgCat k} (f : S ⟶ T)
    (p : ((groupPointsFunctor k).obj G.group).obj S) (x : S ⊗[k] Model k) :
    (pointAction G T (((groupPointsFunctor k).obj G.group).map f p)).val
        (f.hom.toLinearMap.rTensor (Model k) x) =
      f.hom.toLinearMap.rTensor (Model k) ((pointAction G S p).val x) := by
  apply (TrialitySpecification.modelBaseChange k T).injective
  rw [pointAction_apply, modelBaseChange_natural, modelBaseChange_natural, pointAction_apply]
  exact (G.natural f p _).symm

private abbrev dualAlgebra (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

private theorem pointAction_reduces (p : ((groupPointsFunctor k).obj G.group).obj (dualAlgebra k)) :
    reduceTangentPoints G.group p = 1 ↔
      ∀ x : Model k, dualModuleReduction ((pointAction G (dualAlgebra k) p).val (1 ⊗ₜ[k] x)) =
        1 ⊗ₜ[k] x := by
  let F := (groupPointsFunctor k).obj G.group
  let r := dualReduction k
  let K := CommAlgCat.of k k
  have h (x : Model k) : (pointAction G K (F.map r p)).val (1 ⊗ₜ[k] x) =
      dualModuleReduction ((pointAction G (dualAlgebra k) p).val (1 ⊗ₜ[k] x)) := by
    have hn := pointAction_natural G r p (1 ⊗ₜ[k] x)
    change (pointAction G K (F.map r p)).val
      ((TrivSqZeroExt.fstHom k k k 1) ⊗ₜ[k] x) =
        dualModuleReduction ((pointAction G (dualAlgebra k) p).val (1 ⊗ₜ[k] x)) at hn
    simpa only [map_one] using hn
  constructor
  · intro hp x
    change F.map r p = 1 at hp
    rw [← h, hp, map_one]
    rfl
  · intro hp
    apply pointAction_injective G K
    change pointAction G K (F.map r p) = pointAction G K 1
    rw [map_one]
    apply Units.ext
    exact tensorOne_ext fun x => (h x).trans (hp x)

private theorem pointAction_scale (p : LinearAlgebraicGroups.Specs.Lie k G.group)
    (c : k) (D : Module.End k (Model k))
    (hp : (pointAction G (dualAlgebra k) p.toMul.val).val = infinitesimal D) :
    (pointAction G (dualAlgebra k) (scalePointKernel G.group c p).toMul.val).val =
      infinitesimal (c • D) := by
  apply tensorOne_ext
  intro x
  let f := CommAlgCat.ofHom (dualNumberScale c)
  have h := pointAction_natural G f p.toMul.val (1 ⊗ₜ[k] x)
  change (pointAction G (dualAlgebra k) (scalePointKernel G.group c p).toMul.val).val
      ((dualNumberScale c 1) ⊗ₜ[k] x) =
      (dualNumberScale c).toLinearMap.rTensor (Model k)
        ((pointAction G (dualAlgebra k) p.toMul.val).val (1 ⊗ₜ[k] x)) at h
  rw [map_one, hp, infinitesimal_apply, LinearMap.baseChange_tmul, scalar_eps_tmul, map_add] at h
  rw [h, infinitesimal_apply, LinearMap.baseChange_tmul, scalar_eps_tmul]
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one, scaled_epsilon,
    TensorProduct.smul_tmul, LinearMap.smul_apply]

set_option maxHeartbeats 1000000 in
private theorem frameTangentEquiv (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y) :
    letI := G.affine
    ∃ e : frameDerivations J ≃ₗ[k] LinearAlgebraicGroups.Specs.Lie k G.group,
      ∀ D x, (G.points (dualAlgebra k) (e D).toMul.val).val
          (TrialitySpecification.modelBaseChange k (DualNumber k) x) =
        TrialitySpecification.modelBaseChange k (DualNumber k) (infinitesimal D.val x) := by
  letI := G.affine
  let A := pointAction G (dualAlgebra k)
  have hfix (D : Module.End k (Model k)) :
      FixesFrame (coordinateActionEquiv (dualAlgebra k) (infinitesimalUnit D)) ↔
        D ∈ frameDerivations J := by
    change FixesFrame (generalLinearEquiv (DualNumber k) (Model (DualNumber k))
      (congrLinearEquiv (TrialitySpecification.modelBaseChange k (DualNumber k))
        (infinitesimalUnit D))) ↔ _
    rw [point_preservation J hu ho]
    change (PreservesQuadratic J (DualNumber k) (infinitesimal D) ∧ _) ↔ _
    rw [infinitesimal_quadratic_iff]
    exact and_congr_right fun _ => forall_congr' (fun i => infinitesimal_fixes D (frameAxis i))
  -- Reduction to the identity determines the unique coefficient of ε.
  choose d hd using fun p : LinearAlgebraicGroups.Specs.Lie k G.group =>
    exists_infinitesimal (A p.toMul.val).val ((pointAction_reduces G _).mp p.toMul.property)
  have hm (p : LinearAlgebraicGroups.Specs.Lie k G.group) : d p ∈ frameDerivations J := by
    apply (hfix (d p)).mp
    have he : A p.toMul.val = infinitesimalUnit (d p) := Units.ext (hd p)
    exact (pointAction_range G _ _).mp ⟨p.toMul.val, he⟩
  let L : LinearAlgebraicGroups.Specs.Lie k G.group →ₗ[k] frameDerivations J :=
    { toFun := fun p => ⟨d p, hm p⟩
      map_add' := fun p q => by
        apply Subtype.ext
        apply infinitesimal_injective
        change infinitesimal (d (p + q)) = infinitesimal (d p + d q)
        calc
          _ = (A (p + q).toMul.val).val := (hd _).symm
          _ = (A p.toMul.val).val * (A q.toMul.val).val := congrArg Units.val (map_mul A _ _)
          _ = _ := by rw [hd, hd, infinitesimal_add]
      map_smul' := fun c p => by
        apply Subtype.ext
        apply infinitesimal_injective
        change infinitesimal (d (scalePointKernel G.group c p)) = infinitesimal (c • d p)
        rw [← hd]
        exact pointAction_scale G p c (d p) (hd p) }
  have hL : Function.Bijective L := by
    constructor
    · intro p q h
      apply Subtype.ext
      apply pointAction_injective G (dualAlgebra k)
      apply Units.ext
      exact (hd p).trans ((congrArg (fun a : frameDerivations J => infinitesimal a.val) h).trans
        (hd q).symm)
    · intro D
      obtain ⟨p, hp⟩ := (pointAction_range G (dualAlgebra k) (infinitesimalUnit D.val)).mpr
        ((hfix D.val).mpr D.property)
      have hr := (pointAction_reduces G p).mpr (by
        rw [hp]
        exact infinitesimal_reduction D.val)
      let q : LinearAlgebraicGroups.Specs.Lie k G.group := ⟨p, hr⟩
      refine ⟨q, Subtype.ext (infinitesimal_injective ?_)⟩
      exact (hd q).symm.trans (congrArg Units.val hp)
  let e : LinearAlgebraicGroups.Specs.Lie k G.group ≃ₗ[k] frameDerivations J :=
    LinearEquiv.ofBijective L hL
  refine ⟨e.symm, fun D x => ?_⟩
  have hcoeff : d (e.symm D) = D.val := congrArg Subtype.val (e.apply_symm_apply D)
  have hpoint : (A (e.symm D).toMul.val).val = infinitesimal D.val :=
    (hd (e.symm D)).trans (congrArg infinitesimal hcoeff)
  exact (pointAction_apply G (dualAlgebra k) (e.symm D).toMul.val x).symm.trans
    (congrArg (fun T : Module.End (DualNumber k) (DualNumber k ⊗[k] Model k) =>
      TrialitySpecification.modelBaseChange k (DualNumber k) (T x)) hpoint)

end Tangent

section Dimension

open TensorProduct Algebra.TensorProduct Bialgebra

attribute [local instance] coordinateGroup

open private switchOpen switchOpen_cover switchOpen_smooth
  from LinearAlgebraicGroups.Albert.SplitSpin

private theorem integralCoordinates_locallyStandardSmooth :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 28)
      (algebraMap ℤ integralCoordinates) := by
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 28)
    (φ := CommRingCat.ofHom (algebraMap ℤ integralCoordinates))).mp ?_
  change SmoothOfRelativeDimension (2 * 4 ^ 2 - 4) (SpinFunctor.spinScheme spinForm spinBasis).X.hom
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} (2 * 4 ^ 2 - 4)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (2 * 4 ^ 2 - 4)))
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (2 * 4 ^ 2 - 4))
    (switchOpen 4) (switchOpen_cover 4) (switchOpen_smooth 4 (by decide))

private theorem locallyStandardSmooth_intTensor {A : Type} [CommRing A]
    (k : Type u) [CommRing k] (n : ℕ)
    (hA : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap ℤ A)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap k (k ⊗[ℤ] A)) := by
  obtain ⟨s, hs, h⟩ := hA
  let j : A →ₐ[ℤ] k ⊗[ℤ] A := Algebra.TensorProduct.includeRight
  refine ⟨j '' s, ?_, ?_⟩
  · change Ideal.span (j.toRingHom '' s) = ⊤
    rw [← Ideal.map_span j.toRingHom s, hs, Ideal.map_top]
  · rintro _ ⟨a, ha, rfl⟩
    let B := Localization.Away a
    letI : Algebra ℤ B := Ring.toIntAlgebra B
    have hloc := h a ha
    rw [← IsScalarTower.algebraMap_eq ℤ A B,
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hloc
    letI : Algebra.IsStandardSmoothOfRelativeDimension n ℤ B := hloc
    letI : Algebra.IsStandardSmoothOfRelativeDimension n k (k ⊗[ℤ] B) :=
      Algebra.IsStandardSmoothOfRelativeDimension.baseChange n k
    rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv n
      (IsLocalization.Away.tensorProductEquivTMulRight ℤ k a B)

private theorem cotangent_finrank {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (x : A →ₐ[k] k) (n : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap k A)) :
    Module.finrank k (PointCotangent x) = n := by
  classical
  obtain ⟨s, hs, H⟩ := h
  have he : ∃ a ∈ s, x a ≠ 0 := by
    by_contra! hn
    have hle : Ideal.span s ≤ RingHom.ker x.toRingHom :=
      Ideal.span_le.mpr fun a ha => RingHom.mem_ker.mpr (hn a ha)
    have h1 : (1 : A) ∈ RingHom.ker x.toRingHom := hle (by simp [hs])
    exact one_ne_zero ((map_one x).symm.trans (RingHom.mem_ker.mp h1))
  obtain ⟨a, ha, hxa⟩ := he
  -- Localize at a standard smooth neighborhood containing the rational point.
  let B := Localization.Away a
  have hB := H a ha
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hB
  let y₀ : B →+* k := IsLocalization.Away.lift a (isUnit_iff_ne_zero.mpr hxa)
  have hy (b : A) : y₀ (algebraMap A B b) = x b := IsLocalization.Away.lift_eq a _ b
  letI : Algebra A k := x.toRingHom.toAlgebra
  letI : Algebra B k := y₀.toAlgebra
  letI : IsScalarTower A B k := IsScalarTower.of_algebraMap_eq fun b => (hy b).symm
  letI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq fun r => (x.commutes r).symm
  letI : IsScalarTower k B k := IsScalarTower.of_algebraMap_eq fun r => by
    change r = y₀ (algebraMap k B r)
    rw [IsScalarTower.algebraMap_apply k A B, hy, x.commutes]
    rfl
  haveI : Nontrivial B := y₀.domain_nontrivial
  haveI : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := B) (Submonoid.powers a)
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange A B k k (KaehlerDifferential k A)
  let e₂ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A B
  let e₃ := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl k k) e₂
  obtain ⟨e, -⟩ := AdvCommAlg.Differentials.point_cotangent k A x
  have hfin := (e.trans (e₁.symm.trans e₃)).finrank_eq
  rw [hfin]
  obtain ⟨iota, sigma, _, _, P, hp⟩ := hB.out
  letI : Fintype ((Set.range P.map)ᶜ : Set _) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (P.basisKaehler.baseChange k)]
  exact_mod_cast ((rank_eq_card_basis P.basisKaehler).symm.trans
    (P.rank_kaehlerDifferential.trans (congrArg (fun d : ℕ => (d : Cardinal)) hp)))

set_option maxHeartbeats 1000000 in
private theorem frameGroup_finrank (k : Type u) [Field k] :
    letI := frameGroup_affine k
    Module.finrank k (LinearAlgebraicGroups.Specs.Lie k (frameGroup k)) = 28 := by
  letI := frameGroup_affine k
  let C : Grp ((CommAlgCat k)ᵒᵖ) := Grp.mk (coordinateObject k)
  let E := commHopfAlgCatEquivCogrpCommAlgCat k
  let A := E.inverse.obj (op C)
  let i : hopfSpectrum A ≅ frameGroup k := ((algSpec (CommRingCat.of k)).mapGrp).mapIso
    (E.counitIso.app (op C)).unop.symm
  obtain ⟨e, _, he⟩ := liePresentation k A (frameGroup k) i
  let d : PointTangent (counitAlgHom k A) ≃ₗ[k] LinearAlgebraicGroups.Specs.Lie k (frameGroup k) :=
    { e with map_smul' := he }
  rw [← d.finrank_eq, Subspace.dual_finrank_eq]
  exact cotangent_finrank (counitAlgHom k A) 28 (locallyStandardSmooth_intTensor k 28 integralCoordinates_locallyStandardSmooth)

end Dimension

/-- The frame-fixing quadratic derivations identify with the represented tangent
kernel and have dimension 28 over every field. -/
theorem frameTangentRank : FrameTangentRank.{u} := by
  intro k _ J hu ho
  let G := frameRepresentation k
  letI := G.affine
  obtain ⟨e, he⟩ := frameTangentEquiv G J hu ho
  refine ⟨G, ⟨lieAddCommGroup G.group, rfl, lieModule G.group, rfl⟩, e, he, ?_⟩
  exact e.finrank_eq.trans (frameGroup_finrank k)

end
end LinearAlgebraicGroups.Albert.FrameTangent
