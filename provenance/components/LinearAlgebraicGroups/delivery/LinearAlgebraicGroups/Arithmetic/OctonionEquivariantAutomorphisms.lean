import Specs.LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms
import LinearAlgebraicGroups.Composition.OctonionAutomorphisms
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms

open LinearAlgebraicGroups.Specs (GroupScheme)
open LinearAlgebraicGroups.Specs.AutomorphismSequence (relativePoints restrictIso innerAut)
open LinearAlgebraicGroups.Specs.RelativeFormComparison (fieldTest fieldMap transportedAut)
open LinearAlgebraicGroups.Specs.OctonionEquivariantAutomorphisms
open LinearAlgebraicGroups.Composition
open PeirceSpecification (tensorMap)
open OctonionAutomorphismSpecification (AutomorphismGroup)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (bilinearStabilizer)
open LinearAlgebraicGroups.Descent (SemilinearAction)

open private conjugateUnits conjugateUnits_apply conjugateUnits_preserves_iff
  octonionAlgebra_preserves_iff from LinearAlgebraicGroups.Composition.OctonionAutomorphisms

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

section Tensors

variable {C : Type v} {D : Type w} [AddCommGroup C] [AddCommGroup D]
  [Module k C] [Module k D]
variable {R S T : TestAlgebra k}

private theorem tensorMap_smul (a : R ⟶ S) (r : R) (x : R ⊗[k] C) :
    tensorMap a.hom (r • x) = a.hom r • tensorMap a.hom x := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, Peirce.tensorMap_tmul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem tensorMap_comp (a : R ⟶ S) (b : S ⟶ T) (x : R ⊗[k] C) :
    tensorMap (a ≫ b).hom x = tensorMap b.hom (tensorMap a.hom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem extend_tmul (f : CommAlgCat.of k K ⟶ S)
    (e : (K ⊗[k] C) →ₗ[K] (K ⊗[k] D)) (s : S) (x : C) :
    extendComparison f e (s ⊗ₜ[k] x) = s • tensorMap f.hom (e (1 ⊗ₜ[k] x)) := rfl

private theorem eq_on_generators {M : Type*} [AddCommGroup M] [Module S M]
    (a b : (S ⊗[k] C) →ₗ[S] M)
    (h : ∀ x : C, a (1 ⊗ₜ[k] x) = b (1 ⊗ₜ[k] x)) (x : S ⊗[k] C) : a x = b x := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    rw [show s ⊗ₜ[k] x = s • ((1 : S) ⊗ₜ[k] x) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem extend_tensorMap (f : CommAlgCat.of k K ⟶ S)
    (e : (K ⊗[k] C) →ₗ[K] (K ⊗[k] D)) (x : K ⊗[k] C) :
    extendComparison f e (tensorMap f.hom x) = tensorMap f.hom (e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [Peirce.tensorMap_tmul, extend_tmul,
      show r ⊗ₜ[k] x = r • ((1 : K) ⊗ₜ[k] x) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, tensorMap_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private def extendEquiv (f : CommAlgCat.of k K ⟶ S)
    (e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] D)) : (S ⊗[k] C) ≃ₗ[S] (S ⊗[k] D) :=
  LinearEquiv.ofLinearMap (extendComparison f e.toLinearMap)
    (extendComparison f e.symm.toLinearMap)
    (LinearMap.ext fun x => eq_on_generators _ _ (fun y => by
      change extendComparison f e.toLinearMap (extendComparison f e.symm.toLinearMap _) = _
      rw [extend_tmul, one_smul, extend_tensorMap]
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Peirce.tensorMap_tmul, map_one, LinearMap.id_apply]) x)
    (LinearMap.ext fun x => eq_on_generators _ _ (fun y => by
      change extendComparison f e.symm.toLinearMap (extendComparison f e.toLinearMap _) = _
      rw [extend_tmul, one_smul, extend_tensorMap]
      simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Peirce.tensorMap_tmul, map_one, LinearMap.id_apply]) x)

private theorem extend_natural (f : CommAlgCat.of k K ⟶ S) (a : S ⟶ T)
    (e : (K ⊗[k] C) →ₗ[K] (K ⊗[k] D)) (x : S ⊗[k] C) :
    extendComparison (f ≫ a) e (tensorMap a.hom x) =
      tensorMap a.hom (extendComparison f e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    rw [Peirce.tensorMap_tmul, extend_tmul, extend_tmul, tensorMap_smul, tensorMap_comp]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tensors

section Products

variable {C : Type v} {D : Type w} [NonAssocRing C] [NonAssocRing D]
  [Module k C] [Module k D] [IsScalarTower k C C] [IsScalarTower k D D]
  [SMulCommClass k C C] [SMulCommClass k D D]
variable {R S : TestAlgebra k}

private theorem tensorMap_mul (a : R ⟶ S) (x y : R ⊗[k] C) :
    tensorMap a.hom (x * y) = tensorMap a.hom x * tensorMap a.hom y := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | tmul s y => simp only [Algebra.TensorProduct.tmul_mul_tmul, Peirce.tensorMap_tmul, map_mul]
    | add y z hy hz => simp only [mul_add, map_add, hy, hz]
  | add x z hx hz => simp only [add_mul, map_add, hx, hz]

omit [IsScalarTower k C C] [IsScalarTower k D D] [SMulCommClass k C C] [SMulCommClass k D D] in
private theorem extend_one (f : CommAlgCat.of k K ⟶ S)
    (e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] D)) (h : e 1 = 1) :
    extendEquiv f e 1 = 1 := by
  change extendComparison f e.toLinearMap ((1 : S) ⊗ₜ[k] (1 : C)) = (1 : S) ⊗ₜ[k] (1 : D)
  rw [extend_tmul, one_smul]
  change tensorMap f.hom (e 1) = (1 : S) ⊗ₜ[k] (1 : D)
  rw [h]
  change tensorMap f.hom ((1 : K) ⊗ₜ[k] (1 : D)) = _
  rw [Peirce.tensorMap_tmul, map_one]

private theorem extend_mul (f : CommAlgCat.of k K ⟶ S)
    (e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] D)) (h : ∀ x y, e (x * y) = e x * e y)
    (x y : S ⊗[k] C) : extendEquiv f e (x * y) = extendEquiv f e x * extendEquiv f e y := by
  change extendComparison f e.toLinearMap (x * y) =
    extendComparison f e.toLinearMap x * extendComparison f e.toLinearMap y
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    induction y using TensorProduct.inductionOn with
    | tmul t y =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, extend_tmul, LinearEquiv.coe_coe]
      rw [show (1 : K) ⊗ₜ[k] (x * y) = ((1 : K) ⊗ₜ[k] x) * ((1 : K) ⊗ₜ[k] y) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
        h, tensorMap_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    | add y z hy hz => simp only [mul_add, map_add, hy, hz]
  | add x z hx hz => simp only [add_mul, map_add, hx, hz]

end Products

section RelativePoints

local notation "V" => fieldTest k K

private theorem exists_affineTest_iso (U : Over V) (hU : IsAffine U.left.left) :
    ∃ (S : TestAlgebra k) (f : CommAlgCat.of k K ⟶ S), Nonempty (affineTest f ≅ U) := by
  obtain ⟨S, ⟨i⟩⟩ := essImage_algSpec.mpr hU
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f := ff.preimage (i.hom ≫ U.hom)
  exact ⟨S.unop, f.unop, ⟨Over.isoMk i (ff.map_preimage _).symm⟩⟩

private theorem affineTest_hom {S T : TestAlgebra k}
    {f : CommAlgCat.of k K ⟶ S} {g : CommAlgCat.of k K ⟶ T}
    (a : affineTest g ⟶ affineTest f) :
    ∃ b : S ⟶ T, a.left = (testSpec k).map b.op ∧ g = f ≫ b := by
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let b := ff.preimage a.left
  have hb : (testSpec k).map b = a.left := ff.map_preimage _
  refine ⟨b.unop, hb.symm, ?_⟩
  apply Quiver.Hom.op_inj
  apply ff.map_injective
  change (testSpec k).map g.op = (testSpec k).map (f ≫ b.unop).op
  rw [op_comp, Functor.map_comp]
  change (testSpec k).map g.op = (testSpec k).map b ≫ (testSpec k).map f.op
  rw [hb]
  exact (Over.w a).symm

private abbrev relativeProduct (X : SchemeOver k) : Over V :=
  Over.mk (snd X V)

private def relativeLift {X : SchemeOver k} {U : Over V} (x : U.left ⟶ X) :
    U ⟶ relativeProduct (K := K) X :=
  Over.homMk (lift x U.hom) (lift_snd _ _)

private theorem relativeLift_natural {X : SchemeOver k} {U W : Over V} (a : U ⟶ W)
    (x : W.left ⟶ X) : (relativeLift (a.left ≫ x)).left =
      a.left ≫ (relativeLift x).left := by
  change lift (a.left ≫ x) U.hom = a.left ≫ lift x W.hom
  rw [comp_lift, Over.w a]

private theorem relativeProduct_affine (X : SchemeOver k) (hX : IsAffine X.left) :
    IsAffine (relativeProduct (K := K) X).left.left := by
  let := hX
  change IsAffine (pullback X.hom (fieldSpecMap k K))
  infer_instance

/-- Every relative point of an affine scheme pulls back from an affine test. -/
private theorem relative_induction {X : SchemeOver k} (hX : IsAffine X.left)
    {P : ∀ U : Over V, (U.left ⟶ X) → Prop}
    (ha : ∀ (S : TestAlgebra k) (f : CommAlgCat.of k K ⟶ S) x, P (affineTest f) x)
    (hn : ∀ {U W : Over V} (a : U ⟶ W) (x : W.left ⟶ X),
      P W x → P U (a.left ≫ x)) (U : Over V) (x : U.left ⟶ X) : P U x := by
  obtain ⟨S, f, ⟨i⟩⟩ := exists_affineTest_iso (relativeProduct (K := K) X)
    (relativeProduct_affine X hX)
  let p : (affineTest f).left ⟶ X := i.hom.left ≫ fst X V
  have he : (relativeLift x ≫ i.inv).left ≫ p = x := by
    simp [p, Over.comp_left, relativeLift]
  exact he ▸ hn (relativeLift x ≫ i.inv) p (ha S f p)

/-- Extend a natural family on affine tests by evaluating it on the universal point. -/
private theorem exists_relativeHom {G H : GroupScheme k} (hG : IsAffine G.X.left)
    (E : ∀ (S : TestAlgebra k), (CommAlgCat.of k K ⟶ S) → (Points G.X S →* Points H.X S))
    (hE : ∀ {S T : TestAlgebra k} (f : CommAlgCat.of k K ⟶ S) (a : S ⟶ T)
      (x : Points G.X S), E T (f ≫ a) (mapPoints a x) = mapPoints a (E S f x)) :
    ∃ forward : relativePoints G V ⟶ relativePoints H V,
      ∀ (S : TestAlgebra k) (f : CommAlgCat.of k K ⟶ S) (x : Points G.X S),
        (forward.app (op (affineTest f))).hom x = E S f x := by
  obtain ⟨T, g, ⟨i⟩⟩ := exists_affineTest_iso (relativeProduct (K := K) G.X)
    (relativeProduct_affine G.X hG)
  let p : Points G.X T := i.hom.left ≫ fst G.X V
  let F (U : Over V) (x : U.left ⟶ G.X) : U.left ⟶ H.X :=
    (relativeLift x ≫ i.inv).left ≫ E T g p
  have nat {U W : Over V} (a : U ⟶ W) (x : W.left ⟶ G.X) :
      F U (a.left ≫ x) = a.left ≫ F W x := by
    simp only [F, Over.comp_left, relativeLift_natural, Category.assoc]
  have affine (S : TestAlgebra k) (f : CommAlgCat.of k K ⟶ S) (x : Points G.X S) :
      F (affineTest f) x = E S f x := by
    let a := relativeLift (U := affineTest f) x ≫ i.inv
    obtain ⟨b, hb, hf⟩ := affineTest_hom a
    have hx : mapPoints b p = x := by
      rw [mapPoints, ← hb]
      simp [a, p, Over.comp_left, relativeLift]
    change a.left ≫ E T g p = _
    rw [hb, ← mapPoints, ← hE, hx, ← hf]
  have mul (U : Over V) (x y : U.left ⟶ G.X) : F U (x * y) = F U x * F U y := by
    have hp : IsAffine (G.X ⊗ G.X).left := by
      let := hG
      change IsAffine (pullback G.X.hom G.X.hom)
      infer_instance
    have h := relative_induction (K := K) hp
      (P := fun W z =>
        F W ((z ≫ fst G.X G.X) * (z ≫ snd G.X G.X)) =
          F W (z ≫ fst G.X G.X) * F W (z ≫ snd G.X G.X))
      (fun S f z => by rw [affine, affine, affine, map_mul])
      (by
        intro U' W a z hz
        have hh := congrArg (fun t : W.left ⟶ H.X => a.left ≫ t) hz
        simpa only [MonObj.comp_mul, ← nat, Category.assoc] using hh)
      U (lift x y)
    simpa only [lift_fst, lift_snd] using h
  let app (U : (Over V)ᵒᵖ) : (relativePoints G V).obj U ⟶ (relativePoints H V).obj U := by
    refine GrpCat.ofHom { toFun := F U.unop, map_one' := ?_, map_mul' := mul U.unop }
    have h := mul U.unop 1 1
    rw [mul_one] at h
    have he := congrArg ((F U.unop 1)⁻¹ * ·) h
    simpa [mul_assoc] using he.symm
  refine ⟨{ app := app, naturality := ?_ }, affine⟩
  intro U W a
  apply GrpCat.ext
  intro x
  exact nat a.unop x

private theorem relativeHom_ext {G H : GroupScheme k} (hG : IsAffine G.X.left)
    {forward backward : relativePoints G V ⟶ relativePoints H V}
    (h : ∀ (S : TestAlgebra k) (f : CommAlgCat.of k K ⟶ S) (x : Points G.X S),
      (forward.app (op (affineTest f))).hom x = (backward.app (op (affineTest f))).hom x) : forward = backward := by
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  apply relative_induction (K := K) hG (P := fun W p =>
    (forward.app (op W)).hom p = (backward.app (op W)).hom p) h _ U.unop x
  intro W T a p hp
  have eforward := ConcreteCategory.congr_hom (forward.naturality a.op) p
  have ebackward := ConcreteCategory.congr_hom (backward.naturality a.op) p
  change (forward.app (op W)).hom (a.left ≫ p) = a.left ≫ (forward.app (op T)).hom p at eforward
  change (backward.app (op W)).hom (a.left ≫ p) = a.left ≫ (backward.app (op T)).hom p at ebackward
  rw [eforward, ebackward, hp]

private theorem exists_relativeIso {G H : GroupScheme k} (hG : IsAffine G.X.left)
    (hH : IsAffine H.X.left)
    (E : ∀ (S : TestAlgebra k), (CommAlgCat.of k K ⟶ S) → (Points G.X S ≃* Points H.X S))
    (hE : ∀ {S T : TestAlgebra k} (f : CommAlgCat.of k K ⟶ S) (a : S ⟶ T)
      (x : Points G.X S), E T (f ≫ a) (mapPoints a x) = mapPoints a (E S f x)) :
    ∃ j : relativePoints G V ≅ relativePoints H V,
      ∀ (S : TestAlgebra k) (f : CommAlgCat.of k K ⟶ S) (x : Points G.X S),
        (j.hom.app (op (affineTest f))).hom x = E S f x := by
  obtain ⟨forward, hforward⟩ := exists_relativeHom hG (fun S f => (E S f).toMonoidHom) hE
  obtain ⟨backward, hbackward⟩ := exists_relativeHom hH (fun S f => (E S f).symm.toMonoidHom) (by
    intro S T f a x
    change (E T (f ≫ a)).symm (mapPoints a x) = mapPoints a ((E S f).symm x)
    apply (E T (f ≫ a)).injective
    rw [MulEquiv.apply_symm_apply, hE, MulEquiv.apply_symm_apply])
  refine ⟨⟨forward, backward, ?_, ?_⟩, hforward⟩
  · apply relativeHom_ext hG
    intro S f x
    change (backward.app (op (affineTest f))).hom ((forward.app (op (affineTest f))).hom x) = x
    rw [hforward, hbackward]
    exact (E S f).symm_apply_apply x
  · apply relativeHom_ext hH
    intro S f x
    change (forward.app (op (affineTest f))).hom ((backward.app (op (affineTest f))).hom x) = x
    rw [hbackward, hforward]
    exact (E S f).apply_symm_apply x

end RelativePoints

section Conjugation

variable {C : Type v} {D : Type w} [NonAssocRing C] [NonAssocRing D] [Module k C] [Module k D]
  [IsScalarTower k C C] [IsScalarTower k D D] [SMulCommClass k C C] [SMulCommClass k D D]
variable (A : AutomorphismGroup k C) (B : AutomorphismGroup k D)
variable {S T : TestAlgebra k}

private abbrev pointAction (A : AutomorphismGroup k C) {S : TestAlgebra k}
    (p : Points A.group.X S) : Module.End S (S ⊗[k] C) := (A.subgroupPoints S p).val.val

private theorem pointAction_natural (A : AutomorphismGroup k C) (a : S ⟶ T)
    (p : Points A.group.X S) (x : S ⊗[k] C) :
    pointAction A (mapPoints a p) (tensorMap a.hom x) = tensorMap a.hom (pointAction A p x) := by
  have h := A.scalarChange a (p ≫ A.inclusion.hom.hom) x
  change (A.linearPoints T (mapPoints a (p ≫ A.inclusion.hom.hom))).val
      (tensorMap a.hom x) =
    tensorMap a.hom ((A.linearPoints S (p ≫ A.inclusion.hom.hom)).val x) at h
  rw [show mapPoints a (p ≫ A.inclusion.hom.hom) =
    mapPoints a p ≫ A.inclusion.hom.hom from (Category.assoc ..).symm] at h
  have hEval (U : TestAlgebra k) (q : Points A.group.X U) :
      A.linearPoints U (q ≫ A.inclusion.hom.hom) = (A.subgroupPoints U q).val :=
    A.evaluatesInclusion U q
  rwa [hEval, hEval] at h

private theorem pointAction_injective (A : AutomorphismGroup k C) :
    Function.Injective (pointAction A (S := S)) := by
  intro p q h
  apply (A.subgroupPoints S).injective
  exact Subtype.ext (Units.ext h)

private theorem pointAction_mul (A : AutomorphismGroup k C) (p q : Points A.group.X S)
    (x : S ⊗[k] C) :
    pointAction A (p * q) x = pointAction A p (pointAction A q x) := by
  change (A.subgroupPoints S (p * q)).val.val x = _
  rw [map_mul]
  rfl

private def restrictMulEquiv {M N : Type*} [Group M] [Group N]
    {P : Subgroup M} {Q : Subgroup N} (e : M ≃* N)
    (h : ∀ g, e g ∈ Q ↔ g ∈ P) : P ≃* Q where
  toFun g := ⟨e g.val, (h g.val).mpr g.property⟩
  invFun g := ⟨e.symm g.val, (h (e.symm g.val)).mp (by
    rw [e.apply_symm_apply]
    exact g.property)⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv g := Subtype.ext (e.apply_symm_apply g.val)
  map_mul' g h := Subtype.ext (e.map_mul g.val h.val)

private abbrev octonionStabilizer (C : Type v) [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] (S : TestAlgebra k) :=
  bilinearStabilizer (OctonionAutomorphismSpecification.octonionAlgebra (R := k) (C := C)) S

private def comparisonStabilizers (f : CommAlgCat.of k K ⟶ S)
    (e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] D)) (h₁ : e 1 = 1) (hm : ∀ x y, e (x * y) = e x * e y) :
    octonionStabilizer D S ≃* octonionStabilizer C S := by
  let E := extendEquiv f e
  have hE₁ : E.symm 1 = 1 := E.symm_apply_eq.mpr (extend_one f e h₁).symm
  have hEm (x y : S ⊗[k] D) : E.symm (x * y) = E.symm x * E.symm y := by
    apply E.injective
    rw [E.apply_symm_apply, extend_mul f e hm, E.apply_symm_apply, E.apply_symm_apply]
  refine restrictMulEquiv (conjugateUnits E.symm) fun g => ?_
  exact (octonionAlgebra_preserves_iff (R := k) (C := C) S (conjugateUnits E.symm g)).trans
    ((conjugateUnits_preserves_iff E.symm hE₁ hEm g).trans
      (octonionAlgebra_preserves_iff (R := k) (C := D) S g).symm)

private def pointComparison (f : CommAlgCat.of k K ⟶ S)
    (e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] D)) (h₁ : e 1 = 1) (hm : ∀ x y, e (x * y) = e x * e y) :
    Points B.group.X S ≃* Points A.group.X S :=
  (B.subgroupPoints S).trans <| (comparisonStabilizers f e h₁ hm).trans (A.subgroupPoints S).symm

private theorem pointComparison_apply (f : CommAlgCat.of k K ⟶ S)
    (e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] D)) (h₁ : e 1 = 1) (hm : ∀ x y, e (x * y) = e x * e y)
    (p : Points B.group.X S) (x : S ⊗[k] C) :
    extendComparison f e.toLinearMap (pointAction A (pointComparison A B f e h₁ hm p) x) =
      pointAction B p (extendComparison f e.toLinearMap x) := by
  let E := extendEquiv f e
  change extendComparison f e.toLinearMap
    ((A.subgroupPoints S ((A.subgroupPoints S).symm
      (comparisonStabilizers f e h₁ hm (B.subgroupPoints S p)))).val.val x) = _
  rw [(A.subgroupPoints S).apply_symm_apply]
  change E ((conjugateUnits E.symm (B.subgroupPoints S p).val).val x) = pointAction B p (E x)
  have he := conjugateUnits_apply E.symm (B.subgroupPoints S p).val (E x)
  rw [E.symm_apply_apply] at he
  rw [he, E.apply_symm_apply]

private theorem pointComparison_natural (f : CommAlgCat.of k K ⟶ S) (a : S ⟶ T)
    (e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] D)) (h₁ : e 1 = 1) (hm : ∀ x y, e (x * y) = e x * e y)
    (p : Points B.group.X S) :
    pointComparison A B (f ≫ a) e h₁ hm (mapPoints a p) =
      mapPoints a (pointComparison A B f e h₁ hm p) := by
  apply pointAction_injective A
  apply LinearMap.ext
  apply eq_on_generators
  intro y
  let z := (1 : S) ⊗ₜ[k] y
  let q := pointComparison A B f e h₁ hm p
  let eS := extendComparison f e.toLinearMap
  let eT := extendComparison (f ≫ a) e.toLinearMap
  have hz : tensorMap a.hom z = (1 : T) ⊗ₜ[k] y := by
    rw [Peirce.tensorMap_tmul, map_one]
  rw [← hz]
  apply (extendEquiv (f ≫ a) e).injective
  change eT (pointAction A (pointComparison A B (f ≫ a) e h₁ hm (mapPoints a p))
      (tensorMap a.hom z)) = eT (pointAction A (mapPoints a q) (tensorMap a.hom z))
  calc
    _ = pointAction B (mapPoints a p) (eT (tensorMap a.hom z)) :=
      pointComparison_apply A B (f ≫ a) e h₁ hm (mapPoints a p) (tensorMap a.hom z)
    _ = pointAction B (mapPoints a p) (tensorMap a.hom (eS z)) :=
      congrArg (pointAction B (mapPoints a p)) (extend_natural f a e.toLinearMap z)
    _ = tensorMap a.hom (pointAction B p (eS z)) := pointAction_natural B a p (eS z)
    _ = tensorMap a.hom (eS (pointAction A q z)) :=
      congrArg (tensorMap a.hom) (pointComparison_apply A B f e h₁ hm p z).symm
    _ = eT (tensorMap a.hom (pointAction A q z)) :=
      (extend_natural f a e.toLinearMap (pointAction A q z)).symm
    _ = _ := congrArg eT (pointAction_natural A a q z).symm

end Conjugation

section Displacement

variable {C : Type v} {D : Type w} [NonAssocRing C] [NonAssocRing D] [Module k C] [Module k D]
  [IsScalarTower k C C] [IsScalarTower k D D] [SMulCommClass k C C] [SMulCommClass k D D]
variable (A : AutomorphismGroup k C) (B : AutomorphismGroup k D)

private abbrev galoisHom (σ : Gal(K/k)) : CommAlgCat.of k K ⟶ CommAlgCat.of k K :=
  CommAlgCat.ofHom σ.toAlgHom

private theorem coefficient_action {M : Type*} [AddCommGroup M] [Module k M]
    (σ : Gal(K/k)) (x : K ⊗[k] M) :
    (SemilinearAction.scalarExtension (k := k) (K := K) M).act σ x =
      tensorMap (galoisHom σ).hom x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [IsScalarTower k C C] [SMulCommClass k C C] in
/-- Pulling the intertwining formula along the specified scalar map compares the two extensions. -/
private theorem extendComparison_twist {S : TestAlgebra k} (f : CommAlgCat.of k K ⟶ S)
    (σ : Gal(K/k)) (c : fieldTest k K ⟶ B.group.X)
    (e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] D))
    (h : ∀ x, pointAction B c
      ((SemilinearAction.scalarExtension (k := k) (K := K) D).act σ (e x)) =
        e ((SemilinearAction.scalarExtension (k := k) (K := K) C).act σ x))
    (x : S ⊗[k] C) :
    pointAction B (mapPoints f c) (extendComparison (galoisHom σ ≫ f) e.toLinearMap x) =
      extendComparison f e.toLinearMap x := by
  apply eq_on_generators ((pointAction B (mapPoints f c)).comp
    (extendComparison (galoisHom σ ≫ f) e.toLinearMap)) _ _ x
  intro y
  simp only [LinearMap.comp_apply, extend_tmul, one_smul, LinearEquiv.coe_coe]
  let z := e ((1 : K) ⊗ₜ[k] y)
  have hfix : (SemilinearAction.scalarExtension (k := k) (K := K) C).act σ
      ((1 : K) ⊗ₜ[k] y) = (1 : K) ⊗ₜ[k] y := by
    change σ 1 ⊗ₜ[k] y = 1 ⊗ₜ[k] y
    rw [map_one]
  have he := h ((1 : K) ⊗ₜ[k] y)
  rw [hfix, coefficient_action σ z] at he
  rw [tensorMap_comp (galoisHom σ) f z,
    pointAction_natural B f c (tensorMap (galoisHom σ).hom z), he]

private theorem pointComparison_twist {S : TestAlgebra k} (f : CommAlgCat.of k K ⟶ S)
    (σ : Gal(K/k)) (c : fieldTest k K ⟶ B.group.X)
    (e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] D))
    (h₁ : e 1 = 1) (hm : ∀ x y, e (x * y) = e x * e y)
    (h : ∀ x, pointAction B c
      ((SemilinearAction.scalarExtension (k := k) (K := K) D).act σ (e x)) =
        e ((SemilinearAction.scalarExtension (k := k) (K := K) C).act σ x))
    (p : Points B.group.X S) :
    pointComparison A B (galoisHom σ ≫ f) e h₁ hm p =
      pointComparison A B f e h₁ hm (mapPoints f c * p * (mapPoints f c)⁻¹) := by
  let t := mapPoints f c
  let g := galoisHom σ ≫ f
  have ht := extendComparison_twist B f σ c e h
  apply pointAction_injective A
  apply LinearMap.ext
  intro x
  apply (extendEquiv f e).injective
  change extendComparison f e.toLinearMap
      (pointAction A (pointComparison A B g e h₁ hm p) x) =
    extendComparison f e.toLinearMap
      (pointAction A (pointComparison A B f e h₁ hm (t * p * t⁻¹)) x)
  let z := extendComparison g e.toLinearMap x
  have hc :
      pointAction B t (pointAction B p z) = pointAction B (t * p * t⁻¹) (pointAction B t z) := by
    rw [← pointAction_mul B t p z, ← pointAction_mul B (t * p * t⁻¹) t z,
      mul_assoc (t * p), inv_mul_cancel, mul_one]
  calc
    _ = pointAction B t (extendComparison g e.toLinearMap
        (pointAction A (pointComparison A B g e h₁ hm p) x)) := (ht _).symm
    _ = pointAction B t (pointAction B p z) :=
      congrArg (pointAction B t) (pointComparison_apply A B g e h₁ hm p x)
    _ = pointAction B (t * p * t⁻¹) (pointAction B t z) := hc
    _ = pointAction B (t * p * t⁻¹) (extendComparison f e.toLinearMap x) :=
      congrArg (pointAction B (t * p * t⁻¹)) (ht x)
    _ = _ := (pointComparison_apply A B f e h₁ hm (t * p * t⁻¹) x).symm

private theorem relativeHom_mk_congr {G H : GroupScheme k} {V X : SchemeOver k}
    (a : relativePoints G V ⟶ relativePoints H V) {f g : X ⟶ V} (h : f = g)
    (p : X ⟶ G.X) :
    (a.app (op (Over.mk f))).hom p = (a.app (op (Over.mk g))).hom p := by
  subst g
  rfl

private theorem restrictIso_affine_apply {G H : GroupScheme k}
    (j : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    (σ : Gal(K/k)) {S : TestAlgebra k} (f : CommAlgCat.of k K ⟶ S) (p : Points G.X S) :
    ((restrictIso (fieldMap k K σ) j).hom.app (op (affineTest f))).hom p =
      (j.hom.app (op (affineTest (galoisHom σ ≫ f)))).hom p := by
  have h : (testSpec k).map f.op ≫ fieldMap k K σ =
      (testSpec k).map (galoisHom σ ≫ f).op := by
    rw [op_comp, Functor.map_comp]
  exact relativeHom_mk_congr j.hom h p

end Displacement

/-- The conjugation comparison for a finite Galois twist of the split octonions. -/
theorem equivariantAutomorphisms : EquivariantAutomorphisms.{u,v} := by
  intro k K _ _ _ _ _ C _ _ _ _ n hn B A c e h₁ hm hnrm h
  obtain ⟨j, hj⟩ := exists_relativeIso (K := K) B.groupAffine A.groupAffine
    (fun _ f => pointComparison A B f e h₁ hm)
    (fun f a p => pointComparison_natural A B f a e h₁ hm p)
  refine ⟨j, ?_, ?_⟩
  · intro S f p x
    change extendComparison f e.toLinearMap (pointAction A ((j.hom.app (op (affineTest f))).hom p) x) =
      pointAction B p (extendComparison f e.toLinearMap x)
    rw [hj]
    exact pointComparison_apply A B f e h₁ hm p x
  · intro σ
    have he : restrictIso (fieldMap k K σ) j = (innerAut (c σ)).asIso ≪≫ j := by
      apply Iso.ext
      apply relativeHom_ext B.groupAffine
      intro S f p
      rw [restrictIso_affine_apply]
      change (j.hom.app (op (affineTest (galoisHom σ ≫ f)))).hom p =
        (j.hom.app (op (affineTest f))).hom (mapPoints f (c σ) * p * (mapPoints f (c σ))⁻¹)
      rw [hj, hj]
      exact pointComparison_twist A B f σ (c σ) e h₁ hm (h σ) p
    apply Aut.ext
    change restrictIso (fieldMap k K σ) j ≪≫ j.symm = (innerAut (c σ)).asIso
    rw [he, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

end
end LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms
